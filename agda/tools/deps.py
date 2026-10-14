#!/usr/bin/env python3
"""Read-only Agda import-closure audit; never invokes Agda or writes files.

Run: python3 tools/deps.py [--json] [--external] [--root MODULE_OR_PATH]
Roots come from roots.txt (paths relative to --project, the agda directory),
normally Assembly/Complete and HPInf/Complete. A missing manifest is an error;
repeated --root options independently replace it. Only src supplies local modules;
archive is searched for diagnostic hints, never for dependency resolution.

--external follows Cubical imports using deps.lock.json's cubical.path, relative
to --project. CUBICAL_DIR overrides that path (also relative to --project).
No user/global Agda library registry is consulted. Agda.* are compiler builtins,
not source dependencies. This is a lexical source audit, not a type check, lock
integrity check, or proof-completeness/semantic-obsolescence test.
"""
from __future__ import annotations

import argparse
from collections import Counter
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re

ROOT_PATHS = ("Assembly/Complete.agda", "HPInf/Complete.agda")
IMPORT = re.compile(r"(?:^|[;{}])\s*(?:open\s+)?import\s+([^\s;(){}]+)", re.MULTILINE)
MODULE = re.compile(r"^\s*module\s+([^\s;(){}]+)", re.MULTILINE)


def strip_comments_strings(text: str) -> str:
    """Mask nested {- -}, -- comments and strings; preserve line boundaries.

    Pragmas, including OPTIONS, are masked as block comments as well.
    """
    out = []
    i, depth = 0, 0
    in_string = False
    while i < len(text):
        c = text[i]
        if depth:
            if text.startswith("{-", i):
                depth += 1
                out.append("  ")
                i += 2
            elif text.startswith("-}", i):
                depth -= 1
                out.append("  ")
                i += 2
            else:
                out.append("\n" if c == "\n" else " ")
                i += 1
        elif in_string:
            if c == "\\" and i + 1 < len(text):
                out.append(" \n" if text[i + 1] == "\n" else "  ")
                i += 2
            else:
                out.append("\n" if c == "\n" else " ")
                in_string = c != '"'
                i += 1
        elif text.startswith("{-", i):
            depth = 1
            out.append("  ")
            i += 2
        elif text.startswith("--", i):
            end = text.find("\n", i)
            end = len(text) if end == -1 else end
            out.append(" " * (end - i))
            i = end
        elif c == '"':
            in_string = True
            out.append(" ")
            i += 1
        else:
            out.append(c)
            i += 1
    return "".join(out)


def closure(graph: dict[str, set[str]], roots) -> set[str]:
    """Return reachability in a resolved graph (including its root vertices)."""
    seen = set()
    todo = list(roots)
    while todo:
        node = todo.pop()
        if node not in seen:
            seen.add(node)
            todo.extend(graph[node] - seen)
    return seen


def _namespace(name: str, namespace: str) -> bool:
    return name == namespace or name.startswith(namespace + ".")


def _root_name(value: str, project: Path) -> str:
    """Accept a dotted DeloopS3 name or a project-relative src/...agda path."""
    value = value.strip()
    if value.endswith(".agda"):
        path = Path(value)
        if path.is_absolute():
            path = path.relative_to(project)
        if not path.parts or path.parts[0] != "src" or ".." in path.parts:
            raise ValueError(f"root must be under src/: {value}")
        value = ".".join(path.with_suffix("").parts[1:])
    if not value.startswith("DeloopS3.") or any(
        not part or any(c.isspace() or c in "/\\;(){}" for c in part)
        for part in value.split(".")
    ):
        raise ValueError(f"invalid root module or source path: {value}")
    return value


def audit(project: Path, roots=None, external: bool = False) -> dict:
    """Audit all active local sources and the selected roots' import closure.

    The one-argument API remains a local-only audit. External modules are read
    lazily, only when reachable from the selected roots. Errors are returned in
    the report; the CLI exits nonzero when ok is false.
    """
    project = project.resolve()
    src, archive = project / "src", project / "archive"
    started = datetime.now(timezone.utc).isoformat()
    config_errors, path_violations, mismatches = [], [], []
    manifest = project / "roots.txt"
    if roots is not None:
        root_source, selected = "explicit", list(roots)
    elif manifest.exists():
        root_source = str(manifest)
        selected = [line.split("#", 1)[0].strip() for line in manifest.read_text().splitlines()]
        selected = [line for line in selected if line]
    else:
        root_source, selected = str(manifest), []
        config_errors.append("missing roots.txt; expected final roots: " + ", ".join(ROOT_PATHS)
                             + "; alternatively provide explicit --root options")
    requested = set()
    for value in selected:
        try:
            requested.add(_root_name(value, project))
        except ValueError as exc:
            config_errors.append(str(exc))
    if not selected and not config_errors:
        config_errors.append("no roots selected (empty roots manifest or override)")

    # Index archive paths only. Archived imports/declarations are not obligations.
    archive_index = {}
    for path in sorted(archive.rglob("*.agda")):
        parts = path.relative_to(archive).with_suffix("").parts
        if "DeloopS3" in parts:
            name = ".".join(parts[parts.index("DeloopS3"):])
            archive_index.setdefault(name, []).append(str(path.relative_to(project)))

    paths = sorted(src.rglob("*.agda"))
    files, fingerprints, imports, modules = {}, {}, {}, {}

    def read_module(name: str, path: Path, base: Path) -> bool:
        actual = path.resolve()
        if actual.is_relative_to(archive.resolve()) or not actual.is_relative_to(base.resolve()):
            path_violations.append({"module": name, "file": str(path), "resolved": str(actual),
                                    "reason": "source escapes its allowed tree or resolves into archive"})
            return False
        raw = path.read_bytes()
        text = raw.decode("utf-8")
        masked = strip_comments_strings(text)
        declaration = MODULE.search(masked)
        if not declaration or declaration.group(1) != name:
            mismatches.append({"file": str(path), "expected": name,
                               "declared": declaration.group(1) if declaration else None})
        files[name] = path
        fingerprints[name] = hashlib.sha256(raw).hexdigest()
        imports[name] = set(IMPORT.findall(masked))
        modules[name] = {
            "path": os.path.relpath(path, project), "lines": len(text.splitlines()),
            "sha256": fingerprints[name], "declared_module": declaration.group(1) if declaration else None,
            "header_comments": [line.strip().removeprefix("--").strip()
                                for line in text.splitlines()[:75]
                                if line.lstrip().startswith("--")][:12],
        }
        return True

    for path in paths:
        name = ".".join(path.relative_to(src).with_suffix("").parts)
        if not _namespace(name, "DeloopS3"):
            path_violations.append({"module": name, "file": str(path),
                                    "reason": "active src must contain only DeloopS3 modules"})
            continue
        read_module(name, path, src)
    names = set(files)
    graph = {name: deps & names for name, deps in imports.items()}
    valid_roots = requested & names
    reachable = closure(graph, valid_roots)

    def missing_detail(importer: str, target: str) -> dict:
        return {"importer": importer, "module": target,
                "archive_candidates": archive_index.get(target, [])}

    missing_local = [missing_detail(name, dep) for name in sorted(names)
                     for dep in sorted(imports[name] - names) if _namespace(dep, "DeloopS3")]
    vendor, vendor_source = None, None
    if external:
        override = os.environ.get("CUBICAL_DIR")
        if override:
            vendor, vendor_source = (project / override).resolve(), "CUBICAL_DIR"
        else:
            try:
                lock = json.loads((project / "deps.lock.json").read_text())
                value = lock["cubical"]["path"]
                if not isinstance(value, str) or not value.strip():
                    raise ValueError("cubical.path must be a nonempty string")
                vendor, vendor_source = (project / value).resolve(), "deps.lock.json:cubical.path"
            except (OSError, ValueError, KeyError, TypeError) as exc:
                config_errors.append(f"cannot resolve locked Cubical directory: {exc}")
        if vendor is not None and (vendor.is_relative_to(archive.resolve())
                                   or not (vendor / "Cubical").is_dir()):
            config_errors.append(f"Cubical directory is absent or inside archive: {vendor}")
            vendor = None
    external_names, attempted = set(), set()
    todo = list(reachable) if external and vendor is not None else []
    while todo:
        name = todo.pop()
        if name in attempted:
            continue
        attempted.add(name)
        if name not in names:
            parts = name.split(".")
            if any(not part or "/" in part or "\\" in part for part in parts):
                continue
            path = vendor.joinpath(*parts).with_suffix(".agda")
            if not path.is_file() or not read_module(name, path, vendor):
                continue
            external_names.add(name)
        todo.extend(dep for dep in imports[name] if dep in names or _namespace(dep, "Cubical"))

    all_names = names | external_names
    for name in sorted(external_names):
        missing_local.extend(missing_detail(name, dep) for dep in sorted(imports[name] - names)
                             if _namespace(dep, "DeloopS3"))
    full_graph = {name: deps & all_names for name, deps in imports.items()}
    transitive = closure(full_graph, valid_roots)
    reachable = transitive & names
    candidates = names - reachable
    external_seeds = {dep for name in reachable for dep in imports[name] if _namespace(dep, "Cubical")}
    missing_external = [missing_detail(name, dep) for name in sorted(reachable | external_names)
                        for dep in sorted(imports[name] - external_names)
                        if external and _namespace(dep, "Cubical")]
    unknown = [missing_detail(name, dep) for name in sorted(all_names)
               for dep in sorted(imports[name] - all_names)
               if not dep.startswith("Agda.") and not any(_namespace(dep, ns) for ns in ("DeloopS3", "Cubical"))]
    builtins = sorted({dep for name in transitive for dep in imports[name] if dep.startswith("Agda.")})
    archive_leaks = [item for item in missing_local
                     if item["importer"] in transitive and item["archive_candidates"]]
    reverse = {name: set() for name in all_names}
    for name, deps in full_graph.items():
        for dep in deps:
            reverse[dep].add(name)
    for name in all_names:
        modules[name].update({"imports": sorted(full_graph[name]), "imported_by": sorted(reverse[name]),
                              "external_imports": sorted(imports[name] - names),
                              "all_imports": sorted(imports[name])})
    changed = [name for name, path in sorted(files.items())
               if not path.exists() or hashlib.sha256(path.read_bytes()).hexdigest() != fingerprints[name]]
    new_or_removed = sorted(str(p) for p in set(src.rglob("*.agda")) ^ set(paths))
    root_closures = {}
    for root in sorted(valid_roots):
        nodes = closure(full_graph, [root])
        root_closures[root] = {"local_count": len(nodes & names), "external_count": len(nodes & external_names),
                               "local": sorted(nodes & names), "external": sorted(nodes & external_names)}
    ok = not (config_errors or requested - names or missing_local or missing_external or unknown
              or mismatches or path_violations or changed or new_or_removed)
    return {
        "ok": ok, "project": str(project), "snapshot_started_utc": started,
        "scope": "local-and-cubical" if external else "local-only",
        "snapshot_finished_utc": datetime.now(timezone.utc).isoformat(),
        "root_source": root_source, "requested_roots": sorted(requested), "roots": sorted(valid_roots),
        "missing_roots": sorted(requested - names),
        "missing_root_details": [{"module": name, "archive_candidates": archive_index.get(name, [])}
                                 for name in sorted(requested - names)],
        "counts": {"total": len(names), "roots": len(valid_roots), "reachable": len(reachable),
                   "archive_candidates": len(candidates), "external_reachable": len(external_names),
                   "transitive_source_modules": len(transitive), "compiler_builtins": len(builtins),
                   "reachable_lines": sum(modules[n]["lines"] for n in reachable),
                   "archive_lines": sum(modules[n]["lines"] for n in candidates)},
        "reachable": sorted(reachable), "archive_candidates": sorted(candidates),
        "archive_candidates_note": "Active src modules outside the selected closure; not a deletion recommendation.",
        "root_closures": root_closures, "transitive_modules": sorted(transitive),
        "external": {"enabled": external, "directory": str(vendor) if vendor else None,
                     "source": vendor_source, "lock_integrity_verified": False,
                     "integrity_note": "Source graph only; vendor hashes/commit are not checked by this tool.",
                     "direct_imports": sorted(external_seeds),
                     "reachable": sorted(external_names), "unresolved_imports": missing_external,
                     "modules": {n: modules[n] for n in sorted(external_names)}},
        "compiler_builtins": builtins,
        "compiler_builtins_note": "Agda.* are supplied by the compiler and excluded from source counts.",
        "unresolved_local_imports": sorted({item["module"] for item in missing_local}),
        "unresolved_local_import_details": missing_local,
        "unknown_nonbuiltin_imports": unknown, "module_path_mismatches": mismatches,
        "source_path_violations": path_violations, "reachable_imports_archive": archive_leaks,
        "configuration_errors": config_errors, "changed_during_audit": changed,
        "new_or_removed_during_audit": new_or_removed,
        "directory_counts": dict(sorted(Counter(str(files[n].relative_to(src).parent)
                                                  for n in reachable).items())),
        "modules": {n: modules[n] for n in sorted(names)},
    }


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--project", type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument("--json", action="store_true", help="Print full module lists and metadata")
    parser.add_argument("--root", action="append", help="Root module or src/...agda path; repeat to override roots.txt")
    parser.add_argument("--external", action="store_true", help="Traverse reachable Cubical sources using lock/CUBICAL_DIR")
    args = parser.parse_args(argv)
    try:
        result = audit(args.project, roots=args.root, external=args.external)
    except (OSError, UnicodeError, ValueError) as exc:
        print(json.dumps({"ok": False, "configuration_errors": [str(exc)]}, ensure_ascii=False, indent=2))
        return 1
    if args.json:
        print(json.dumps(result, ensure_ascii=False, indent=2))
    else:
        summary = {k: result[k] for k in (
            "ok", "scope", "root_source", "roots", "counts", "missing_roots", "missing_root_details",
            "configuration_errors", "unresolved_local_imports", "unresolved_local_import_details",
            "unknown_nonbuiltin_imports", "module_path_mismatches", "source_path_violations",
            "reachable_imports_archive", "changed_during_audit", "new_or_removed_during_audit")}
        summary["external"] = {k: v for k, v in result["external"].items()
                               if k not in ("modules", "reachable", "direct_imports")}
        summary["external"]["direct_import_count"] = len(result["external"]["direct_imports"])
        summary["compiler_builtins"] = result["compiler_builtins"]
        summary["archive_candidates"] = result["archive_candidates"]
        summary["archive_candidates_note"] = result["archive_candidates_note"]
        print(json.dumps(summary, ensure_ascii=False, indent=2))
    return 0 if result["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
