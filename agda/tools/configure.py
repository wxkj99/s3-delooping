#!/usr/bin/env python3
"""Offline, lock-checked Agda configuration and bounded project checks (stdlib only)."""
import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import shlex
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parent.parent


def require(condition, message):
    if not condition:
        raise ValueError(message)


def unique_object(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, f"duplicate JSON key: {key}")
        result[key] = value
    return result


def load_json(path):
    with path.open(encoding="utf-8") as handle:
        return json.load(handle, object_pairs_hook=unique_object)


def text(obj, key):
    value = obj[key]
    require(isinstance(value, str) and value.strip() == value and value,
            f"invalid lock field: {key}")
    require(not any(c in value for c in "\r\n\0"), f"invalid lock field: {key}")
    return value


def relative(value):
    path = PurePosixPath(value)
    require(not path.is_absolute() and ".." not in path.parts and
            str(path) == value and value != ".", f"invalid relative path: {value}")
    return value


def flags(obj):
    value = obj["flags"]
    require(isinstance(value, list) and all(isinstance(x, str) and x.startswith("-")
            for x in value), "invalid flags in lock")
    return value


def declaration(path):
    fields = {}
    current = None
    for line in path.read_text(encoding="utf-8").splitlines():
        if not line.strip() or line.lstrip().startswith("-- "):
            continue
        match = re.match(r"^([a-z-]+):\s*(.*)$", line)
        if match:
            current, value = match.groups()
            require(current not in fields, f"duplicate declaration field in {path}")
            fields[current] = value.split()
        else:
            require(current is not None and line[:1].isspace(),
                    f"invalid library declaration: {path}")
            fields[current].extend(line.split())
    return fields


def ignored(path):
    return bool(set(path.parts) & {"_build", ".git", "__pycache__"}) or path.suffix == ".agdai"


def walk_error(error):
    raise error


def verify(root, lock):
    require(type(lock["schema_version"]) is int and lock["schema_version"] == 1,
            "unsupported lock schema_version")
    version = text(lock["agda"], "version")
    require(re.fullmatch(r"\d+(?:\.\d+)+", version), "invalid Agda version in lock")
    dep, project = lock["cubical"], lock["project"]
    for key in ("commit", "upstream_parent"):
        require(re.fullmatch(r"[0-9a-f]{40}", text(dep, key)), f"invalid {key} in lock")
    require(re.fullmatch(r"[0-9a-f]{64}", text(dep, "tree_sha256")), "invalid tree hash")
    manifest = load_json(root / relative(text(dep, "manifest")))
    require(isinstance(manifest, dict) and manifest, "empty or invalid dependency manifest")
    for name, digest in manifest.items():
        relative(name)
        require(not ignored(PurePosixPath(name)), f"runtime artifact in manifest: {name}")
        require(isinstance(digest, str) and re.fullmatch(r"[0-9a-f]{64}", digest),
                f"invalid manifest digest: {name}")
    tree = "".join(f"{manifest[name]}  {name}\n" for name in sorted(manifest))
    require(hashlib.sha256(tree.encode()).hexdigest() == dep["tree_sha256"],
            "dependency manifest tree hash differs from lock")
    default = text(dep, "path")
    cubical = (root / os.environ.get("CUBICAL_DIR", default)).resolve()
    require(cubical.is_dir(), f"missing Cubical directory: {cubical}")
    for name, digest in manifest.items():
        path = cubical / name
        require(path.is_file(), f"missing dependency file: {path}")
        require(hashlib.sha256(path.read_bytes()).hexdigest() == digest,
                f"changed dependency file: {path}")
    # Check the full file set, not only imports reachable from today's roots.
    for directory, dirs, files in os.walk(cubical, onerror=walk_error):
        dirs[:] = [d for d in dirs if d not in {"_build", ".git", "__pycache__"}]
        for name in files:
            path = (Path(directory) / name).relative_to(cubical)
            require(ignored(path) or path.as_posix() in manifest,
                    f"unexpected dependency file: {path}")
        for name in dirs:
            require(not (Path(directory) / name).is_symlink(),
                    f"unexpected dependency directory symlink: {name}")
    require("cubical.agda-lib" in manifest, "library declaration missing from manifest")
    dep_file = cubical / "cubical.agda-lib"
    project_file = root / relative(text(project, "library_file"))
    for obj, path in ((dep, dep_file), (project, project_file)):
        fields = declaration(path)
        require(fields.get("name") == [text(obj, "library")], f"library name mismatch: {path}")
        require(fields.get("flags") == flags(obj), f"library flags mismatch: {path}")
        includes = obj["include"]
        require(isinstance(includes, list) and includes and
                all(isinstance(x, str) and x for x in includes), "invalid include paths in lock")
        require(fields.get("include") == includes, f"library include mismatch: {path}")
    require(declaration(project_file).get("depend") == [dep["library"]],
            "project dependency declaration differs from lock")
    relative(text(project, "roots_file"))
    return version, dep_file, project_file


def settings(args):
    seconds = args.timeout if args.timeout is not None else os.environ.get("DELOOP_TIMEOUT", "600")
    require(re.fullmatch(r"\d+(?:\.\d+)?", seconds) and float(seconds) > 0,
            "timeout must be a positive number of seconds")
    heap = os.environ.get("DELOOP_HEAP_LIMIT", "12G")
    match = re.fullmatch(r"([1-9]\d*)([KMG])", heap)
    require(match is not None, "DELOOP_HEAP_LIMIT must be a positive size, e.g. 8G or 512M")
    require(int(match[1]) * 1024 ** ("KMG".index(match[2]) + 1) <= 16 * 1024 ** 3,
            "DELOOP_HEAP_LIMIT exceeds the 16 GiB maximum")
    return seconds, heap


def compiler(root, env, heap, expected):
    requested = os.environ.get("AGDA", "agda")
    # AGDA is an executable, not a shell command with flags. Relative paths use agda/.
    if "/" in requested:
        executable = str((root / requested).absolute())
    else:
        executable = shutil.which(requested)
    require(executable is not None, f"Agda executable not found: {requested}")
    result = subprocess.run([executable, "--numeric-version", "+RTS", "-N1", f"-M{heap}", "-RTS"],
                            cwd=root, env=env, text=True, capture_output=True, timeout=10)
    require(result.returncode == 0, f"Agda version query failed: {result.stderr.strip()}")
    require(result.stdout.strip() == expected,
            f"Agda version mismatch: expected {expected}, got {result.stdout.strip()!r} ({executable})")
    return executable


def run(args):
    seconds, heap = settings(args)
    lock = load_json(ROOT / "deps.lock.json")
    version, dep_file, project_file = verify(ROOT, lock)
    roots_file = ROOT / lock["project"]["roots_file"]
    names = [args.file] if args.file is not None else [line.split("#", 1)[0].strip()
             for line in roots_file.read_text(encoding="utf-8").splitlines()]
    inputs = [(ROOT / name).resolve() for name in names if name]
    require(inputs, f"no check roots in {roots_file}")
    for path in inputs:
        require(path.is_file(), f"missing input: {path}")
    local = ROOT / ".local"
    app_dir = local / "agda"
    app_dir.mkdir(parents=True, exist_ok=True)
    env = dict(os.environ, AGDA_DIR=str(app_dir))
    # AGDA_DIR isolates library/default configuration, NOT the compiler's data
    # directory. Keep HOME/XDG_DATA_HOME intact: Agda supplies its own builtins.
    executable = compiler(ROOT, env, heap, version)
    registry = local / "libraries"
    entries = [str(dep_file), str(project_file)]
    require(not any("\n" in value or "\r" in value for value in entries),
            "library paths cannot contain line breaks")
    registry.write_text("\n".join(entries) + "\n", encoding="utf-8")
    print(f"[check] compiler={executable} version={version}", flush=True)
    print(f"[check] verified dependency={dep_file.parent}", flush=True)
    print(f"[check] AGDA_DIR={app_dir} registry={registry}", flush=True)
    print(f"[check] timeout={seconds}s heap={heap} capabilities=1 lock={os.environ.get('DELOOP_LOCK', '/tmp/delooping-agda.lock')}", flush=True)
    if args.configure_only:
        print("[check] configuration status=0 (no type-checking)", flush=True)
        return 0
    require(shutil.which("timeout"), "GNU timeout is required")
    for path in inputs:
        command = ["timeout", "--kill-after=10s", f"{seconds}s", executable,
                   f"--library-file={registry}", "--no-default-libraries",
                   f"--library={lock['project']['library']}", str(path),
                   "+RTS", "-N1", f"-M{heap}", "-RTS"]
        print(f"[check] {shlex.join(command)}", flush=True)
        status = subprocess.run(command, cwd=ROOT, env=env).returncode
        status = 128 - status if status < 0 else status
        print(f"[check] {path.name} status={status}", flush=True)
        if status:
            return status
    return 0


def main():
    parser = argparse.ArgumentParser(description=__doc__, epilog=(
        "Paths are relative to agda/, regardless of working directory. No arguments checks roots.txt. "
        "Overrides: AGDA (executable), CUBICAL_DIR, DELOOP_TIMEOUT (seconds, default 600), "
        "DELOOP_HEAP_LIMIT (default 12G; maximum 16G), DELOOP_LOCK. No downloads or global libraries."))
    parser.add_argument("--configure-only", action="store_true", help="verify inputs and write the local registry without checking proofs")
    parser.add_argument("file", nargs="?", help="single Agda source, otherwise all checked-in roots")
    parser.add_argument("timeout", nargs="?", help="per-file timeout in seconds (overrides DELOOP_TIMEOUT)")
    args = parser.parse_args()
    try:
        return run(args)
    except (OSError, ValueError, KeyError, TypeError, AttributeError, subprocess.SubprocessError) as error:
        print(f"[check] configuration failed: {error}; status=1", file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())
