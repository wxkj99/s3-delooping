#!/usr/bin/env python3
"""Miniature, temporary source fixtures; no Agda invocation or project writes.

Run: python3 -B agda/tools/test_deps.py
"""
from contextlib import redirect_stdout
import io
import json
import os
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

# Importing this test as well as running it directly must not cache deps.py.
sys.dont_write_bytecode = True
import deps


class MaskingTests(unittest.TestCase):
    def test_nested_comments_strings_pragmas_and_line_comments(self):
        text = r'''{-# OPTIONS --safe --cubical
import DeloopS3.FakeOption
#-}
{- module Wrong.Header where
   {- open import DeloopS3.Nested -}
   import DeloopS3.StillCommented
-}
module DeloopS3.Real where
-- open import DeloopS3.LineComment
s = "escaped quote: \" -- {- not a comment
open import DeloopS3.InString
"
open {- nested {- block -} -} import DeloopS3.Actual
import
  Cubical.Real as R
-- trailing comment without newline'''
        masked = deps.strip_comments_strings(text)
        self.assertEqual(len(masked), len(text))
        self.assertEqual([i for i, c in enumerate(masked) if c == "\n"],
                         [i for i, c in enumerate(text) if c == "\n"])
        self.assertEqual(deps.MODULE.search(masked).group(1), "DeloopS3.Real")
        self.assertEqual(set(deps.IMPORT.findall(masked)), {"DeloopS3.Actual", "Cubical.Real"})

    def test_inline_layout_imports(self):
        masked = deps.strip_comments_strings("private { import DeloopS3.A; open import DeloopS3.B }")
        self.assertEqual(set(deps.IMPORT.findall(masked)), {"DeloopS3.A", "DeloopS3.B"})


class AuditTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.base = Path(temporary.name)
        self.project = self.base / "agda"
        self.src = self.project / "src"
        self.vendor = self.base / "vendor" / "cubical"
        self.src.mkdir(parents=True)
        self.env = patch.dict(os.environ, {"CUBICAL_DIR": ""})
        self.env.start()
        self.addCleanup(self.env.stop)
        self.assembly = "DeloopS3.Assembly.Complete"
        self.hpinf = "DeloopS3.HPInf.Complete"
        self.shared = "DeloopS3.Shared"
        self.write_module(self.assembly, [self.shared])
        self.write_module(self.hpinf, [self.shared])
        self.write_module(self.shared)
        # An old assembly module is deliberately NOT an implicit root.
        self.write_module("DeloopS3.Assembly.Final")
        self.manifest = self.project / "roots.txt"
        self.manifest.write_text("# Final source roots\nsrc/DeloopS3/Assembly/Complete.agda\n"
                                 "src/DeloopS3/HPInf/Complete.agda\n", encoding="utf-8")

    def write_module(self, name, imports=(), *, base=None, declared=None):
        base = base if base is not None else self.src
        path = base.joinpath(*name.split(".")).with_suffix(".agda")
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text("{-# OPTIONS --safe --cubical #-}\n"
                        f"module {declared or name} where\n"
                        + "".join(f"open import {dep}\n" for dep in imports), encoding="utf-8")
        return path

    def lock(self, path="../vendor/cubical"):
        self.vendor.mkdir(parents=True, exist_ok=True)
        (self.project / "deps.lock.json").write_text(
            json.dumps({"schema_version": 1, "cubical": {"path": path}}), encoding="utf-8")

    def cli(self, *args):
        output = io.StringIO()
        with redirect_stdout(output):
            status = deps.main(["--project", str(self.project), "--json", *args])
        return status, json.loads(output.getvalue())

    def test_valid_manifest_and_per_root_closures(self):
        status, result = self.cli()
        self.assertEqual(status, 0)
        self.assertTrue(result["ok"])
        self.assertEqual(result["roots"], [self.assembly, self.hpinf])
        self.assertEqual(result["counts"]["total"], 4)
        self.assertEqual(result["counts"]["reachable"], 3)
        self.assertEqual(result["archive_candidates"], ["DeloopS3.Assembly.Final"])
        self.assertEqual(result["root_closures"][self.assembly]["local"], [self.assembly, self.shared])

    def test_missing_manifest_is_configuration_error(self):
        self.manifest.unlink()
        status, result = self.cli()
        self.assertEqual(status, 1)
        self.assertIn("missing roots.txt", result["configuration_errors"][0])
        self.assertEqual(result["roots"], [])

    def test_explicit_roots_replace_even_missing_manifest(self):
        self.manifest.unlink()
        status, result = self.cli("--root", self.assembly, "--root", "src/DeloopS3/Shared.agda")
        self.assertEqual(status, 0)
        self.assertEqual(result["roots"], [self.assembly, self.shared])
        self.assertEqual(result["root_source"], "explicit")

    def test_empty_manifest_fails(self):
        self.manifest.write_text("# no selected roots\n")
        self.assertEqual(self.cli()[0], 1)

    def test_missing_root_fails(self):
        status, result = self.cli("--root", "DeloopS3.Missing")
        self.assertEqual(status, 1)
        self.assertEqual(result["missing_roots"], ["DeloopS3.Missing"])

    def test_archive_path_is_not_a_root(self):
        status, result = self.cli("--root", "archive/src/DeloopS3/Old.agda")
        self.assertEqual(status, 1)
        self.assertTrue(result["configuration_errors"])

    def test_missing_local_dependency_fails(self):
        self.write_module(self.shared, ["DeloopS3.Missing"])
        status, result = self.cli()
        self.assertEqual(status, 1)
        self.assertEqual(result["unresolved_local_imports"], ["DeloopS3.Missing"])
        self.assertEqual(result["unresolved_local_import_details"][0]["importer"], self.shared)

    def test_unreachable_active_source_is_still_audited(self):
        self.write_module("DeloopS3.Unreachable", ["DeloopS3.Missing"])
        status, result = self.cli()
        self.assertEqual(status, 1)
        self.assertEqual(result["unresolved_local_imports"], ["DeloopS3.Missing"])

    def test_module_path_mismatch_fails(self):
        self.write_module(self.shared, declared="DeloopS3.Wrong")
        status, result = self.cli()
        self.assertEqual(status, 1)
        self.assertEqual(result["module_path_mismatches"][0]["declared"], "DeloopS3.Wrong")

    def test_commented_declaration_does_not_satisfy_module_check(self):
        path = self.src / "DeloopS3" / "Shared.agda"
        path.write_text("{- module DeloopS3.Shared where -}\n")
        status, result = self.cli()
        self.assertEqual(status, 1)
        self.assertIsNone(result["module_path_mismatches"][0]["declared"])

    def test_archive_only_dependency_is_reported_not_resolved(self):
        self.write_module(self.shared, ["DeloopS3.Old"])
        self.write_module("DeloopS3.Old", ["DeloopS3.ArchiveMissing"],
                          base=self.project / "archive" / "src")
        status, result = self.cli()
        self.assertEqual(status, 1)
        self.assertEqual(result["unresolved_local_imports"], ["DeloopS3.Old"])
        self.assertEqual(result["reachable_imports_archive"][0]["archive_candidates"],
                         ["archive/src/DeloopS3/Old.agda"])
        self.assertNotIn("DeloopS3.Old", result["reachable"])
        status, result = self.cli("--root", "DeloopS3.Old")
        self.assertEqual(status, 1)
        self.assertEqual(result["missing_root_details"][0]["archive_candidates"],
                         ["archive/src/DeloopS3/Old.agda"])

    def test_unused_archive_is_not_an_obligation(self):
        self.write_module("DeloopS3.Old", ["DeloopS3.ArchiveMissing"],
                          base=self.project / "archive" / "src", declared="Bad.Name")
        self.assertEqual(self.cli()[0], 0)

    def test_symlink_cannot_resolve_active_source_from_archive(self):
        archived = self.write_module(self.shared, base=self.project / "archive" / "src")
        source = self.src / "DeloopS3" / "Shared.agda"
        source.unlink()
        source.symlink_to(archived)
        status, result = self.cli()
        self.assertEqual(status, 1)
        self.assertTrue(result["source_path_violations"])
        self.assertEqual(result["unresolved_local_imports"], [self.shared])

    def test_external_is_optional_and_transitive(self):
        self.write_module(self.shared, ["Cubical.One", "Agda.Primitive"])
        # Local-only mode deliberately does not require any Cubical installation.
        status, local = self.cli()
        self.assertEqual(status, 0)
        self.assertFalse(local["external"]["enabled"])
        self.assertEqual(local["counts"]["external_reachable"], 0)
        self.lock()
        self.write_module("Cubical.One", ["Cubical.Two"], base=self.vendor)
        self.write_module("Cubical.Two", ["Cubical.One", "Agda.Builtin.Nat"], base=self.vendor)
        self.write_module("Cubical.NotUsed", ["Unknown.NotRequired"], base=self.vendor)
        status, result = self.cli("--external")
        self.assertEqual(status, 0)
        self.assertEqual(result["external"]["reachable"], ["Cubical.One", "Cubical.Two"])
        self.assertEqual(result["external"]["directory"], str(self.vendor))
        self.assertFalse(result["external"]["lock_integrity_verified"])
        self.assertEqual(result["counts"]["transitive_source_modules"], 5)
        self.assertEqual(result["compiler_builtins"], ["Agda.Builtin.Nat", "Agda.Primitive"])
        self.assertEqual(result["counts"]["compiler_builtins"], 2)

    def test_missing_lock_external_fails(self):
        status, result = self.cli("--external")
        self.assertEqual(status, 1)
        self.assertTrue(result["configuration_errors"])

    def test_missing_external_module_fails(self):
        self.lock()
        self.write_module(self.shared, ["Cubical.One"])
        self.write_module("Cubical.One", ["Cubical.Missing"], base=self.vendor)
        status, result = self.cli("--external")
        self.assertEqual(status, 1)
        self.assertEqual(result["external"]["unresolved_imports"][0]["module"], "Cubical.Missing")

    def test_external_module_mismatch_fails(self):
        self.lock()
        self.write_module(self.shared, ["Cubical.One"])
        self.write_module("Cubical.One", base=self.vendor, declared="Cubical.Wrong")
        status, result = self.cli("--external")
        self.assertEqual(status, 1)
        self.assertEqual(result["module_path_mismatches"][0]["expected"], "Cubical.One")

    def test_relative_environment_override_is_project_relative(self):
        alternative = self.base / "alternative"
        self.write_module("Cubical.One", base=alternative)
        self.write_module(self.shared, ["Cubical.One"])
        with patch.dict(os.environ, {"CUBICAL_DIR": "../alternative"}):
            status, result = self.cli("--external")
        self.assertEqual(status, 0)
        self.assertEqual(result["external"]["directory"], str(alternative))
        self.assertEqual(result["external"]["source"], "CUBICAL_DIR")

    def test_unknown_nonbuiltins_are_not_silently_ignored(self):
        self.lock()
        self.write_module(self.shared, ["Cubical.One", "Other.LocalDependency"])
        self.write_module("Cubical.One", ["Other.ExternalDependency", "Agda.Primitive"], base=self.vendor)
        status, result = self.cli("--external")
        self.assertEqual(status, 1)
        self.assertEqual({item["module"] for item in result["unknown_nonbuiltin_imports"]},
                         {"Other.LocalDependency", "Other.ExternalDependency"})

    def test_audit_is_read_only(self):
        self.lock()
        self.write_module(self.shared, ["Cubical.One"])
        self.write_module("Cubical.One", base=self.vendor)

        def snapshot():
            return {str(p.relative_to(self.base)): (p.stat().st_mtime_ns, p.read_bytes())
                    for p in self.base.rglob("*") if p.is_file()}

        before = snapshot()
        self.assertTrue(deps.audit(self.project, external=True)["ok"])
        self.assertEqual(self.cli("--external")[0], 0)
        self.assertEqual(snapshot(), before)


if __name__ == "__main__":
    unittest.main()
