#!/usr/bin/env python3
"""Small offline fixtures; never invoke the real Agda compiler or proof checks."""
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest

SOURCE = Path(__file__).resolve().parent.parent
FLAGS = ["--safe", "--cubical"]
MOCK = '''#!/usr/bin/env python3
import fcntl, json, os, sys, time
from pathlib import Path
args = sys.argv[1:]
# The shell's single flock must still be held during version and root checks.
with open(os.environ["DELOOP_LOCK"], "a") as lock:
    try:
        fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
    except BlockingIOError:
        pass
    else:
        raise AssertionError("runner lock is not held")
with open(os.environ["MOCK_LOG"], "a") as handle:
    handle.write(json.dumps({"args": args, "cwd": os.getcwd(),
                            "AGDA_DIR": os.environ.get("AGDA_DIR"),
                            "HOME": os.environ.get("HOME")}) + "\\n")
if "--numeric-version" in args:
    print(os.environ.get("MOCK_VERSION", "2.8.0.2"))
    sys.exit(0)
assert "--no-default-libraries" in args
assert "--library=delooping" in args
registry = Path(next(x.split("=", 1)[1] for x in args if x.startswith("--library-file=")))
assert all(Path(x).is_absolute() and Path(x).is_file() for x in registry.read_text().splitlines())
assert Path(os.environ["AGDA_DIR"]).is_dir()
time.sleep(float(os.environ.get("MOCK_SLEEP", "0")))
sys.exit(int(os.environ.get("MOCK_EXIT", "0")))
'''


class ConfigureTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="delooping portable tests ")
        self.addCleanup(self.temp.cleanup)
        self.base = Path(self.temp.name)
        self.root = self.base / "project with spaces/agda"
        self.vendor = self.root.parent / "vendor/cubical"
        (self.root / "tools").mkdir(parents=True)
        (self.root / "deps").mkdir()
        self.vendor.mkdir(parents=True)
        for filename in ("tools/configure.py", "check.sh"):
            shutil.copy2(SOURCE / filename, self.root / filename)
        self.write(self.vendor / "cubical.agda-lib", "name: cubical-0.9\ninclude: .\nflags: --safe --cubical\n")
        self.write(self.vendor / "Tiny.agda", "module Tiny where\n")
        self.write(self.vendor / "README", "All tracked bytes count.\n")
        self.write(self.root / "delooping.agda-lib", "name: delooping\ninclude: src\ndepend: cubical-0.9\nflags: --safe --cubical\n")
        self.write(self.root / "roots.txt", "# two roots\nsrc/First.agda\nsrc/Second.agda\n")
        self.write(self.root / "src/First.agda", "module First where\n")
        self.write(self.root / "src/Second.agda", "module Second where\n")
        self.write(self.root / "libraries", "# committed portable registry must remain unchanged\n")
        self.lock = {
            "schema_version": 1, "agda": {"version": "2.8.0.2"},
            "cubical": {"path": "../vendor/cubical", "commit": "a" * 40,
                        "upstream_parent": "b" * 40, "library": "cubical-0.9",
                        "manifest": "deps/files.json", "tree_sha256": "", "flags": FLAGS,
                        "include": ["."]},
            "project": {"library": "delooping", "library_file": "delooping.agda-lib",
                        "flags": FLAGS, "include": ["src"], "roots_file": "roots.txt"}}
        self.update_manifest()
        self.mock = self.base / "compiler with spaces/agda"
        self.write(self.mock, MOCK)
        self.mock.chmod(0o755)
        self.home = self.base / "unconfigured home"
        self.home.mkdir()
        self.foreign = self.base / "unrelated working directory"
        self.foreign.mkdir()
        self.log = self.base / "compiler.jsonl"
        self.env = {key: value for key, value in os.environ.items()
                    if not key.startswith(("DELOOP_", "MOCK_", "AGDA")) and key != "CUBICAL_DIR"}
        self.env.update(AGDA=str(self.mock), HOME=str(self.home),
                        AGDA_DIR="/nonexistent/global/config", MOCK_LOG=str(self.log),
                        DELOOP_LOCK=str(self.base / "one run lock"))

    def write(self, path, text):
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text, encoding="utf-8")

    def save_lock(self):
        self.write(self.root / "deps.lock.json", json.dumps(self.lock))

    def update_manifest(self):
        manifest = {p.relative_to(self.vendor).as_posix(): hashlib.sha256(p.read_bytes()).hexdigest()
                    for p in self.vendor.rglob("*") if p.is_file()}
        self.write(self.root / "deps/files.json", json.dumps(manifest))
        tree = "".join(f"{manifest[p]}  {p}\n" for p in sorted(manifest))
        self.lock["cubical"]["tree_sha256"] = hashlib.sha256(tree.encode()).hexdigest()
        self.save_lock()

    def invoke(self, *args, status=0, **env):
        result = subprocess.run(["bash", str(self.root / "check.sh"), *args],
                                cwd=self.foreign, env=dict(self.env, **env),
                                capture_output=True, text=True, timeout=15)
        self.assertEqual(result.returncode, status, result.stdout + result.stderr)
        return result.stdout + result.stderr

    def calls(self, include_version=False):
        calls = [json.loads(line) for line in self.log.read_text().splitlines()] if self.log.exists() else []
        return [call for call in calls if include_version or "--numeric-version" not in call["args"]]

    def test_default_checks_both_roots_isolates_configuration(self):
        output = self.invoke()
        calls = self.calls()
        self.assertEqual(len(calls), 2)
        for call in calls:
            self.assertEqual(call["cwd"], str(self.root))
            self.assertEqual(call["AGDA_DIR"], str(self.root / ".local/agda"))
            self.assertEqual(call["HOME"], str(self.home))
            self.assertIn("-M12G", call["args"])
            self.assertIn("-N1", call["args"])
        self.assertIn("First.agda", str(calls[0]))
        self.assertIn("Second.agda", str(calls[1]))
        self.assertIn("timeout=600s", output)
        self.assertEqual(list(self.home.iterdir()), [])
        self.assertEqual((self.root / "libraries").read_text(), "# committed portable registry must remain unchanged\n")
        self.assertEqual((self.root / ".local/libraries").read_text().splitlines(),
                         [str(self.vendor / "cubical.agda-lib"), str(self.root / "delooping.agda-lib")])

    def test_single_file_and_timeout_precedence(self):
        output = self.invoke("src/Second.agda", "2", DELOOP_TIMEOUT="3", DELOOP_HEAP_LIMIT="512M")
        self.assertEqual(len(self.calls()), 1)
        self.assertIn("Second.agda", str(self.calls()[0]))
        self.assertIn("timeout=2s heap=512M", output)
        self.assertIn("-M512M", self.calls()[0]["args"])

    def test_configure_only_and_timeout_environment(self):
        output = self.invoke("--configure-only", DELOOP_TIMEOUT="7")
        self.assertIn("timeout=7s", output)
        self.assertFalse(self.calls())
        self.assertTrue((self.root / ".local/libraries").exists())

    def test_optional_relative_and_absolute_cubical_override(self):
        alternate = self.root.parent / "alternate dependency"
        shutil.copytree(self.vendor, alternate)
        shutil.rmtree(self.vendor)
        for value in ("../alternate dependency", str(alternate)):
            with self.subTest(value=value):
                self.invoke("--configure-only", CUBICAL_DIR=value)
                self.assertIn(str(alternate / "cubical.agda-lib"),
                              (self.root / ".local/libraries").read_text())

    def test_relative_compiler_override(self):
        local_mock = self.root / "compiler path/agda"
        local_mock.parent.mkdir()
        shutil.copy2(self.mock, local_mock)
        self.invoke("--configure-only", AGDA="compiler path/agda")
        self.assertEqual(len(self.calls(include_version=True)), 1)

    def test_wrong_compiler_rejected_even_if_path_has_good_one(self):
        output = self.invoke("--configure-only", status=1, MOCK_VERSION="2.7.0")
        self.assertIn("version mismatch", output)
        self.assertFalse((self.root / ".local/libraries").exists())

    def test_missing_compiler_no_fallback(self):
        self.invoke("--configure-only", status=1, AGDA=str(self.base / "absent agda"))
        self.assertFalse(self.calls(include_version=True))

    def test_all_manifest_bytes_verified(self):
        for filename in ("Tiny.agda", "README", "cubical.agda-lib"):
            with self.subTest(filename=filename):
                path = self.vendor / filename
                original = path.read_text()
                path.write_text(original + "changed\n")
                self.assertIn("changed dependency file", self.invoke("--configure-only", status=1))
                path.write_text(original)
        self.assertFalse(self.calls(include_version=True))

    def test_missing_vendor_files_rejected(self):
        for filename in ("Tiny.agda", "README", "cubical.agda-lib"):
            with self.subTest(filename=filename):
                path = self.vendor / filename
                original = path.read_bytes()
                path.unlink()
                self.assertIn("missing dependency file", self.invoke("--configure-only", status=1))
                path.write_bytes(original)

    def test_missing_vendor_directory_rejected(self):
        shutil.rmtree(self.vendor)
        self.assertIn("missing Cubical directory", self.invoke("--configure-only", status=1))

    def test_unexpected_source_rejected(self):
        self.write(self.vendor / "unexpected/New.agda", "module New where\n")
        self.assertIn("unexpected dependency file", self.invoke("--configure-only", status=1))

    def test_removed_manifest_source_still_rejected(self):
        manifest = json.loads((self.root / "deps/files.json").read_text())
        del manifest["Tiny.agda"]
        self.write(self.root / "deps/files.json", json.dumps(manifest))
        tree = "".join(f"{manifest[p]}  {p}\n" for p in sorted(manifest))
        self.lock["cubical"]["tree_sha256"] = hashlib.sha256(tree.encode()).hexdigest()
        self.save_lock()
        self.assertIn("unexpected dependency file", self.invoke("--configure-only", status=1))

    def test_runtime_artifacts_allowed(self):
        for path in ("_build/junk.agda", ".git/config", "__pycache__/cache.pyc", "Tiny.agdai"):
            self.write(self.vendor / path, "runtime artifact\n")
        self.invoke("--configure-only")

    def test_manifest_tree_hash_checked(self):
        self.lock["cubical"]["tree_sha256"] = "0" * 64
        self.save_lock()
        self.assertIn("tree hash", self.invoke("--configure-only", status=1))

    def test_library_identity_and_flags_match_lock(self):
        self.lock["cubical"]["library"] = "wrong-library"
        self.save_lock()
        self.assertIn("library name mismatch", self.invoke("--configure-only", status=1))
        self.lock["cubical"]["library"] = "cubical-0.9"
        self.lock["project"]["flags"] = ["--safe"]
        self.save_lock()
        self.assertIn("library flags mismatch", self.invoke("--configure-only", status=1))

    def test_library_include_paths_match_lock(self):
        project_file = self.root / "delooping.agda-lib"
        original = project_file.read_text()
        project_file.write_text(original.replace("include: src", "include: archive"))
        self.assertIn("library include mismatch", self.invoke("--configure-only", status=1))
        project_file.write_text(original)
        self.lock["cubical"]["include"] = ["different"]
        self.save_lock()
        self.assertIn("library include mismatch", self.invoke("--configure-only", status=1))
        self.lock["cubical"]["include"] = ["."]
        self.lock["project"]["include"] = "src"
        self.save_lock()
        self.assertIn("invalid include paths", self.invoke("--configure-only", status=1))

    def test_malformed_lock_rejected(self):
        for content in ("{", "{}", '[]', '{"schema_version":1,"schema_version":1}',
                        json.dumps(dict(self.lock, schema_version=2))):
            with self.subTest(content=content):
                self.write(self.root / "deps.lock.json", content)
                self.assertIn("configuration failed", self.invoke("--configure-only", status=1))

    def test_missing_inputs_rejected(self):
        self.invoke("", status=1)
        self.invoke("src/First.agda", "", status=1)
        self.assertIn("missing input", self.invoke("absent.agda", status=1))
        (self.root / "src/Second.agda").unlink()
        self.assertIn("missing input", self.invoke("--configure-only", status=1))

    def test_invalid_limits_rejected(self):
        for value in ("17G", "16385M", "0G", "unlimited"):
            with self.subTest(heap=value):
                self.invoke("--configure-only", status=1, DELOOP_HEAP_LIMIT=value)
        for value in ("0", "-1", "nan", "bad"):
            with self.subTest(seconds=value):
                self.invoke("--configure-only", status=1, DELOOP_TIMEOUT=value)
        self.invoke("--configure-only", DELOOP_HEAP_LIMIT="16G")

    def test_compiler_failure_preserved_and_stops_roots(self):
        self.assertIn("status=42", self.invoke(status=42, MOCK_EXIT="42"))
        self.assertEqual(len(self.calls()), 1)

    def test_timeout_exit_124_preserved(self):
        self.assertIn("status=124", self.invoke("src/First.agda", "0.1", status=124, MOCK_SLEEP="2"))

    def test_help_without_configuration(self):
        (self.root / "deps.lock.json").unlink()
        self.assertIn("--configure-only", self.invoke("--help"))
        self.assertFalse(self.calls(include_version=True))


if __name__ == "__main__":
    unittest.main()
