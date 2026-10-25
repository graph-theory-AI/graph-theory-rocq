#!/usr/bin/env python3
"""API index controls: explicit trust, project enrollment, stale artifacts, and git read only at the root's own toplevel."""
import os
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch

import library_api as API


class IndexControls(unittest.TestCase):
    def setUp(self):
        self.declarations = {
            "GTBase.sample.audited": {"module": "GTBase.sample", "path": "base/theories/sample.v",
                                      "line": 1, "kind": "Definition"},
            "GTBase.sample.neighbour": {"module": "GTBase.sample", "path": "base/theories/sample.v",
                                        "line": 2, "kind": "Definition"},
            "GTBase.sample.fact": {"module": "GTBase.sample", "path": "base/theories/sample.v",
                                   "line": 3, "kind": "Lemma"},
        }
        self.families = {"sample": {"canonical_name": "GTBase.sample.audited", "owner": "base",
                                     "status": "deprecated", "fidelity": "FAITHFUL",
                                     "api_theorems": ["GTBase.sample.fact"]}}

    def render(self, verdicts):
        with patch.object(API, "public_declarations", return_value=(
                {"GTBase.sample": "base/theories/sample.v"}, self.declarations)), \
             patch.object(API, "load_library_registry", return_value={"primitives": self.families}), \
             patch.object(API.FF, "expand_registry", return_value=(verdicts, [])):
            return API.render()

    def test_fidelity_does_not_spread_to_neighbours_or_theorems(self):
        text = self.render([{"qualified_name": "GTBase.sample.audited",
                             "path": "base/theories/sample.v", "verdict": "LIGHTWEIGHT",
                             "note": "Only the guarded | finite contract."}])
        rows = {name: next(row for row in text.splitlines()
                           if row.startswith("| [" + name + "]")) for name in self.declarations}
        self.assertIn("LIGHTWEIGHT: Only the guarded \\| finite contract.", rows["GTBase.sample.audited"])
        self.assertIn("Unclassified", rows["GTBase.sample.neighbour"])
        self.assertIn("Unclassified", rows["GTBase.sample.fact"])
        self.assertIn("Principal lemma: sample", rows["GTBase.sample.fact"])
        self.assertIn("does not deprecate the canonical public API", text)

    def test_family_verdict_does_not_create_explicit_primitive_audit(self):
        text = self.render([])
        row = next(row for row in text.splitlines() if row.startswith("| [GTBase.sample.audited]"))
        self.assertIn("Unclassified", row)
        self.assertNotIn("FAITHFUL", row)

    def test_audited_missing_declaration_refuses(self):
        with self.assertRaisesRegex(ValueError, "no indexed declaration"):
            self.render([{"qualified_name": "GTBase.sample.missing",
                          "path": "base/theories/sample.v", "verdict": "FAITHFUL", "note": "x"}])

    def test_project_enrollment_and_nested_names_use_shared_parser(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            source = root / "base/theories/sample.v"
            source.parent.mkdir(parents=True)
            source.write_text("Module Nested.\nDefinition value := 0.\nEnd Nested.\n")
            project = root / "base/_CoqProject"
            project.write_text("-Q theories GTBase\n")
            with patch.object(API, "ROOT", root), \
                 patch.object(API, "tracked_files", return_value=["base/theories/sample.v", ""]):
                with self.assertRaisesRegex(ValueError, "not build-listed"):
                    API.public_declarations()
                project.write_text("-Q theories GTBase\ntheories/sample.v\n")
                modules, declarations = API.public_declarations()
                self.assertEqual(modules, {"GTBase.sample": "base/theories/sample.v"})
                self.assertIn("GTBase.sample.Nested.value", declarations)

    def test_missing_and_stale_index_refuse_then_exact_bytes_pass(self):
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory) / "LIBRARY_API.md"
            with patch.object(API, "OUTPUT", output), patch.object(API, "render", return_value="current\n"):
                self.assertEqual(API.main(["--check"]), 1)
                output.write_text("old\n")
                self.assertEqual(API.main(["--check"]), 1)
                output.write_text("current\n")
                self.assertEqual(API.main(["--check"]), 0)


class TrackedSources(unittest.TestCase):
    """The tracked sources come from git only at the root's own toplevel (the O-1 rule); anything else is refused."""
    def setUp(self):
        temporary = tempfile.TemporaryDirectory(prefix="library-api-git-")
        self.addCleanup(temporary.cleanup)
        self.t = Path(temporary.name).resolve()
        environment = patch.dict(os.environ, {"GIT_CONFIG_NOSYSTEM": "1", "GIT_CONFIG_GLOBAL": os.devnull,
                                              "GIT_CEILING_DIRECTORIES": str(self.t)})
        environment.start()
        self.addCleanup(environment.stop)
        for key in API.GIT_SELECT_ENV:
            os.environ.pop(key, None)

    def repo(self, path, tracked):
        # No automatic gc / maintenance in the fixture (errno 39 on CI when a background run outlives the test).
        quiet = ["-c", "gc.auto=0", "-c", "maintenance.auto=false"]
        subprocess.run(["git", "-c", "init.defaultBranch=main", *quiet, "init", "-q", str(path)], check=True, capture_output=True)
        for relative in tracked:
            (path / relative).parent.mkdir(parents=True, exist_ok=True)
            (path / relative).write_text("Definition x := 0.\n")
            subprocess.run(["git", *quiet, "-C", str(path), "add", relative], check=True, capture_output=True)
        return path

    def test_a_toplevel_checkout_lists_its_tracked_files(self):
        root = self.repo(self.t / "top", ["base/theories/sample.v"])
        (root / "base/theories/untracked.v").write_text("Definition y := 0.\n")
        self.assertEqual([p for p in API.tracked_files(root) if p], ["base/theories/sample.v"])

    def test_o1_a_tree_nested_in_another_repository_is_refused(self):
        enclosing = self.repo(self.t / "enclosing", ["base/theories/other.v"])
        root = enclosing / "archive"
        (root / "base/theories").mkdir(parents=True)
        (root / "base/theories/sample.v").write_text("Definition x := 0.\n")
        listed = subprocess.run(["git", "-C", str(enclosing), "ls-files"], check=True, capture_output=True, text=True)
        self.assertEqual(listed.stdout.split(), ["base/theories/other.v"])  # the enclosing repository exists, tracking another file
        with self.assertRaisesRegex(ValueError, "not its own git toplevel"):
            API.tracked_files(root)

    def test_an_archive_without_a_repository_is_refused(self):
        root = self.t / "plain"
        (root / "base/theories").mkdir(parents=True)
        (root / "base/theories/sample.v").write_text("Definition x := 0.\n")
        with self.assertRaisesRegex(ValueError, "not its own git toplevel"):
            API.tracked_files(root)

    def test_git_selecting_variables_are_ignored(self):
        enclosing = self.repo(self.t / "enclosing", ["base/theories/other.v"])
        nested = enclosing / "archive"
        nested.mkdir()
        own = self.repo(self.t / "own", ["base/theories/own.v"])
        with patch.dict(os.environ, {"GIT_DIR": str(enclosing / ".git"), "GIT_WORK_TREE": str(nested)}):
            with self.assertRaisesRegex(ValueError, "not its own git toplevel"):
                API.tracked_files(nested)
            self.assertEqual([p for p in API.tracked_files(own) if p], ["base/theories/own.v"])


if __name__ == "__main__":
    unittest.main()
