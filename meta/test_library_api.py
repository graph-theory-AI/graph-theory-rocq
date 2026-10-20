#!/usr/bin/env python3
"""API index controls: explicit trust, project enrollment and stale artifacts."""
from pathlib import Path
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
                 patch.object(API.subprocess, "check_output", return_value=b"base/theories/sample.v\0"):
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


if __name__ == "__main__":
    unittest.main()
