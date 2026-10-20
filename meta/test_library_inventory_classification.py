#!/usr/bin/env python3
"""G-4 controls: the residual-helper classification refuses every gap, each with its own message."""
import copy
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import library_classification as CL
import library_inventory as INV

FAMILY = "GTBase.base.edge_count"


def helper(qualified, path, line, body="0"):
    name = qualified.rsplit(".", 1)[-1]
    return {"qualified_name": qualified, "name": name, "path": path, "line": line,
            "normalized_name": INV.normalized_name(name), "body_shape_hash": INV.sha256(body)}


class Classification(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory(prefix="library-classification-")
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        conj = self.root / "cycle-theory/theories/conjectures"
        conj.mkdir(parents=True)
        (conj / "X1.v").write_text("Definition x1_widget (n : nat) := n.\n"
                                   "Lemma x1_count_sym : forall G, edge_count G = edge_count G.\n")
        (conj / "X2.v").write_text("Definition x2_widget (n : nat) := n.\n"
                                   "Lemma x2_count_sym : forall G, edge_count G = edge_count G.\n"
                                   "Definition x2_shape := 7.\n")
        (conj / "X3.v").write_text("Definition x3_form := 7.\n")
        self.helpers = [helper("Cycle.conjectures.X1.x1_widget", "cycle-theory/theories/conjectures/X1.v", 1),
                        helper("Cycle.conjectures.X1.x1_count_sym", "cycle-theory/theories/conjectures/X1.v", 2),
                        helper("Cycle.conjectures.X2.x2_widget", "cycle-theory/theories/conjectures/X2.v", 1),
                        helper("Cycle.conjectures.X2.x2_count_sym", "cycle-theory/theories/conjectures/X2.v", 2),
                        helper("Cycle.conjectures.X2.x2_shape", "cycle-theory/theories/conjectures/X2.v", 3, "7"),
                        helper("Cycle.conjectures.X3.x3_form", "cycle-theory/theories/conjectures/X3.v", 1, "7")]
        self.inventory = {"helpers": self.helpers, "groups": {
            "normalized_name": {"widget": ["Cycle.conjectures.X1.x1_widget", "Cycle.conjectures.X2.x2_widget"],
                                "count_sym": ["Cycle.conjectures.X1.x1_count_sym", "Cycle.conjectures.X2.x2_count_sym"],
                                "edge_count": ["A.edge_count", "B.edge_count"]},
            "body_shape_hash": {INV.sha256("7"): ["Cycle.conjectures.X2.x2_shape", "Cycle.conjectures.X3.x3_form"],
                                INV.sha256(""): ["Q.empty1", "Q.empty2"]}}}
        self.registry = {"edge-count": {"normalized_names": ["edge_count"], "source_definitions": ["A.edge_count"],
                                        "canonical_name": FAMILY, "api_theorems": []}}
        self.data = {
            "schema_version": 1, "header": ["controls"],
            "milestones": {"post-rc-wave": {"description": "the first library wave after the RC",
                                            "owner": "coordinator", "after": "RC"}},
            "names": {
                "widget": {"class": "candidate_family", "reason": "one notion in two rows, identical bodies",
                           "members": ["Cycle.conjectures.X1.x1_widget", "Cycle.conjectures.X2.x2_widget"],
                           "family_id": "widgets", "milestone": "post-rc-wave"},
                "count_sym": {"class": "family_companion", "reason": "symmetry companions of the edge count",
                              "members": ["Cycle.conjectures.X1.x1_count_sym", "Cycle.conjectures.X2.x2_count_sym"],
                              "family": "edge-count", "kind": "companion"}},
            "body_shapes": {INV.sha256("7"): {"class": "paper_specific", "reason": "two unrelated constants of value 7",
                                             "members": ["Cycle.conjectures.X2.x2_shape", "Cycle.conjectures.X3.x3_form"]}}}

    def run_check(self, data):
        path = self.root / "classification.json"
        path.write_text(json.dumps(data))
        with patch.object(INV, "ROOT", self.root):
            return CL.validate_classification(self.inventory, self.registry, path)[0]

    def assert_only(self, data, fragment):
        errors = self.run_check(data)
        self.assertEqual(len(errors), 1, errors)
        self.assertIn(fragment, errors[0])

    def test_control_passes_with_counts(self):
        path = self.root / "classification.json"
        path.write_text(json.dumps(self.data))
        with patch.object(INV, "ROOT", self.root):
            errors, line = CL.validate_classification(self.inventory, self.registry, path)
        self.assertEqual(errors, [])
        self.assertIn("names 2 (", line)
        self.assertIn("body_shapes 1 (paper_specific 1)", line)

    def test_missing_name_group(self):
        data = copy.deepcopy(self.data); del data["names"]["widget"]
        self.assert_only(data, "residual group widget is unclassified")

    def test_stale_name_entry(self):
        data = copy.deepcopy(self.data); data["names"]["edge_count"] = data["names"]["widget"]
        self.assert_only(data, "stale entry edge_count")

    def test_members_off_by_one(self):
        data = copy.deepcopy(self.data); data["names"]["widget"]["members"] = ["Cycle.conjectures.X1.x1_widget"]
        self.assert_only(data, "!= the inventory group")

    def test_unknown_class(self):
        data = copy.deepcopy(self.data); data["body_shapes"][INV.sha256("7")]["class"] = "orphan"
        self.assert_only(data, "unknown class 'orphan'")

    def test_short_reason(self):
        data = copy.deepcopy(self.data); data["body_shapes"][INV.sha256("7")]["reason"] = "too short"
        self.assert_only(data, "reason must contain at least 20 characters")

    def test_companion_of_an_unknown_family(self):
        data = copy.deepcopy(self.data); data["names"]["count_sym"]["family"] = "no-such-family"
        self.assert_only(data, "unknown registered family 'no-such-family'")

    def test_companion_without_a_reference_to_its_family(self):
        (self.root / "cycle-theory/theories/conjectures/X2.v").write_text(
            "Definition x2_widget (n : nat) := n.\nLemma x2_count_sym : True.\nDefinition x2_shape := 7.\n")
        self.assert_only(self.data, "x2_count_sym references no source, canonical or API name of edge-count")

    def test_candidate_milestone_not_in_the_table(self):
        data = copy.deepcopy(self.data); data["names"]["widget"]["milestone"] = "someday"
        errors = self.run_check(data)
        self.assertEqual(sorted(e.split(": ")[-1] for e in errors),
                         sorted(["milestone 'someday' is not in the milestones table",
                                 "milestone post-rc-wave is referenced by no entry (stale)"]))

    def test_candidate_reusing_a_registered_id(self):
        data = copy.deepcopy(self.data); data["names"]["widget"]["family_id"] = "edge-count"
        self.assert_only(data, "family_id must be a new lower-case family id")

    def test_candidate_joining_a_registered_family(self):
        data = copy.deepcopy(self.data)
        data["names"]["widget"].update(family_id="edge-count", joins_registered=True)
        self.assertEqual(self.run_check(data), [])
        data["names"]["widget"]["family_id"] = "no-such-family"
        self.assert_only(data, "joins_registered needs family_id to name a registered family")

    def test_mixed_parts_overlap(self):
        data = copy.deepcopy(self.data)
        whole = data["names"]["widget"]
        data["names"]["widget"] = {"parts": [dict(whole, members=["Cycle.conjectures.X1.x1_widget"]), copy.deepcopy(whole)]}
        self.assert_only(data, "parts overlap")

    def test_mixed_union_differs_from_the_group(self):
        data = copy.deepcopy(self.data)
        whole = data["names"]["widget"]
        data["names"]["widget"] = {"parts": [dict(whole, members=["Cycle.conjectures.X1.x1_widget"]),
                                             dict(whole, members=["Cycle.conjectures.X9.x9_widget"])]}
        self.assert_only(data, "the union of the parts != the inventory group")

    def test_body_shape_entry_missing(self):
        data = copy.deepcopy(self.data); data["body_shapes"] = {}
        self.assert_only(data, f"residual group {INV.sha256('7')} is unclassified")

    def test_empty_body_group_is_out_of_scope(self):
        data = copy.deepcopy(self.data)
        data["body_shapes"][INV.sha256("")] = data["body_shapes"][INV.sha256("7")]
        self.assert_only(data, f"stale entry {INV.sha256('')}")

    def test_unreferenced_milestone(self):
        data = copy.deepcopy(self.data)
        data["milestones"]["unused-wave"] = dict(data["milestones"]["post-rc-wave"])
        self.assert_only(data, "milestone unused-wave is referenced by no entry (stale)")

    def test_milestone_without_its_fields(self):
        data = copy.deepcopy(self.data); data["milestones"]["post-rc-wave"] = {"description": "x"}
        self.assert_only(data, "milestone post-rc-wave needs description")


if __name__ == "__main__":
    unittest.main()
