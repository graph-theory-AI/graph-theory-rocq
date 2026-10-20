#!/usr/bin/env python3
"""G-5 controls: the static reference inventory of retained aliases, on temporary trees only."""
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import library_alias_retention as AR
import library_inventory as INV
import migration_report as MR

ALIAS = "GTMisc.conjectures.X128.x128_grad_at_most"
LIVE = "Definition x128_grad_at_most (G : sgraph) (r d : nat) := ambient_grad_at_most G r d.\n"
FALLBACK = "ProviderContext fallback at "
EXC = AR.EXCEPTIONS_KEY
REASON = "a reviewed reason of at least twenty characters"
WITH_LEGACY_KEY = {"base": "GTBase", "graph-theory-misc": "GTMisc", "graph-theory-base": "GTBase"}


def fallback_keys(errors):
    return [tuple(e[len(FALLBACK):].split(": ", 1)) for e in errors if e.startswith(FALLBACK)]


class AliasRetention(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory(prefix="library-alias-retention-")
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name).resolve()
        self.files = {}
        self.write("base/_CoqProject", "-Q theories GTBase\ntheories/common.v\n")
        self.write("base/theories/common.v", "Definition ambient_grad_at_most (G : sgraph) (r d : nat) := True.\n")
        self.misc_members = ["theories/conjectures/X128.v", "theories/migration/ambient_grad.v"]
        self.write("graph-theory-misc/theories/conjectures/X128.v",
                   LIVE + "Definition x128_claim_statement : Prop := forall G, x128_grad_at_most G 1 1.\n")
        self.write("graph-theory-misc/theories/migration/ambient_grad.v",
                   "Module X128Legacy.\nDefinition x128_grad_at_most (G : sgraph) (r d : nat) := True.\nEnd X128Legacy.\n"
                   "Lemma x128_grad_at_most_compat G r d :\n  X128Legacy.x128_grad_at_most G r d <-> x128_grad_at_most G r d.\n"
                   "Proof. Admitted.\n")
        # (iii), the own certificate, is the files of the family's compatibility_theorems (Marcol C-3)
        self.registry = {"ambient-grad": {"source_definitions": [ALIAS],
                                          "compatibility_theorems": ["GTMisc.migration.ambient_grad.x128_grad_at_most_compat"]}}
        self.statements = {"x128_claim_statement", "x9_other_statement"}

    def write(self, rel, text):
        path = self.root / rel
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)

    def rows(self, extra_members=(), exceptions=None, namespaces=None):
        self.write("graph-theory-misc/_CoqProject", "-Q theories GTMisc\n-Q ../base/theories GTBase\n"
                   + "".join(m + "\n" for m in (*self.misc_members, *extra_members)))
        namespaces = namespaces or {"base": "GTBase", "graph-theory-misc": "GTMisc"}
        with patch.object(INV, "ROOT", self.root), patch.object(MR, "ROOT", self.root), patch.object(AR, "ROOT", self.root), \
             patch.object(INV, "repository_namespaces", return_value=namespaces), \
             patch.object(INV, "manifest_statement_names", return_value=self.statements), \
             patch.dict("os.environ", {}, clear=False):
            rows, counts, errors = AR.alias_rows(self.registry, exceptions)
        return {row["alias"]: row for row in rows}, counts, errors

    def fallback_fixture(self):
        self.write("base/_CoqProject", "-Q theories GTBase\n-custom-option\ntheories/common.v\n")
        self.write("base/theories/common.v", "Definition ambient_grad_at_most := True.\nDefinition b_use := x128_grad_at_most.\n")

    def test_the_own_certificate_after_its_legacy_module_counts(self):
        rows, counts, errors = self.rows()
        row = rows[ALIAS]
        self.assertEqual(errors, [])
        self.assertEqual(row["own_certificate"]["files"], ["graph-theory-misc/theories/migration/ambient_grad.v"])
        self.assertEqual(row["frozen_references"], 1)  # X128Legacy.x128_grad_at_most is a frozen copy
        self.assertEqual(row["same_file"]["statements"], ["x128_claim_statement"])

    def test_the_alias_does_not_shadow_itself_in_its_own_file(self):
        self.write("graph-theory-misc/theories/conjectures/X128.v",
                   LIVE + "Definition x128_helper G := x128_grad_at_most G 2 2.\n"
                   "Definition x128_claim_statement : Prop := forall G, x128_helper G.\n")
        rows, _, _ = self.rows()
        self.assertEqual(rows[ALIAS]["same_file"]["declarations"], ["x128_helper"])  # the statement reaches it via the helper
        self.assertEqual(rows[ALIAS]["same_file"]["statements"], ["x128_claim_statement"])

    def test_the_own_declaration_is_matched_by_its_module_path(self):
        # a Module-nested namesake BEFORE the live alias must not be taken as the alias (Marcol G5-1)
        self.write("graph-theory-misc/theories/conjectures/X128.v",
                   "Module Old.\nDefinition x128_grad_at_most := 0.\nEnd Old.\n" + LIVE
                   + "Definition x128_helper G := x128_grad_at_most G 2 2.\n")
        rows, _, _ = self.rows()
        self.assertEqual(rows[ALIAS]["same_file"]["declarations"], ["x128_helper"])

    def test_namesakes_in_other_modules_or_at_top_level_do_not_hide_the_alias(self):
        # the Mac 1032Z: alias M.B.x9_name; a namesake in Module A (before or after B) or at top level must not hide B's consumer
        alias = "GTMisc.conjectures.X9.B.x9_name"
        b = "Module B.\nDefinition x9_name := True.\nDefinition actual_consumer := x9_name.\nEnd B.\n"
        layouts = {"A before B": "Module A.\nDefinition x9_name := True.\nEnd A.\n" + b,
                   "A after B": b + "Module A.\nDefinition x9_name := True.\nEnd A.\n",
                   "top-level first": "Definition x9_name := 0.\n" + b}
        self.registry = {"x9-family": {"source_definitions": [alias], "compatibility_theorems": []}}
        for label, text in layouts.items():
            with self.subTest(label):
                self.write("graph-theory-misc/theories/conjectures/X9.v", text)
                rows, _, _ = self.rows(["theories/conjectures/X9.v"])
                self.assertEqual(rows[alias]["same_file"]["declarations"], ["actual_consumer"])
                self.assertNotEqual(AR.suggest_milestones([rows[alias]])[alias], "removable-now")

    def test_a_declaration_site_is_not_a_reference(self):
        rows, _, _ = self.rows()
        own = rows[ALIAS]["own_certificate"]["declarations"]
        self.assertNotIn("graph-theory-misc/theories/migration/ambient_grad.v:x128_grad_at_most", own)
        self.assertEqual(own, ["graph-theory-misc/theories/migration/ambient_grad.v:x128_grad_at_most_compat"])

    def test_a_partially_qualified_reference_counts_despite_a_local_namesake(self):
        self.write("graph-theory-misc/theories/conjectures/X9.v",
                   "Definition x128_grad_at_most := 0.\nDefinition x9_use G := X128.x128_grad_at_most G 1 1.\n")
        rows, _, _ = self.rows(["theories/conjectures/X9.v"])
        self.assertIn("graph-theory-misc/theories/conjectures/X9.v", rows[ALIAS]["cross_file"]["files"])

    def test_shadowing_starts_at_the_end_of_the_declaring_sentence(self):
        self.write("graph-theory-misc/theories/conjectures/X9.v",
                   "Definition x128_grad_at_most G := x128_grad_at_most G 2 2.\nDefinition x9_after := x128_grad_at_most.\n")
        rows, _, _ = self.rows(["theories/conjectures/X9.v"])
        self.assertEqual(rows[ALIAS]["cross_file"]["declarations"],
                         ["graph-theory-misc/theories/conjectures/X9.v:x128_grad_at_most"])

    def test_a_reference_in_a_comment_or_string_does_not_count(self):
        self.write("graph-theory-misc/theories/conjectures/X9.v",
                   '(* x128_grad_at_most *)\nDefinition x9_doc := "x128_grad_at_most".\n')
        rows, _, _ = self.rows(["theories/conjectures/X9.v"])
        self.assertNotIn("graph-theory-misc/theories/conjectures/X9.v", rows[ALIAS]["cross_file"]["files"])

    def test_a_grounding_file_is_a_consumer(self):
        self.write("graph-theory-misc/theories/conjectures/grounding_X128.v",
                   "Lemma x128_grounded : x128_grad_at_most G 0 0.\nProof. Admitted.\n")
        rows, _, _ = self.rows(["theories/conjectures/grounding_X128.v"])
        self.assertIn("graph-theory-misc/theories/conjectures/grounding_X128.v", rows[ALIAS]["cross_file"]["files"])

    def test_an_unlisted_file_counts_textually_and_is_listed(self):
        self.write("graph-theory-misc/theories/conjectures/X77.v", "Definition x77_use := x128_grad_at_most.\n")
        rows, counts, _ = self.rows()
        self.assertIn("graph-theory-misc/theories/conjectures/X77.v", rows[ALIAS]["cross_file"]["unlisted"])
        self.assertEqual(counts["unlisted_files"], 1)

    def test_an_undecided_file_counts_every_occurrence(self):
        self.write("graph-theory-misc/theories/conjectures/X9.v", "Definition x9_use := x128_grad_at_most.\n(* unterminated\n")
        rows, counts, _ = self.rows(["theories/conjectures/X9.v"])
        self.assertIn("graph-theory-misc/theories/conjectures/X9.v", rows[ALIAS]["cross_file"]["undecided"])

    def test_a_cross_file_statement_through_a_same_file_chain(self):
        self.statements.add("x9_other_statement")
        self.write("graph-theory-misc/theories/conjectures/X9.v",
                   "Definition x9_helper G := x128_grad_at_most G 1 1.\nDefinition x9_other_statement : Prop := forall G, x9_helper G.\n")
        rows, _, _ = self.rows(["theories/conjectures/X9.v"])
        self.assertEqual(rows[ALIAS]["cross_file"]["statements"], ["graph-theory-misc/theories/conjectures/X9.v:x9_other_statement"])

    def test_a_transitive_require_export_chain_is_reported(self):
        self.write("graph-theory-misc/theories/conjectures/B.v", "From GTMisc Require Export conjectures.X128.\n")
        self.write("graph-theory-misc/theories/conjectures/A.v",
                   "From GTMisc Require Import conjectures.B.\nDefinition a_use := x128_grad_at_most.\n")
        rows, _, _ = self.rows(["theories/conjectures/A.v", "theories/conjectures/B.v"])
        self.assertEqual(rows[ALIAS]["require_chain"]["graph-theory-misc/theories/conjectures/A.v"], "yes")

    def test_implicit_use_in_a_notation(self):
        self.write("graph-theory-misc/theories/conjectures/X9.v", "Notation GA := (x128_grad_at_most _ 1 1).\n")
        rows, _, _ = self.rows(["theories/conjectures/X9.v"])
        self.assertTrue(rows[ALIAS]["implicit_use"])

    def test_a_provider_fallback_is_an_error(self):
        # (c1), firing without an entry: every observed fallback is an error (the real atlas case before its entry)
        self.fallback_fixture()
        _, counts, errors = self.rows()
        self.assertTrue(errors)
        self.assertEqual(len(fallback_keys(errors)), len(errors))
        self.assertEqual((counts["provider_fallbacks"], counts["accepted_fallbacks"]), (len(errors), []))

    def test_an_accepted_fallback_suppresses_only_its_error(self):
        # (c1), entry + firing: no error; the rows and every count but accepted_fallbacks are those of the run without it,
        # and the fallback is still counted as observed
        self.fallback_fixture()
        rows0, counts0, errors0 = self.rows()
        entries = [{"path": p, "fallback": r, "reason": REASON} for p, r in fallback_keys(errors0)]
        rows1, counts1, errors1 = self.rows(exceptions={"accepted_fallbacks": entries})
        self.assertEqual(errors1, [])
        self.assertEqual(rows1, rows0)
        self.assertEqual(counts1["accepted_fallbacks"], sorted(f"{p}: {r}" for p, r in fallback_keys(errors0)))
        self.assertEqual({k: v for k, v in counts1.items() if k != "accepted_fallbacks"},
                         {k: v for k, v in counts0.items() if k != "accepted_fallbacks"})
        self.assertIn(f"provider_fallbacks {len(entries)}, accepted_fallbacks {len(entries)} (", AR.counts_line(counts1, None))
        # the key is the EXACT (path, reason) pair: another reason at the same path accepts nothing and is stale
        other = [dict(e, fallback=e["fallback"] + " (edited)") for e in entries]
        _, _, errors2 = self.rows(exceptions={"accepted_fallbacks": other})
        self.assertEqual(fallback_keys(errors2), fallback_keys(errors0))
        self.assertEqual(len(errors2), 2 * len(entries))

    def test_an_accepted_fallback_that_no_longer_fires_is_stale(self):
        # (c1), entry + not firing
        entry = {"path": "base/_CoqProject", "fallback": "unsupported _CoqProject option -custom-option", "reason": REASON}
        _, counts, errors = self.rows(exceptions={"accepted_fallbacks": [entry]})
        self.assertEqual(errors, [f"{EXC}: accepted fallback at base/_CoqProject: unsupported _CoqProject option "
                                  "-custom-option no longer fires (stale)"])
        self.assertEqual((counts["provider_fallbacks"], counts["accepted_fallbacks"]), (0, []))

    def test_malformed_exceptions_accept_nothing(self):
        self.fallback_fixture()
        _, _, errors0 = self.rows()
        short = [{"path": p, "fallback": r, "reason": "too short"} for p, r in fallback_keys(errors0)]
        for exceptions in ({"accepted_fallbacks": short}, {"accepted_fallbacks": {}}, {"surprise": []}, []):
            with self.subTest(exceptions):
                _, _, errors = self.rows(exceptions=exceptions)
                self.assertEqual(fallback_keys(errors), fallback_keys(errors0))
                self.assertTrue(any(e.startswith(EXC) for e in errors))

    def test_a_declared_package_without_a_project_is_skipped_and_named(self):
        # (a): the declared key is skipped and named in the summary
        _, counts, errors = self.rows(exceptions={"packages_without_project": {"graph-theory-base": REASON}},
                                      namespaces=WITH_LEGACY_KEY)
        self.assertEqual(errors, [])
        self.assertEqual(counts["packages_without_project"], ["graph-theory-base"])
        self.assertIn("packages_without_project 1 (graph-theory-base)", AR.counts_line(counts, None))

    def test_an_undeclared_package_without_a_project_is_an_error(self):
        # (a): an undeclared missing _CoqProject is an error, and accepting its fallback instead does not hide it
        missing = (f"{EXC}: repository namespace graph-theory-base has no regular _CoqProject and is not declared in "
                   "packages_without_project")
        _, counts, errors = self.rows(namespaces=WITH_LEGACY_KEY)
        self.assertEqual(sorted(errors), sorted([missing, FALLBACK + "graph-theory-base/_CoqProject: missing or non-regular current source"]))
        self.assertEqual(counts["packages_without_project"], [])
        entry = {"path": "graph-theory-base/_CoqProject", "fallback": "missing or non-regular current source", "reason": REASON}
        _, _, errors = self.rows(exceptions={"accepted_fallbacks": [entry]}, namespaces=WITH_LEGACY_KEY)
        self.assertEqual(errors, [missing])

    def test_a_declared_package_with_a_project_is_stale(self):
        # (a): a declared key that has a _CoqProject again (or names no namespace) is stale
        for package, why in (("base", "has a regular _CoqProject (stale)"), ("no-such-package", "is not a repository namespace (stale)")):
            with self.subTest(package):
                _, counts, errors = self.rows(exceptions={"packages_without_project": {package: REASON}})
                self.assertEqual(errors, [f"{EXC}: packages_without_project {package} {why}"])
                self.assertEqual(counts["packages_without_project"], [])

    def test_an_unlisted_providers_alias_counts_what_providercontext_would_rule_out(self):
        # (b): base maps only GTBase, so from base/theories/common.v ProviderContext rules a GTMisc provider out (the
        # control, with the provider listed); with the provider unlisted the reference counts, and the row says so
        unlisted = "GTMisc.conjectures.X15u.x15u_part"
        self.registry["x15u"] = {"source_definitions": [unlisted], "compatibility_theorems": []}
        self.write("graph-theory-misc/theories/conjectures/X15u.v", "Definition x15u_part := True.\n")
        self.write("base/theories/common.v",
                   "Definition ambient_grad_at_most (G : sgraph) (r d : nat) := True.\nDefinition b_use := x15u_part.\n")
        rows, counts, errors = self.rows(["theories/conjectures/X15u.v"])
        self.assertEqual((errors, rows[unlisted]["cross_file"]["files"], rows[unlisted]["provider_unlisted"]), ([], [], False))
        self.assertEqual((counts["provider_unlisted_files"], counts["provider_unlisted_aliases"]), ([], 0))
        rows, counts, errors = self.rows()
        row = rows[unlisted]
        self.assertEqual(errors, [])
        self.assertTrue(row["provider_unlisted"])
        self.assertEqual(row["cross_file"]["files"], ["base/theories/common.v"])
        self.assertEqual((counts["provider_unlisted_files"], counts["provider_unlisted_aliases"]),
                         (["graph-theory-misc/theories/conjectures/X15u.v"], 1))
        self.assertNotEqual(AR.suggest_milestones([row])[unlisted], "removable-now")
        self.assertFalse(rows[ALIAS]["provider_unlisted"])


class Milestones(unittest.TestCase):
    def row(self, **kw):
        row = {"alias": "M.x_a", "family": "f", "same_file": {"declarations": [], "statements": []},
               "cross_file": {"files": [], "declarations": [], "statements": [], "certificates_of": [],
                              "undecided": [], "unlisted": []},
               "own_certificate": {"files": [], "declarations": []}, "implicit_use": False}
        for key, value in kw.items():
            row[key].update(value) if isinstance(value, dict) else row.__setitem__(key, value)
        return row

    def check(self, row, value, table=("post-rc",)):
        return AR.validate_milestones([row], {row["alias"]: value}, dict.fromkeys(table, {}), {"helpers": []})

    def test_vocabulary(self):
        self.assertEqual(self.check(self.row(), "removable-now")[0], [])
        self.assertEqual(self.check(self.row(same_file={"declarations": ["d"]}), "remove-after:post-rc"), ([], {"post-rc"}))
        self.assertIn("not in the vocabulary", self.check(self.row(), "delete-me")[0][0])
        self.assertIn("not in the table", self.check(self.row(same_file={"declarations": ["d"]}), "remove-after:later")[0][0])

    def test_frozen_statement_needs_a_statement(self):
        self.assertIn("without a statement consumer", self.check(self.row(), "retain:frozen-statement")[0][0])
        self.assertEqual(self.check(self.row(same_file={"statements": ["s"]}), "retain:frozen-statement")[0], [])

    def test_a_statement_consumer_allows_only_frozen_retention(self):
        # the Mac 1032Z: an authored removal milestone cannot override a frozen-statement consumer, same-file or cross-file
        for row in (self.row(same_file={"statements": ["s"]}), self.row(cross_file={"statements": ["F.v:s"], "files": ["F.v"]})):
            for value in ("remove-after:post-rc", "removable-now", "retain:certificate"):
                self.assertTrue(any("only retain:frozen-statement is allowed" in e for e in self.check(row, value)[0]), value)
            self.assertEqual(self.check(row, "retain:frozen-statement")[0], [])

    def test_certificate_needs_another_family(self):
        own = self.row(cross_file={"certificates_of": ["f"]})
        self.assertIn("another family", self.check(own, "retain:certificate")[0][0])
        self.assertEqual(self.check(self.row(cross_file={"certificates_of": ["g"]}), "retain:certificate")[0], [])

    def test_removable_now_refuses_consumers_and_implicit_use(self):
        for row in (self.row(same_file={"declarations": ["d"]}), self.row(own_certificate={"files": ["c.v"]}),
                    self.row(implicit_use=True)):
            self.assertIn("removable-now with consumers or implicit use", self.check(row, "removable-now")[0][0])

    def test_every_alias_needs_one_milestone_and_none_is_stale(self):
        errors, _ = AR.validate_milestones([self.row()], {"M.other": "removable-now"}, {}, {"helpers": []})
        self.assertEqual(sorted(e.split(":")[1].strip() for e in errors), ["M.x_a has no milestone", "stale alias M.other"])

    def test_the_inventory_direct_consumers_must_be_in_the_same_file_set(self):
        inventory = {"helpers": [{"qualified_name": "M.x_a", "direct_consumers": ["M.d1"]}]}
        errors, _ = AR.validate_milestones([self.row()], {"M.x_a": "removable-now"}, {}, inventory)
        self.assertTrue(any("lacks the inventory's direct consumers ['M.d1']" in e for e in errors))


if __name__ == "__main__":
    unittest.main()
