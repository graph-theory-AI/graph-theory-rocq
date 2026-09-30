#!/usr/bin/env python3
"""Mutation canaries for the statement doc-block gate (meta/check_statement_docs.py).

A throwaway repo is built in a temp dir: a fake manifest pair (pointed at by rebinding
`corpus_registry.META`) and one fake package with a `theories/conjectures/` file. Each test
rewrites that file and asserts the gate's verdict, so the canaries are independent of the real
corpus and of the concurrent manifest regeneration.
"""
from __future__ import annotations

import io
import json
import os
from pathlib import Path
import sys
import tempfile
import unittest
import warnings

META = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, META)
import corpus_registry as REG            # noqa: E402
import gate_contracts as CONTRACTS       # noqa: E402
import check_statement_docs as GATE      # noqa: E402

ROW_ID = "arxiv:1611.03196#02"
SITE = "https://graph-theory-ai.github.io/graph-conjectures/arxiv/1611.03196__02/"
REVIEW = ("https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/"
          "arxiv_reviews/1611.03196__02.json")

GOOD_BLOCK = f"""(** Corpus row: {ROW_ID}
    Site: {SITE}
    Review: {REVIEW}
    English statement: (Aharoni et al. 2016, Conjecture 1.14)
      If the edges of a graph are partitioned, some matching meets every class often enough.
    Definitions: [fake_matching M] - pairwise disjoint edges (this file). *)
Definition fake_statement : Prop := True.
"""

EXTERNAL_BLOCK = """(** External theorem: A. Author and B. Author, "A fake duality",
    Journal of Fake Results 28 (1998) 155-161.
    Claim: every fake object of weight two carries a fake flow.
    Not formalized here. *)
Definition external_fake_duality_statement : Prop := True.
"""


class DocGateCanaries(unittest.TestCase):
    def setUp(self):
        # corpus_registry.load_manifest leaves its file handle to the GC; not our business here.
        warnings.simplefilter("ignore", ResourceWarning)
        self.temporary = tempfile.TemporaryDirectory(prefix="statement-docs-canary-")
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.meta = self.root / "meta"
        self.meta.mkdir()
        self.conj = self.root / "fakepkg/theories/conjectures"
        self.conj.mkdir(parents=True)
        self.source = self.conj / "X99.v"
        self.baseline = self.meta / "statement_docs_baseline.json"
        self.write_manifests()
        real_meta = REG.META
        REG.META = str(self.meta)
        self.addCleanup(lambda: setattr(REG, "META", real_meta))
        self.source.write_text(GOOD_BLOCK)

    # ── fixtures ────────────────────────────────────────────────────────────────────────
    def write_manifests(self, alias=False):
        v2 = {"rows": [
            {"row_id": ROW_ID, "slug": "axv_1611_03196_02", "formal_name": "fake_statement",
             "repo": "fakepkg", "alias_of": ("arxiv:1611.03196#01" if alias else None),
             "legs": {"statement": "done"}},
            {"row_id": "erdos:e42", "slug": "erd_42", "formal_name": "erdos_statement",
             "repo": "fakepkg", "alias_of": None, "legs": {"statement": "todo"}},
        ]}
        opg = {"rows": [
            {"slug": "fake_op", "formal_name": "fake_op_statement", "repo": "fakepkg",
             "legs": {"statement": "done"}},
        ]}
        (self.meta / "v2_corpus_manifest.json").write_text(json.dumps(v2))
        (self.meta / "opg_corpus_manifest.json").write_text(json.dumps(opg))

    def gate(self, **kw):
        buf = io.StringIO()
        code = GATE.run(root=str(self.root), baseline_path=str(self.baseline), out=buf, **kw)
        return code, buf.getvalue()

    # ── canaries ────────────────────────────────────────────────────────────────────────
    def test_valid_block_passes(self):
        code, output = self.gate()
        self.assertEqual(code, 0, output)
        self.assertIn("1 target(s), 1 documented", output)

    def test_blank_line_before_definition_is_tolerated(self):
        self.source.write_text(GOOD_BLOCK.replace("*)\nDefinition", "*)\n\nDefinition"))
        code, output = self.gate()
        self.assertEqual(code, 0, output)

    def test_wrong_site_url_fails(self):
        self.source.write_text(GOOD_BLOCK.replace(SITE, SITE.replace("1611", "1612")))
        code, output = self.gate()
        self.assertEqual(code, 1)
        self.assertIn("`Site:` is", output)
        self.assertIn("X99.v:7: fake_statement:", output)

    def test_wrong_formal_name_fails(self):
        self.source.write_text(GOOD_BLOCK.replace("Definition fake_statement",
                                                  "Definition other_statement"))
        code, output = self.gate()
        self.assertEqual(code, 1)
        self.assertIn("not 'other_statement'", output)

    def test_wrong_repo_fails(self):
        (self.meta / "v2_corpus_manifest.json").write_text(json.dumps({"rows": [
            {"row_id": ROW_ID, "formal_name": "fake_statement", "repo": "otherpkg",
             "alias_of": None, "legs": {"statement": "done"}}]}))
        code, output = self.gate()
        self.assertEqual(code, 1)
        self.assertIn("repo 'otherpkg'", output)

    def test_unknown_row_fails(self):
        self.source.write_text(GOOD_BLOCK.replace(ROW_ID, "arxiv:0000.00000#99"))
        code, output = self.gate()
        self.assertEqual(code, 1)
        self.assertIn("unknown corpus row", output)

    def test_missing_definitions_key_fails(self):
        self.source.write_text(
            f"(** Corpus row: {ROW_ID}\n    Site: {SITE}\n    Review: {REVIEW}\n"
            "    English statement: Some matching meets every class often enough. *)\n"
            "Definition fake_statement : Prop := True.\n")
        code, output = self.gate()
        self.assertEqual(code, 1)
        self.assertIn("missing key `Definitions:`", output)

    def test_keys_out_of_order_fails(self):
        self.source.write_text(GOOD_BLOCK.replace(
            f"    Site: {SITE}\n    Review: {REVIEW}\n",
            f"    Review: {REVIEW}\n    Site: {SITE}\n"))
        code, output = self.gate()
        self.assertEqual(code, 1)
        self.assertIn("keys out of order", output)

    def test_orphan_block_passes_for_a_non_corpus_name(self):
        self.source.write_text("(** No corpus row: LLM-proofs variant, not a corpus row. *)\n"
                               "Definition fake_llm_statement : Prop := True.\n")
        code, output = self.gate()
        self.assertEqual(code, 0, output)

    def test_orphan_block_on_a_corpus_name_fails(self):
        self.source.write_text("(** No corpus row: pretending. *)\n"
                               "Definition fake_statement : Prop := True.\n")
        code, output = self.gate()
        self.assertEqual(code, 1)
        self.assertIn("which is a corpus formal_name", output)

    def test_alias_row_is_not_citable(self):
        self.write_manifests(alias=True)
        code, output = self.gate()
        self.assertEqual(code, 1)
        self.assertIn("is an alias of", output)

    def test_row_without_site_page_uses_none(self):
        self.source.write_text(GOOD_BLOCK.replace(ROW_ID, "erdos:e42")
                               .replace(SITE, "none").replace(REVIEW, "none")
                               .replace("Definition fake_statement", "Definition erdos_statement"))
        code, output = self.gate()
        self.assertEqual(code, 0, output)

    def test_row_without_site_page_rejects_a_url(self):
        self.source.write_text(GOOD_BLOCK.replace(ROW_ID, "erdos:e42")
                               .replace("Definition fake_statement", "Definition erdos_statement"))
        code, output = self.gate()
        self.assertEqual(code, 1)
        self.assertIn("expected 'none'", output)

    # ── external-theorem blocks ─────────────────────────────────────────────────────────
    def test_external_theorem_block_passes(self):
        self.source.write_text(EXTERNAL_BLOCK)
        code, output = self.gate()
        self.assertEqual(code, 0, output)
        self.assertIn("1 target(s), 1 documented", output)

    def test_external_theorem_block_without_claim_fails(self):
        self.source.write_text("\n".join(l for l in EXTERNAL_BLOCK.splitlines()
                                         if not l.strip().startswith("Claim:")) + "\n")
        code, output = self.gate()
        self.assertEqual(code, 1)
        self.assertIn("missing key `Claim:`", output)

    def test_external_theorem_block_on_a_non_external_definition_fails(self):
        self.source.write_text(EXTERNAL_BLOCK.replace("external_fake_duality_statement",
                                                      "fake_helper_statement"))
        code, output = self.gate()
        self.assertEqual(code, 1)
        self.assertIn("is not an `external_*_statement` definition", output)

    def test_external_theorem_block_without_a_year_fails(self):
        self.source.write_text(EXTERNAL_BLOCK.replace(
            "Journal of Fake Results 28 (1998) 155-161", "Journal of Fake Results, to appear"))
        code, output = self.gate()
        self.assertEqual(code, 1)
        self.assertIn("must be a citation line", output)

    # ── baseline rollout ────────────────────────────────────────────────────────────────
    def test_baseline_shields_then_must_shrink(self):
        undocumented = "Definition fake_statement : Prop := True.\n"
        self.source.write_text(undocumented)
        code, output = self.gate()
        self.assertEqual(code, 1)
        self.assertIn("missing doc block", output)

        code, output = self.gate(write_baseline=True)
        self.assertEqual(code, 0, output)
        self.assertEqual(json.loads(self.baseline.read_text()),
                         ["fakepkg/theories/conjectures/X99.v#fake_statement"])

        code, output = self.gate()                       # shielded by the baseline
        self.assertEqual(code, 0, output)

        code, output = self.gate(list_baseline=True)     # --list prints what is left
        self.assertIn("fakepkg/theories/conjectures/X99.v#fake_statement", output)

        self.source.write_text(GOOD_BLOCK)               # documented, baseline now stale
        code, output = self.gate()
        self.assertEqual(code, 1)
        self.assertIn("baseline entry is now documented", output)

        self.source.write_text("Definition unrelated_thing : nat := 0.\n")
        code, output = self.gate()                       # target gone, baseline stale
        self.assertEqual(code, 1)
        self.assertIn("baseline entry no longer exists", output)

    def test_missing_baseline_file_is_an_empty_baseline(self):
        self.assertFalse(self.baseline.exists())
        code, output = self.gate()
        self.assertEqual(code, 0, output)

    # ── coverage, warnings, comment spans ───────────────────────────────────────────────
    def test_strict_reverse_coverage_fails_on_an_uncovered_row(self):
        code, output = self.gate()                       # fake_op_statement is never defined
        self.assertEqual(code, 0, output)
        self.assertIn("1 uncovered", output)
        code, output = self.gate(strict=True)
        self.assertEqual(code, 1)
        self.assertIn("uncovered corpus row: opg:fake_op", output)

    def test_duplicate_vocabulary_warning(self):
        self.source.write_text(GOOD_BLOCK + "Definition fake_perfect_matching : Prop := True.\n"
                                            "Definition fake_widget : nat := 0.\n")
        code, output = self.gate(show_warnings=True)
        self.assertEqual(code, 0, output)
        self.assertIn("fake_perfect_matching: warning: local definition duplicates", output)
        self.assertNotIn("fake_widget: warning", output)
        self.assertIn("warnings: total 1", output)

    def test_comment_spans_skip_definitions_inside_comments(self):
        src = "(* outer (* nested *) still *)\nDefinition a : nat := 0.\n"
        self.assertEqual(CONTRACTS.comment_spans(src), [(0, 30)])
        self.assertEqual(CONTRACTS.strip_comments(src)[30:],
                         "\nDefinition a : nat := 0.\n")
        self.source.write_text("(* Definition fake_statement : Prop := True. *)\n"
                               "Definition unrelated : nat := 0.\n")
        code, output = self.gate()
        self.assertEqual(code, 0, output)
        self.assertIn("0 target(s)", output)


if __name__ == "__main__":
    unittest.main(verbosity=2)
