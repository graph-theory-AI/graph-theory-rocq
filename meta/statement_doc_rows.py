#!/usr/bin/env python3
"""Dump, for every conjecture statement of a package, the corpus row it must document.

Companion of meta/check_statement_docs.py for the documentation pass (plan WP4): prints one
JSON object per undocumented target of the package (or of the whole tree), with the fields an
author needs to write the doc block — row id, the two URLs (from corpus_registry.row_urls), the
source statement/context texts, title, attribution and status. Targets that own no corpus row
are listed with "row": null (they need a `(** No corpus row: ... *)` marker).

Usage: python3 meta/statement_doc_rows.py [<package>] [--all]   (--all: documented targets too)
"""
import json
import os
import sys

META = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, META)
import corpus_registry as REG              # noqa: E402
import check_statement_docs as CSD         # noqa: E402


def row_index():
    idx = {}
    v2 = REG.load_manifest("v2")
    for r in v2["rows"]:
        if r.get("formal_name"):
            idx.setdefault(r["formal_name"], []).append(("v2", r["row_id"], r))
    opg = REG.load_manifest("opg")
    for r in opg["rows"]:
        if r.get("formal_name"):
            idx.setdefault(r["formal_name"], []).append(("opg", f"opg:{r['slug']}", r))
    return idx


def main(argv):
    pkgs = [a for a in argv if not a.startswith("--")]
    show_all = "--all" in argv
    idx = row_index()
    pkg_dirs = CSD.packages_with_theories(REG.MONO, pkgs or None)
    targets, _ = CSD.scan(REG.MONO, pkg_dirs, CSD.CorpusIndex())
    for t in targets:
        kind = t.block[0]
        if kind is not None and not show_all:
            continue
        out = {"target": t.key, "file": t.rel, "line": t.line, "name": t.name, "documented": kind is not None}
        rows = idx.get(t.name, [])
        if not rows:
            out["row"] = None
        else:
            corpus, rid, r = rows[0]
            site, review = REG.row_urls(rid)
            out["row"] = {
                "corpus": corpus, "row_id": rid, "site": site or "none", "review": review or "none",
                "repo": r.get("repo"), "status": r.get("status"),
                "title": r.get("title"), "kind": r.get("kind"),
                "paper_title": r.get("paper_title"), "paper_authors": r.get("paper_authors"),
                "attributed_to": r.get("attributed_to"), "attributed_year": r.get("attributed_year"),
                "arxiv_id": r.get("arxiv_id"), "published": r.get("published"),
                "statement_text": r.get("statement_text") or r.get("source_text"),
                "context_text": r.get("context_text"),
                "source_propositions": r.get("source_propositions"),
                "status_semantics": r.get("status_semantics"),
                "verification_note": r.get("verification_note"),
                "legs_statement": (r.get("legs") or {}).get("statement"),
                "other_rows_with_same_formal_name": [x[1] for x in rows[1:]],
            }
        print(json.dumps(out, ensure_ascii=False))


if __name__ == "__main__":
    main(sys.argv[1:])
