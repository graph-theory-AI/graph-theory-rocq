#!/usr/bin/env python3
"""Build meta/v2_corpus_manifest.json + meta/v2_legs_state.json (milestone X0b; plan §1).

Mechanical, deterministic construction of the v2 corpus rows from the upstream
graph-conjectures clone (located ONLY through corpus_registry.graph_conjectures_dir()):

  S2  data/arxiv_conjectures.json      768 arXiv statement records -> corpus "arxiv"
      data/arxiv_reviews/*.json        per-record status (open/partial/solved/disproved/unclear)
      ARXIV_OPEN_DIFFICULTY_RANKING.md difficulty score/tier/lean (metadata, never scheduling)
      data/arxiv_opg_matches.json      manual_confirmed paper->OPG matches (B1 alias CANDIDATES —
                                       flagged for per-record adjudication, never auto-aliased)
  S5  data/erdos_graph.json            277 erdosproblems.com records -> corpus "erdos"
      data/intersection.json           15 erdos<->OPG crosswalk entries -> alias_of rows
  S7  data/bondy_murty_conjectures.json  38 Bondy–Murty Appendix A records -> corpus "bm"
      data/bondy_murty_reviews/*.json    per-record status (keyed by bm_id, like the arXiv joins)
      data/others_conjectures.json        1 curated record -> corpus "others"
      data/others_reviews/*.json          per-record status (keyed by id)

The arXiv ids are POSITIONAL (`<safe_id>__<nn>` = the nn-th record of that paper in the JSON
array), so the builder asserts review_id == record_key for every arXiv row: a mismatch means the
upstream array was reordered and every downstream id would silently shift.

Every row carries `site_url` / `review_url`, derived from its row_id by corpus_registry.row_urls()
(None for the erdős / derived / studies rows, which have no public per-record page).

Status mapping (exact-type-gate vocabulary, plan §1.4): identity for open/partial/solved/
disproved; `unclear` -> open (safest polarity: forbids committed direct proofs); the raw review
status is preserved in `review_status`. The three ABOULKER_CONJECTURES_RANKED.md errata status
corrections are applied explicitly (ERRATA below) since the review files predate them.

Recovery triage (plan §1.1 B3) is pinned HERE so the counts are reproducible:
  needed  iff statement_text is missing, shorter than SHORT_LEN chars, or matches INTERNAL_RE.

Classifier-owned fields (bucket, topic, formalizability, repo, phase, formal_name, rocq_idiom,
new_primitives, defer_reason, disposition) are initialized to None — the X0b classifier pass and
wave planning fill them; this builder is re-runnable without clobbering them ONLY via the overlay
model (legs live in v2_legs_state.json and are merged in, like the v1 builder). The verification
tuple (source_verified_by/at, implemented_by, verification_note) starts empty; source_locator +
source_hash are prefilled mechanically (they identify the consulted record, not its verification).

Source-text hash pins (plan WP3): a reconciled entry (meta/v2_reconciliation.json) or a wave row
(meta/v2_statement_waves.json) MAY carry an opt-in `source_hash` recording the corpus text the
second reader actually read, plus per-row `source_verified_by`/`source_verified_at` overriding the
file/wave-level values. When the upstream statement is later reworded, the recomputed row hash no
longer matches the pin and the build exits ("source text changed since verification; re-verify")
instead of silently keeping the statement leg `done`.

Usage: python3 meta/build_v2_manifest.py [--check]     (--check: fail on drift vs committed)
"""
import glob
import hashlib
import json
import os
import re
import subprocess
import sys

META = os.path.dirname(os.path.abspath(__file__))
MONO = os.path.dirname(META)
sys.path.insert(0, META)
import corpus_registry as REG

GC = REG.graph_conjectures_dir()

OUT_MANIFEST = REG.manifest_path("v2")
OUT_OVERLAY = REG.overlay_path("v2")

# ── pinned triage constants (plan §1.1 B3; change = manifest change, reviewably) ──
SHORT_LEN = 59
INTERNAL_RE = re.compile(
    r"\b(Theorem|Lemma|Corollary|Conjecture|Question|Problem|Proposition|Claim|Section|Equation)\s+\d")
STATUS_MAP = {"open": "open", "partial": "partial", "solved": "solved",
              "disproved": "disproved", "unclear": "open"}

# ── S3 errata status corrections (ABOULKER_CONJECTURES_RANKED.md, revised draft 2026-05-21) ──
ERRATA = [
    ("2310.04265", "Conjecture 4.3 (Gyárfás-Sumner for Tournaments)", "disproved",
     "Errata (Aboulker ranked list): refuted by Aubian arXiv:2401.07776 — forest backedge graph "
     "with bounded clique number and unbounded dichromatic number."),
    ("1710.06282", "Conjecture 1.4", "solved",
     "Errata (Aboulker ranked list): treewidth version follows from Conjecture 1.2 "
     "(Cames van Batenburg–Huynh–Joret–Raymond) + the grid-minor theorem."),
    ("2310.04265", "Conjecture 5.6", "solved",
     "Errata (Aboulker ranked list): implied by Crew–Fan–Koerts–Moore–Spirkl arXiv:2602.09863 "
     "plus dom(T) <= omega-bar(T)."),
]


# ── arXiv records without a review file upstream (pinned; graph-conjectures@b72c585) ──
# Commit d8f5c43 "Fix arXiv catalog extraction and statements" appended 6 records to
# data/arxiv_conjectures.json without running the per-record status-review pass, so no
# data/arxiv_reviews/<key>.json exists for them. They become rows with status `open` (the safest
# polarity: an open row forbids a committed direct proof) and review_status/review_date null.
# Any OTHER record without a review still stops the build.
UNREVIEWED = {
    "2308.15387__02", "2308.15387__03", "2308.15387__04",
    "2309.04460__01", "2309.04460__02", "2309.04460__03",
}

# ── S7 Bondy–Murty aliases (pinned; one per confirmed `same_conjecture` corpus relation) ──
# data/relations.json edge e213: bm:bm-014 --same_conjecture--> opg:m_n_cycle_covers, verdict
# confirmed / confidence high ("every bridgeless graph has a (5,2)-cycle-cover" IS the five cycle
# double cover conjecture). An alias row owns no statement and no legs (plan §1.4), so the
# five-CDC statement is owed by the OPG row, not by bm-014.
BM_ALIAS = {"bm-014": "opg:m_n_cycle_covers"}


def sha256_file(p):
    return hashlib.sha256(open(p, "rb").read()).hexdigest()


def sha256_text(s):
    return hashlib.sha256(s.encode("utf-8")).hexdigest()


def git_head(path):
    try:
        return subprocess.run(["git", "-C", path, "rev-parse", "HEAD"],
                              capture_output=True, text=True).stdout.strip()
    except OSError:
        return ""


# ── load sources ──
arxiv = json.load(open(os.path.join(GC, "data", "arxiv_conjectures.json")))
erdos = json.load(open(os.path.join(GC, "data", "erdos_graph.json")))
intersection = json.load(open(os.path.join(GC, "data", "intersection.json")))
matches = json.load(open(os.path.join(GC, "data", "arxiv_opg_matches.json")))
bondy_murty = json.load(open(os.path.join(GC, "data", "bondy_murty_conjectures.json")))
others = json.load(open(os.path.join(GC, "data", "others_conjectures.json")))

reviews = {}       # (arxiv_id, conjecture_title) -> review dict
reviews_by_id = {}  # record key (= review file name) -> review dict, titled or not
untitled = {}      # arxiv_id -> [review dicts with null conjecture_title] (rare extractor gap)
for fn in sorted(glob.glob(os.path.join(GC, "data", "arxiv_reviews", "*.json"))):
    rv = json.load(open(fn))
    rv["review_id"] = os.path.basename(fn)[:-5]   # filename is authoritative (key not always present)
    reviews_by_id[rv["review_id"]] = rv
    if not rv.get("conjecture_title"):
        untitled.setdefault(rv.get("arxiv_id"), []).append(rv)
        continue
    key = (rv.get("arxiv_id"), rv.get("conjecture_title"))
    if key in reviews:
        sys.exit(f"duplicate review key {key} ({fn})")
    reviews[key] = rv

# S7 reviews: one file per record, keyed by the record id (the file name is authoritative).
def load_dir_reviews(subdir):
    out = {}
    for fn in sorted(glob.glob(os.path.join(GC, "data", subdir, "*.json"))):
        rv = json.load(open(fn))
        rv["review_id"] = os.path.basename(fn)[:-5]
        if rv["review_id"] in out:
            sys.exit(f"duplicate review id {rv['review_id']!r} in {subdir}")
        out[rv["review_id"]] = rv
    return out


bm_reviews = load_dir_reviews("bondy_murty_reviews")
others_reviews = load_dir_reviews("others_reviews")

# difficulty score/tier/lean from the Complete Ranking table, keyed by review_id
RANK_RE = re.compile(r"^\|\s*\d+\s*\|\s*([\d.]+)\s*\|\s*(\d)\s*\|\s*(\w+)\s*\|\s*\w+\s*\|\s*`?([\w.\-]+__\d+)`?\s*\|")
ranking = {}
for line in open(os.path.join(GC, "ARXIV_OPEN_DIFFICULTY_RANKING.md")):
    m = RANK_RE.match(line)
    if m:
        ranking[m.group(4)] = {"score": float(m.group(1)), "tier": int(m.group(2)), "lean": m.group(3)}

accepted_match = {aid: m["opg_slug"] for aid, m in matches.items() if m.get("manual_confirmed")}

# classification merge (X0b classifier pass): meta/v2_classification.json is the committed
# output of the classifier workflow, keyed by slug -> {bucket, topic, formalizability,
# defer_reason, repo, b1_adjudication, duplicate_of_hint, class_notes}. The builder merges it
# so the manifest stays a pure deterministic function of committed inputs.
CLASS_PATH = os.path.join(META, "v2_classification.json")
CLASS = json.load(open(CLASS_PATH))["rows"] if os.path.exists(CLASS_PATH) else {}
CLASS_FIELDS = ("bucket", "topic", "formalizability", "defer_reason", "repo",
                "b1_adjudication", "duplicate_of_hint", "class_notes")

# overlay merge model (v1 convention): legs live in the overlay; the builder merges them in.
prior_overlay = REG.load_overlay("v2", required=False) or {"entries": {}}
prior_entries = prior_overlay.get("entries", {})

LEGS = ["statement", "grounding", "edges", "correspondence", "audit_page"]


def legs_for(slug):
    e = prior_entries.get(slug, {})
    return {lg: e.get(lg, "todo") for lg in LEGS}


def recovery_of(stmt):
    if not stmt or not stmt.strip():
        return "needed"
    if len(stmt) < SHORT_LEN or INTERNAL_RE.search(stmt):
        return "needed"
    return "none"


rows = []
missing_reviews = []

# ── S2: arXiv rows ──
per_paper_idx = {}
errata_by_key = {(a, t): (st, note) for a, t, st, note in ERRATA}
errata_hit = set()
unreviewed_hit = set()
retitled = []      # (record_key, review title, record title) joined positionally, not by title
for rec in arxiv:
    aid = rec["arxiv_id"]
    nn = per_paper_idx.get(aid, 0)
    per_paper_idx[aid] = nn + 1
    key = (aid, rec["title"])
    rid = f"arxiv:{aid}#{nn:02d}"
    slug = f"axv_{aid.replace('.', '_')}_{nn:02d}"
    record_key = f"{aid.replace('/', '_')}__{nn:02d}"
    rv = reviews.get(key)
    if rv is None:
        # fallback 1: the POSITIONAL key (the review file name), which is what the ids are built
        # from anyway — used when the extractor later renamed a conjecture_title upstream.
        rv = reviews_by_id.get(record_key)
        if rv is not None:
            retitled.append((record_key, rv.get("conjecture_title"), rec["title"]))
    if rv is None:
        # fallback 2: a same-paper review whose conjecture_title the extractor left null —
        # join only when it is unambiguous (exactly one such review for this paper).
        cands = untitled.get(aid, [])
        if len(cands) == 1:
            rv = cands[0]
        elif record_key in UNREVIEWED:
            rv = {}
        else:
            missing_reviews.append(key)
            continue
    raw_status = rv.get("status")
    status = STATUS_MAP.get(raw_status) if raw_status else "open"
    note = None
    if key in errata_by_key:
        status, note = errata_by_key[key][0], errata_by_key[key][1]
        errata_hit.add(key)
    if status is None:
        sys.exit(f"unmapped review status {raw_status!r} for {key}")
    # arXiv record ids are POSITIONAL: the nn-th record of this paper in the array. The review
    # file name encodes the same position, so a disagreement means the upstream array was
    # reordered and every id downstream (slug, row_id, site/review URL) would silently shift.
    if rv and rv.get("review_id") != record_key:
        sys.exit(f"arXiv positional id drift: record {record_key} joined review "
                 f"{rv.get('review_id')!r} (title {rec['title']!r}). data/arxiv_conjectures.json "
                 f"was reordered upstream — re-derive the ids before rebuilding the manifest.")
    if not rv:
        unreviewed_hit.add(record_key)
    frag = (rec.get("statement_text") or "") + "\n" + (rec.get("context_text") or "")
    rank = ranking.get(rv.get("review_id", ""), {})
    rows.append({
        "row_id": rid, "slug": slug, "corpus": "arxiv",
        "record_key": record_key, "kind": rec.get("kind"),
        "title": rec["title"], "arxiv_id": aid, "erdos_id": None,
        "paper_title": rec.get("paper_title"), "paper_authors": rec.get("paper_authors"),
        "published": rec.get("published"), "abs_url": rec.get("abs_url"),
        "attributed_to": rec.get("attributed_to"), "attributed_year": rec.get("attributed_year"),
        "statement_text": rec.get("statement_text"), "context_text": rec.get("context_text"),
        # source_text starts as the extractor's statement (to be REPLACED by our normalized
        # statement at REC/implementation time — plan §2 licensing: store normalized).
        "source_text": rec.get("statement_text") or None,
        "source_locator": f"arXiv:{aid} — {rec['title']}",
        "source_hash": sha256_text(frag),
        "source_excerpt": None, "license": None,
        "implemented_by": None, "source_verified_by": None, "source_verified_at": None,
        "verification_note": None, "status_verified_at": None,
        "status": status,
        "status_semantics": (note or (rv.get("summary") if status != "open" else None)),
        "review_status": raw_status, "review_date": rv.get("reviewed_at"),
        "review_confidence": rv.get("confidence"), "extraction_confidence": rec.get("confidence"),
        "difficulty_score": rank.get("score"), "difficulty_tier": rank.get("tier"),
        "difficulty_lean": rank.get("lean"),
        "recovery": recovery_of(rec.get("statement_text")),
        "b1_candidate": aid in accepted_match,
        "opg_match": accepted_match.get(aid),
        "alias_of": None, "parent": None, "disposition": None,
        # classifier / wave-planning fields (X0b classifier + wave milestones fill these):
        "bucket": None, "topic": None, "formalizability": None, "defer_reason": None,
        "repo": None, "phase": None, "formal_name": None, "rocq_idiom": None,
        "new_primitives": None,
        "legs": legs_for(slug),
    })

if missing_reviews:
    sys.exit(f"{len(missing_reviews)} arXiv records lack a review (join on arxiv_id+title): "
             f"{missing_reviews[:5]}")
if errata_hit != set(errata_by_key):
    sys.exit(f"errata records not found in corpus: {set(errata_by_key) - errata_hit}")
for rk, rv_title, rec_title in retitled:
    sys.stderr.write(f"NOTE: {rk} joined by position, not by title (review {rv_title!r} vs "
                     f"record {rec_title!r} — the extractor renamed it upstream)\n")
if unreviewed_hit != UNREVIEWED:
    sys.exit(f"UNREVIEWED pin is stale: {sorted(UNREVIEWED - unreviewed_hit)} now have a review "
             f"(drop them from the pin and rebuild)")

# ── S5: erdős rows (aliases per intersection.json) ──
erdos_alias = {}   # erdos number -> opg slug
for opg_slug, m in intersection.items():
    erdos_alias[int(m["erdos_id"])] = opg_slug
for rec in sorted(erdos, key=lambda r: r["number"]):
    n = rec["number"]
    rid = f"erdos:{n}"
    slug = f"erdos_{n}"
    alias = erdos_alias.get(n)
    stmt = rec.get("statement", "")
    row = {
        "row_id": rid, "slug": slug, "corpus": "erdos",
        "record_key": str(n), "kind": "Problem",
        "title": f"Erdős problem #{n}", "arxiv_id": None, "erdos_id": n,
        "abs_url": rec.get("url"), "tags": rec.get("tags"), "prize": rec.get("prize"),
        "citation_keys": rec.get("citation_keys"),
        "statement_text": stmt, "context_text": None,
        "source_text": stmt or None,
        "source_locator": rec.get("url"),
        "source_hash": sha256_text(stmt),
        "source_excerpt": None, "license": "GFDL (erdosproblems.com, attribution Thomas Bloom)",
        "implemented_by": None, "source_verified_by": None, "source_verified_at": None,
        "verification_note": None, "status_verified_at": None,
        "status": rec.get("status"),
        "status_semantics": None,
        "review_status": rec.get("status"), "review_date": None,
        "recovery": recovery_of(stmt),
        "b1_candidate": False, "opg_match": alias,
        "alias_of": (f"opg:{alias}" if alias else None),
        "parent": None, "disposition": None,
        "bucket": None, "topic": None, "formalizability": None, "defer_reason": None,
        "repo": None, "phase": None, "formal_name": None, "rocq_idiom": None,
        "new_primitives": None,
        "legs": legs_for(slug) if not alias else {lg: "todo" for lg in LEGS},
    }
    if rec.get("status") not in ("open", "solved"):
        sys.exit(f"unexpected erdos status {rec.get('status')!r} for #{n}")
    rows.append(row)

# ── S7: Bondy–Murty Appendix A rows (corpus "bm") + curated "others" rows ──
# Both corpora mirror the arXiv row key-for-key (so milestone_rows.V2_FIELDS and
# formal_resolutions.validate_entry find every field) and add their own record fields.
BM_LICENSE = ("Bondy–Murty, Théorie des graphes, Appendix A « Problèmes ouverts » (French edition "
              "by F. Havet, 2025, HAL hal-05211979; English: Graph Theory, GTM 244, Springer 2008) "
              "— statements curated in graph-conjectures/data/bondy_murty_conjectures.json.")
OTHERS_LICENSE = ("project (graph-conjectures curated record, data/others_conjectures.json); "
                  "attribution to the original source cited in the record.")

bm_alias_hit = set()
for rec in sorted(bondy_murty, key=lambda r: r["bm_id"]):
    bid = rec["bm_id"]
    rv = bm_reviews.get(bid)
    if rv is None:
        sys.exit(f"Bondy–Murty record {bid} lacks a review "
                 f"(expected {GC}/data/bondy_murty_reviews/{bid}.json)")
    raw_status = rv.get("status", "")
    status = STATUS_MAP.get(raw_status)
    if status is None:
        sys.exit(f"unmapped review status {raw_status!r} for {bid}")
    src = rec.get("source") or {}
    stmt = rec.get("statement_text") or ""
    alias = BM_ALIAS.get(bid)
    if alias:
        bm_alias_hit.add(bid)
    slug = bid.replace("-", "_")
    rows.append({
        "row_id": f"bm:{bid}", "slug": slug, "corpus": "bm",
        "record_key": bid, "kind": rec.get("kind"),
        "title": rec["title"], "arxiv_id": None, "erdos_id": None,
        "abs_url": src.get("url"),
        "attributed_to": rec.get("attributed_to"), "attributed_year": rec.get("attributed_year"),
        "statement_text": stmt, "context_text": rec.get("context_text"),
        "source_text": stmt or None,
        "source_locator": (f"Bondy–Murty Appendix A #{rec['appendix_number']} — {rec['title']} — "
                           f"{src.get('url')} (book p.{src.get('book_page')}, "
                           f"pdf p.{src.get('pdf_page')})"),
        "source_hash": sha256_text(stmt + "\n" + (rec.get("context_text") or "")),
        "source_excerpt": None, "license": BM_LICENSE,
        "implemented_by": None, "source_verified_by": None, "source_verified_at": None,
        "verification_note": None, "status_verified_at": None,
        "status": status,
        "status_semantics": (rv.get("summary") if status != "open" else None),
        "review_status": raw_status, "review_date": rv.get("reviewed_at"),
        "review_confidence": rv.get("confidence"),
        "recovery": recovery_of(stmt),
        "b1_candidate": False, "opg_match": (alias.split(":", 1)[1] if alias else None),
        "alias_of": alias, "parent": None, "disposition": None,
        "bm_id": bid, "appendix_number": rec["appendix_number"], "section": rec["section"],
        "book_refs": rec.get("book_refs"), "coverage": rec.get("coverage"),
        "related": rec.get("related"), "notes": rec.get("notes"),
        "bucket": None, "topic": None, "formalizability": None, "defer_reason": None,
        "repo": None, "phase": None, "formal_name": None, "rocq_idiom": None,
        "new_primitives": None,
        # alias rows own no legs (plan §1.4): all-todo, like the erdős aliases
        "legs": legs_for(slug) if not alias else {lg: "todo" for lg in LEGS},
    })

if bm_alias_hit != set(BM_ALIAS):
    sys.exit(f"BM_ALIAS records not found in corpus: {set(BM_ALIAS) - bm_alias_hit}")

for rec in sorted(others, key=lambda r: r["id"]):
    oid = rec["id"]
    rv = others_reviews.get(oid)
    if rv is None:
        sys.exit(f"others record {oid} lacks a review "
                 f"(expected {GC}/data/others_reviews/{oid}.json)")
    raw_status = rv.get("status", "")
    status = STATUS_MAP.get(raw_status)
    if status is None:
        sys.exit(f"unmapped review status {raw_status!r} for {oid}")
    src = rec.get("source") or {}
    stmt = rec.get("statement_text") or ""
    slug = "oth_" + re.sub(r"[^a-z0-9]+", "_", oid.lower()).strip("_")
    rows.append({
        "row_id": f"others:{oid}", "slug": slug, "corpus": "others",
        "record_key": oid, "kind": rec.get("kind"),
        "title": rec["title"], "arxiv_id": None, "erdos_id": None,
        "abs_url": src.get("url"),
        "attributed_to": rec.get("attributed_to"), "attributed_year": rec.get("attributed_year"),
        "statement_text": stmt, "context_text": rec.get("context_text"),
        "source_text": stmt or None,
        "source_locator": (f"graph-conjectures/data/others_conjectures.json#{oid} — "
                           f"{src.get('url')}"),
        "source_hash": sha256_text(stmt + "\n" + (rec.get("context_text") or "")),
        "source_excerpt": None, "license": OTHERS_LICENSE,
        "implemented_by": None, "source_verified_by": None, "source_verified_at": None,
        "verification_note": None, "status_verified_at": None,
        "status": status,
        "status_semantics": (rv.get("summary") if status != "open" else None),
        "review_status": raw_status, "review_date": rv.get("reviewed_at"),
        "review_confidence": rv.get("confidence"),
        "recovery": recovery_of(stmt),
        "b1_candidate": False, "opg_match": None,
        "alias_of": None, "parent": None, "disposition": None,
        "section": rec.get("section"), "coverage": rec.get("coverage"),
        "related": rec.get("related"), "notes": rec.get("notes"),
        "workstream": rec.get("workstream"),
        "bucket": None, "topic": None, "formalizability": None, "defer_reason": None,
        "repo": None, "phase": None, "formal_name": None, "rocq_idiom": None,
        "new_primitives": None,
        "legs": legs_for(slug),
    })

# ── B6: derived rows (X0c; meta/v2_derived_rows.json, mined from the attack folders) ──
DERIVED_PATH = os.path.join(META, "v2_derived_rows.json")
if os.path.exists(DERIVED_PATH):
    v2_slug_to_rid = {r["slug"]: r["row_id"] for r in rows}
    opg_slugs = {r["slug"] for r in REG.load_manifest("opg")["rows"]}
    for d in json.load(open(DERIVED_PATH))["rows"]:
        parent = d.get("parent")
        if parent in v2_slug_to_rid:
            parent = v2_slug_to_rid[parent]
        elif parent in opg_slugs:
            parent = f"opg:{parent}"
        elif parent:
            sys.stderr.write(f"WARNING: derived row {d['slug']} parent {parent!r} matches no "
                             f"corpus row; kept verbatim\n")
        rows.append({
            "row_id": f"derived:{d['slug']}", "slug": d["slug"], "corpus": "derived",
            "record_key": f"{d['folder']}/{d['hyp_id']}", "kind": "Derived",
            "title": d["title"], "arxiv_id": None, "erdos_id": None,
            "abs_url": None,
            "statement_text": d["statement"], "context_text": None,
            "source_text": d["statement"],
            "source_locator": f"graph-conjectures/problems/{d['folder']}/{d['source_ref']}"
                              f"@{(d.get('ledger_commit') or '')[:12]}",
            "source_hash": sha256_text(d["statement"]),
            "source_excerpt": None,
            "license": "project (graph-conjectures attack-engine artifact, same authorship)",
            "implemented_by": None, "source_verified_by": None, "source_verified_at": None,
            "verification_note": None, "status_verified_at": None,
            "status": d["status"],
            "status_semantics": (d["statement"] if d["status"] == "disproved" else None),
            "review_status": d["status"], "review_date": None,
            "t2_certificate": d["t2_certificate"],
            "recovery": "none",
            "b1_candidate": False, "opg_match": None,
            "alias_of": None, "parent": parent, "disposition": None,
            "bucket": "B6", "topic": None, "formalizability": None, "defer_reason": None,
            "repo": None, "phase": None, "formal_name": None, "rocq_idiom": None,
            "new_primitives": None, "class_notes": d.get("notes"),
            "legs": legs_for(d["slug"]),
        })

# ── S6: studies-slice rows (X0d; meta/v2_studies_rows.json, adjudicated third-party conjectures) ──
STUDIES_PATH = os.path.join(META, "v2_studies_rows.json")
if os.path.exists(STUDIES_PATH):
    known_rids = {r["row_id"] for r in rows} | {f"opg:{r['slug']}"
                                                 for r in REG.load_manifest("opg")["rows"]}
    for s in json.load(open(STUDIES_PATH))["rows"]:
        alias = s.get("alias_of")
        if alias and alias not in known_rids:
            sys.exit(f"studies row {s['slug']} aliases unknown row {alias!r}")
        rows.append({
            "row_id": f"studies:{s['slug']}", "slug": s["slug"], "corpus": "arxiv-studied",
            "record_key": ",".join(s.get("papers", []))[:120], "kind": s.get("kind"),
            "title": s["canonical_name"], "arxiv_id": None, "erdos_id": None, "abs_url": None,
            "statement_text": s.get("statement"), "context_text": None,
            # promoted rows own a statement (source_text); alias/edge-anchor/parked do not.
            "source_text": s.get("statement") if s["disposition"] == "promoted" else None,
            "source_locator": f"graph-conjectures/data/arxiv_extracted (studies-role, "
                              f"{s.get('n_records')} record(s): {','.join(s.get('papers', [])[:3])})",
            "source_hash": sha256_text(s.get("statement") or ""),
            "source_excerpt": None,
            "license": "arXiv-derived (studies-role extraction; per-paper license at REC time)",
            "implemented_by": None, "source_verified_by": None, "source_verified_at": None,
            "verification_note": None, "status_verified_at": None,
            "status": "open",   # studied third-party conjectures; SVER revisits promoted rows
            "status_semantics": None, "review_status": "open", "review_date": None,
            "recovery": "none",
            "b1_candidate": False, "opg_match": None,
            "alias_of": alias, "parent": None,
            "disposition": s["disposition"] if s["disposition"] != "promoted" else None,
            "bucket": "S6-promoted" if s["disposition"] == "promoted" else "S6",
            "topic": s.get("topic"), "formalizability": s.get("formalizability"),
            "defer_reason": (s.get("reason") if s["disposition"] in ("edge-anchor", "parked") else None),
            "repo": s.get("repo"), "phase": None, "formal_name": None, "rocq_idiom": None,
            "new_primitives": None, "class_notes": s.get("reason"),
            "attributed_to": s.get("attributed_to"),
            # alias rows own no legs; the rest get overlay-tracked todo legs
            "legs": ({lg: "todo" for lg in LEGS} if alias else legs_for(s["slug"])),
        })

# merge classifier output (fields the classifier owns; None until it has run)
for r in rows:
    c = CLASS.get(r["slug"], {})
    for f in CLASS_FIELDS:
        r.setdefault(f, None)
        if c.get(f) is not None:
            r[f] = c[f]
    # parked buckets carry their disposition from day one (plan §4: parked rows count as
    # attempted via disposition + note; the note is the classifier's defer_reason)
    if r.get("bucket") in ("B4", "B5") and not r.get("disposition"):
        r["disposition"] = "parked"

# ── X1: directed reconciliation (meta/v2_reconciliation.json) — runs after the classifier so it
# wins on repo/phase: reconciled rows live in digraph-theory regardless of topical area.
# Maps rows onto pre-existing digraph-theory constants verified faithful; assigns
# formal_name/repo/phase/already_formalized + the source-verification tuple, and marks the
# statement leg done in the overlay (with provenance).
RECON_PATH = os.path.join(META, "v2_reconciliation.json")
recon_overlay = {}   # slug -> overlay entry to force (statement=done + provenance)


def check_source_pin(slug, row, entry, where):
    """WP3 hash pin: an opt-in `source_hash` on a reconciled entry / wave row records the corpus
    text the second reader actually read. A later upstream rewording changes the row's recomputed
    hash; the build then stops instead of silently keeping the statement leg `done`."""
    pin = entry.get("source_hash")
    if pin and pin != row["source_hash"]:
        sys.exit(f"{slug}: source text changed since verification "
                 f"({pin[:12]} -> {row['source_hash'][:12]}); re-verify "
                 f"(pin recorded in {where})")
if os.path.exists(RECON_PATH):
    RC = json.load(open(RECON_PATH))
    row_by_slug = {r["slug"]: r for r in rows}
    for slug, rc in RC["reconciled"].items():
        r = row_by_slug.get(slug)
        if r is None:
            sys.exit(f"reconciliation targets unknown v2 slug {slug!r}")
        if r.get("alias_of"):
            sys.exit(f"reconciliation targets alias row {slug!r} (aliases own no statement)")
        check_source_pin(slug, r, rc, "meta/v2_reconciliation.json")
        r["formal_name"] = rc["formal_name"]
        r["repo"] = RC["repo"]
        r["phase"] = RC["phase"]
        r["already_formalized"] = True
        r["reencodings"] = rc.get("reencodings") or None
        r["implemented_by"] = RC["implemented_by"]
        r["source_verified_by"] = rc.get("source_verified_by") or RC["source_verified_by"]
        r["source_verified_at"] = rc.get("source_verified_at") or RC["source_verified_at"]
        r["verification_note"] = (
            f"Reconciled to {rc['defines_file']}:{rc['formal_name']}"
            + (f" (re-encodings: {', '.join(rc['reencodings'])})" if rc.get("reencodings") else "")
            + f". {rc.get('note', '')}")[:600]
        r["source_locator"] = (r.get("source_locator") or "") + \
            f" | Rocq: digraph-theory/theories/conjectures/{rc['defines_file']}#{rc['formal_name']}"
        recon_overlay[slug] = {
            "statement": "done", "grounding": "todo", "edges": "todo",
            "correspondence": "todo", "audit_page": "todo",
            "commit": "x1-reconcile", "package": RC["repo"],
            "note": r["verification_note"],
        }
        for lg in ("grounding", "edges", "correspondence", "audit_page"):   # overlay is the source of truth for the other legs
            if slug in prior_entries:
                recon_overlay[slug][lg] = prior_entries[slug].get(lg, "todo")
        r["legs"] = {lg: recon_overlay[slug][lg] for lg in LEGS}

# ── Statement waves after X1 (meta/v2_statement_waves.json): new authored statement files.
# This keeps milestone assignment reproducible instead of hand-editing the generated manifest.
WAVES_PATH = os.path.join(META, "v2_statement_waves.json")
wave_overlay = {}   # slug -> overlay entry to force (statement=done + provenance)
if os.path.exists(WAVES_PATH):
    WAVES = json.load(open(WAVES_PATH))
    row_by_slug = {r["slug"]: r for r in rows}
    for wave_name, wave in WAVES.get("waves", {}).items():
        phase, repo, defines_file = wave["phase"], wave["repo"], wave["defines_file"]
        if phase != wave_name and not wave_name.startswith(f"{phase}:"):
            sys.exit(f"statement wave key {wave_name!r} disagrees with phase {phase!r}")
        for slug, wr in wave["rows"].items():
            if slug in recon_overlay:
                sys.exit(f"statement wave {phase} targets X1-reconciled slug {slug!r}")
            r = row_by_slug.get(slug)
            if r is None:
                sys.exit(f"statement wave {phase} targets unknown v2 slug {slug!r}")
            if r.get("alias_of"):
                sys.exit(f"statement wave {phase} targets alias row {slug!r} (aliases own no statement)")
            check_source_pin(slug, r, wr, f"meta/v2_statement_waves.json wave {wave_name}")
            if not r.get("source_text") and r.get("statement_text"):
                r["source_text"] = r["statement_text"]
            # A wave row is `done` by default. `state: "partial"` marks an authored, faithful-but-
            # PROXY statement (a documented weakening/approximation of the source under an explicit
            # modelling assumption, e.g. an order-Theta form of an ill-posed exact bound): it keeps
            # its source-verification tuple (verified faithful AS a proxy) and carries a
            # `partial_reason`. `state: "blocked"` marks an authored-but-unfaithful statement awaiting
            # a layer deliberately out of scope: it carries a `blocked_reason`, claims NO source-
            # verification tuple. Both keep formal_name/phase/commit+package provenance so the
            # milestone gate still checks the .v compiles axiom-free.
            state = wr.get("state", "done")
            if state not in ("done", "partial", "blocked"):
                sys.exit(f"statement wave {phase} row {slug!r} has unsupported state {state!r}")
            r["formal_name"] = wr["formal_name"]
            r["repo"] = repo
            r["phase"] = phase
            r["already_formalized"] = False
            r["implemented_by"] = wave["implemented_by"]
            if state == "done":
                r["source_verified_by"] = wr.get("source_verified_by") or wave["source_verified_by"]
                r["source_verified_at"] = wr.get("source_verified_at") or wave["source_verified_at"]
                r["verification_note"] = (
                    f"Authored in {defines_file}:{wr['formal_name']}. {wr.get('note', '')}")[:600]
            elif state == "partial":
                r["source_verified_by"] = wr.get("source_verified_by") or wave["source_verified_by"]
                r["source_verified_at"] = wr.get("source_verified_at") or wave["source_verified_at"]
                r["verification_note"] = (
                    f"PARTIAL (proxy) — {wr.get('partial_reason', wr.get('note', ''))} "
                    f"Authored in {defines_file}:{wr['formal_name']}.")[:600]
            else:  # blocked: no source-verification tuple is claimed
                r["source_verified_by"] = None
                r["source_verified_at"] = None
                r["verification_note"] = (
                    f"BLOCKED — {wr.get('blocked_reason', wr.get('note', ''))}")[:600]
            r["source_locator"] = (r.get("source_locator") or "") + \
                f" | Rocq: {repo}/theories/conjectures/{defines_file}#{wr['formal_name']}"
            wave_overlay[slug] = {
                "statement": state, "grounding": "todo", "edges": "todo",
                "correspondence": "todo", "audit_page": "todo",
                "commit": wave.get("commit", phase.lower()), "package": repo,
                "note": r["verification_note"],
            }
            for lg in ("grounding", "edges", "correspondence", "audit_page"):   # overlay is the source of truth for the other legs
                if slug in prior_entries:
                    wave_overlay[slug][lg] = prior_entries[slug].get(lg, "todo")
            r["legs"] = {lg: wave_overlay[slug][lg] for lg in LEGS}

# public URLs (site page + per-record review file on GitHub) for EVERY row; the statement-doc
# gate reads the same helper, so manifest and doc blocks agree byte for byte. Rows without a
# public page (erdos / derived / studies) get (None, None).
for r in rows:
    r["site_url"], r["review_url"] = REG.row_urls(r["row_id"])

rows.sort(key=lambda r: r["row_id"])
slugs = [r["slug"] for r in rows]
assert len(slugs) == len(set(slugs)), "duplicate slug"
assert len(rows) == len({r["row_id"] for r in rows}), "duplicate row_id"

# ── totals ──
def cnt(key):
    out = {}
    for r in rows:
        out[str(r.get(key))] = out.get(str(r.get(key)), 0) + 1
    return dict(sorted(out.items()))

n_alias = sum(1 for r in rows if r["alias_of"])
totals = {
    "rows": len(rows), "by_corpus": cnt("corpus"), "by_status": cnt("status"),
    "by_kind": cnt("kind"), "by_recovery": cnt("recovery"),
    "alias_rows": n_alias, "b1_candidates": sum(1 for r in rows if r["b1_candidate"]),
    "arxiv_rows": sum(1 for r in rows if r["corpus"] == "arxiv"),
    "erdos_rows": sum(1 for r in rows if r["corpus"] == "erdos"),
    "bm_rows": sum(1 for r in rows if r["corpus"] == "bm"),
    "others_rows": sum(1 for r in rows if r["corpus"] == "others"),
}

manifest = {
    "_README": "v2 corpus manifest (graph-conjectures beyond OPG; plan meta/V2_FULL_CORPUS_PLAN.md). "
               "Built by meta/build_v2_manifest.py from the upstream graph-conjectures clone — "
               "deterministic; regenerate + diff to review changes. Status uses the exact-type-gate "
               "vocabulary (unclear->open, raw kept in review_status; 3 Aboulker errata applied). "
               "b1_candidate rows are OPG-alias CANDIDATES pending per-record adjudication. "
               "source_text currently holds the extractor's statement; REC/implementation replaces it "
               "with our normalized statement (licensing: LICENSE-DATA.md). Corpus tags: arxiv, "
               "erdos, derived, arxiv-studied, bm (Bondy–Murty Appendix A records bm-NNN) and "
               "others (curated data/others_conjectures.json records). site_url/review_url are "
               "derived from row_id by corpus_registry.row_urls() (null for erdos/derived/studies "
               "rows, which have no public per-record page). Legs merge in from "
               "meta/v2_legs_state.json (the source of truth). Classifier fields (bucket/topic/"
               "formalizability/repo/phase/formal_name) come from the hand-maintained "
               "meta/v2_classification.json (edit there, then rebuild — never hand-edit this file) "
               "and from wave planning.",
    "schema_version": 1,
    "provenance": {
        "graph_conjectures_commit": git_head(GC),
        "arxiv_conjectures_sha256": sha256_file(os.path.join(GC, "data", "arxiv_conjectures.json")),
        "erdos_graph_sha256": sha256_file(os.path.join(GC, "data", "erdos_graph.json")),
        "intersection_sha256": sha256_file(os.path.join(GC, "data", "intersection.json")),
        "arxiv_opg_matches_sha256": sha256_file(os.path.join(GC, "data", "arxiv_opg_matches.json")),
        "bondy_murty_conjectures_sha256": sha256_file(
            os.path.join(GC, "data", "bondy_murty_conjectures.json")),
        "others_conjectures_sha256": sha256_file(os.path.join(GC, "data", "others_conjectures.json")),
        "relations_sha256": sha256_file(os.path.join(GC, "data", "relations.json")),
        "graph_conjectures_pin": REG.GRAPH_CONJECTURES_PIN,
        "n_reviews_joined": len(reviews),
        "n_bm_reviews_joined": len(bm_reviews),
    },
    "totals": totals,
    "rows": rows,
}
new = json.dumps(manifest, ensure_ascii=False, indent=1) + "\n"

# overlay init: every NON-ALIAS row gets an entry (alias rows own nothing — plan §1.4)
overlay = {
    "_README": "Per-row leg-state overlay for the v2 corpus (source of truth for legs; the manifest "
               "merges it in at build time). Same conventions as opg_legs_state.json: non-todo legs "
               "require commit+package provenance and a note; statement=done additionally requires "
               "the source-verification tuple on the manifest row (gated by check_milestone.py).",
    "_allowed_states": ["todo", "partial", "done", "blocked"],
    "_legs": LEGS,
    # reconciliation/waves force statement=done + provenance; else preserve prior overlay, else todo
    "entries": {r["slug"]: (recon_overlay.get(r["slug"])
                            or wave_overlay.get(r["slug"])
                            or prior_entries.get(r["slug"], {lg: "todo" for lg in LEGS}))
                for r in rows if not r["alias_of"]},
}
new_overlay = json.dumps(overlay, ensure_ascii=False, indent=1) + "\n"

if "--check" in sys.argv:
    old = open(OUT_MANIFEST).read() if os.path.exists(OUT_MANIFEST) else ""
    old_ov = open(OUT_OVERLAY).read() if os.path.exists(OUT_OVERLAY) else ""
    if old != new or old_ov != new_overlay:
        sys.exit("V2-MANIFEST DRIFT: regenerate with `python3 meta/build_v2_manifest.py`")
    print(f"v2-manifest gate OK: {totals['rows']} rows ({totals['by_corpus']}), no drift")
else:
    open(OUT_MANIFEST, "w").write(new)
    open(OUT_OVERLAY, "w").write(new_overlay)
    print(f"wrote {os.path.relpath(OUT_MANIFEST, MONO)}: {totals['rows']} rows "
          f"| by_corpus {totals['by_corpus']} | by_status {totals['by_status']} "
          f"| recovery {totals['by_recovery']} | aliases {n_alias} | b1 {totals['b1_candidates']}")
