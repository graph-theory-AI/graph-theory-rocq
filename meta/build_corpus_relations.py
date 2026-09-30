#!/usr/bin/env python3
"""Corpus relations as data: graph-conjectures data/relations.json -> meta/corpus_relations.json.

These are AI/literature relations between CORPUS ROWS (the upstream corpus asserts them after an
adversarial review pass); they are explicitly NOT formally verified. They are therefore kept apart
from meta/dependency_graph.json, which only ever contains machine-checkable (*@EDGE ...*)
annotations between Rocq `formal_name`s (verified edges additionally name a Qed theorem).

This builder joins the two worlds without mixing them:
  - every upstream edge is resolved to manifest rows (v2 for arxiv/bm/others, opg for opg:<slug>),
    so we know whether each endpoint has a Rocq statement (`formal_name` + a done statement leg);
  - `both_formalized` marks the edges that a later wave can try to prove in an implications_X2nn.v;
  - `rocq_edge` says whether an (*@EDGE ...*) already mirrors the relation (implies -> kind
    "implies" OR "specializes", since a specialisation is the implication of a special case;
    equivalent_to -> kind "equiv"; same_conjecture / related_only are never mirrored: they feed
    alias decisions resp. documentation only). A `conditional` Rocq edge counts as mirrored like a
    verified one (`rocq_edge` carries the status, so the reader sees which it is).
  - an endpoint row that is an ALIAS of another row owns no statement (plan §1.4), so it is
    resolved to its alias target: `from_formal_name`/`from_leg` (resp. to_) are the TARGET's, and
    `via_alias` names the row id it was resolved through. `from_slug`/`to_slug` keep naming the
    upstream endpoint's own row, so the relation can still be traced back to it.

Endpoint node ids upstream are `opg:<slug>`, `arxiv:<safe_id>__<nn>`, `bm:bm-NNN`, `others:<id>`;
the manifests use `arxiv:<aid>#<nn>` for arXiv rows (joined here on `record_key`) and identify OPG
rows by `slug`. Endpoints whose row does not exist (yet) are kept with null slug/leg and counted in
provenance.n_unmapped_endpoints — the file is always complete w.r.t. upstream, never truncated.

Usage: python3 meta/build_corpus_relations.py [--check] [--out <path>]
       (--check: fail on drift vs the committed file; --out: write/compare elsewhere)
Deterministic: sorted by edge_id, no timestamps; provenance pins the clone commit + file sha256.
"""
import hashlib
import json
import os
import subprocess
import sys

META = os.path.dirname(os.path.abspath(__file__))
MONO = os.path.dirname(META)
sys.path.insert(0, META)
import corpus_registry as REG  # noqa: E402

def arg_after(flag, default):
    """Value of a `--flag <value>` command-line option (default when absent)."""
    if flag in sys.argv[:-1]:
        return sys.argv[sys.argv.index(flag) + 1]
    return default


OUT = arg_after("--out", os.path.join(META, "corpus_relations.json"))
DEP_GRAPH = os.path.join(META, "dependency_graph.json")
SCHEMA_VERSION = 1

# upstream relation -> the @EDGE kinds that may mirror it (relations absent from this map are never
# mirrored in Rocq). `implies` accepts `specializes` too: a specialisation IS an implication, stated
# with the more informative kind when one statement is a special case of the other.
MIRRORED_KIND = {"implies": ("implies", "specializes"), "equivalent_to": ("equiv",)}
RELATIONS = ("implies", "equivalent_to", "same_conjecture", "related_only")
VERDICTS = ("confirmed", "plausible")


def sha256_file(path):
    return hashlib.sha256(open(path, "rb").read()).hexdigest()


def clone_commit(gc_dir):
    """git rev-parse HEAD of the graph-conjectures clone (None if it is not a git checkout)."""
    try:
        out = subprocess.run(["git", "-C", gc_dir, "rev-parse", "HEAD"],
                             capture_output=True, text=True, check=True)
    except (OSError, subprocess.CalledProcessError):
        return None
    return out.stdout.strip() or None


def index_rows():
    """upstream node id -> manifest row, for every row that can carry a statement.

    v2 arXiv rows are keyed by `record_key` (`<safe_id>__<nn>`), bm/others rows by their `row_id`
    (already the upstream shape), OPG rows by `opg:<slug>`. Rows of the arxiv-studied/erdos/derived
    corpora are never relation endpoints (their record_keys are not unique, and the upstream
    relations file does not address them), so they are deliberately not indexed."""
    idx = {}

    def put(node, row):
        if node in idx:
            sys.exit(f"corpus-relations: duplicate manifest row for node {node!r} "
                     f"({idx[node].get('slug')} and {row.get('slug')})")
        idx[node] = row

    v2 = REG.load_manifest("v2", required=False)
    if v2:
        for r in v2["rows"]:
            corpus, rid = r.get("corpus"), r.get("row_id")
            if corpus == "arxiv" and r.get("record_key"):
                put(f"arxiv:{r['record_key']}", r)
            elif corpus in ("bm", "others") and rid:
                put(rid, r)
    opg = REG.load_manifest("opg", required=False)
    if opg:
        for r in opg["rows"]:
            put(f"opg:{r['slug']}", r)
    return idx


def index_by_row_id():
    """manifest row id -> row, over both manifests (OPG rows are keyed `opg:<slug>`).

    Used ONLY to follow `alias_of`, which upstream/manifest-side is written as a ROW ID
    (`opg:<slug>`, `arxiv:<aid>#<nn>`, `erdos:<n>`, ...) — a different shape from the upstream
    relation node ids that index_rows() keys on."""
    idx = {}
    for corpus in ("v2", "opg"):
        m = REG.load_manifest(corpus, required=False)
        for r in (m or {}).get("rows", []):
            rid = r.get("row_id") if corpus == "v2" else (f"opg:{r['slug']}" if r.get("slug") else None)
            if rid:
                idx.setdefault(rid, r)
    return idx


def resolve_alias(node, row, by_row_id):
    """Follow `alias_of` to the row that actually owns the statement.

    Returns (node, row, via) where `via` is the row id resolved THROUGH (None when the endpoint is
    not an alias). An alias row owns no statement (plan §1.4) — it exists only to record that the
    upstream corpus lists the same conjecture twice — so a relation touching it is really a
    relation about its target, and that is the row whose formal_name/statement leg matter. The
    returned node keeps the resolved row's ID shape so leg_of() still tags OPG legs `opg-`.
    An unknown or cyclic alias target leaves the endpoint unresolved (and warns): better a
    relation that is not `both_formalized` than one crediting a statement nobody owns."""
    if row is None or not row.get("alias_of"):
        return node, row, None
    seen, cur_node, cur_row = set(), node, row
    while cur_row.get("alias_of"):
        rid = cur_row["alias_of"]
        if rid in seen:
            sys.exit(f"corpus-relations: alias cycle through {rid!r} (endpoint {node})")
        seen.add(rid)
        nxt = by_row_id.get(rid)
        if nxt is None:
            sys.stderr.write(f"WARNING: corpus-relations: endpoint {node} is an alias of {rid!r}, "
                             f"which is in no manifest; endpoint left unresolved\n")
            return node, row, rid
        cur_node, cur_row = rid, nxt
    return cur_node, cur_row, cur_node


def row_id_of(node, row):
    """Manifest-style row id of an endpoint (falls back to the upstream node id when unresolved —
    bm/others/opg node ids already have the manifest shape; only arXiv ids differ)."""
    if row is None:
        return node
    return row.get("row_id") or f"opg:{row['slug']}"


def leg_of(node, row):
    """Statement-leg state of an endpoint; OPG rows (frozen, statement-complete corpus) are tagged
    `opg-<state>` so a Rocq statement coming from v1 is never confused with a v2 wave result."""
    if row is None:
        return None
    state = (row.get("legs") or {}).get("statement", "todo")
    return f"opg-{state}" if node.startswith("opg:") else state


def leg_done(leg):
    return leg in ("done", "opg-done")


def load_rocq_edges():
    """(from, to, kind) -> '<from>-><to>:<kind>:<status>' for the committed @EDGE graph."""
    if not os.path.exists(DEP_GRAPH):
        return {}
    out = {}
    for e in json.load(open(DEP_GRAPH))["edges"]:
        out.setdefault((e["from"], e["to"], e["kind"]), []).append(
            f"{e['from']}->{e['to']}:{e['kind']}:{e['status']}")
    return {k: sorted(v)[0] for k, v in out.items()}


def build():
    gc_dir = REG.graph_conjectures_dir()
    rel_path = os.path.join(gc_dir, "data", "relations.json")
    if not os.path.exists(rel_path):
        raise SystemExit(f"corpus-relations: {rel_path} not found in the graph-conjectures clone")
    upstream = json.load(open(rel_path))
    idx = index_rows()
    by_row_id = index_by_row_id()
    rocq = load_rocq_edges()

    edges, unmapped = [], 0
    for rel in upstream["relations"]:
        eid = (rel.get("provenance") or {}).get("edge_id")
        if not eid:
            sys.exit(f"corpus-relations: upstream relation without provenance.edge_id: "
                     f"{rel.get('source')} -> {rel.get('target')}")
        src, tgt = rel["source"], rel["target"]
        frow, trow = idx.get(src), idx.get(tgt)
        unmapped += (frow is None) + (trow is None)
        # An alias endpoint owns no statement: resolve it to the row that does (see resolve_alias).
        fnode, fstmt, fvia = resolve_alias(src, frow, by_row_id)
        tnode, tstmt, tvia = resolve_alias(tgt, trow, by_row_id)
        f_name = (fstmt or {}).get("formal_name") or None
        t_name = (tstmt or {}).get("formal_name") or None
        f_leg, t_leg = leg_of(fnode, fstmt), leg_of(tnode, tstmt)
        both = bool(f_name and t_name and leg_done(f_leg) and leg_done(t_leg))
        kinds = MIRRORED_KIND.get(rel["relation"], ())
        rocq_edge = None
        if f_name and t_name:
            for kind in kinds:
                rocq_edge = rocq.get((f_name, t_name, kind))
                if rocq_edge is None and kind == "equiv":   # equivalence is symmetric
                    rocq_edge = rocq.get((t_name, f_name, kind))
                if rocq_edge is not None:
                    break
        edges.append({
            "edge_id": eid,
            "from_row": row_id_of(src, frow), "to_row": row_id_of(tgt, trow),
            "from_node": src, "to_node": tgt,
            "relation": rel["relation"], "verdict": rel["verdict"],
            "confidence": rel.get("confidence"),
            "from_slug": (frow or {}).get("slug"), "to_slug": (trow or {}).get("slug"),
            "from_formal_name": f_name, "to_formal_name": t_name,
            "from_leg": f_leg, "to_leg": t_leg,
            "via_alias": {"from": fvia, "to": tvia},
            "both_formalized": both,
            "rocq_edge": rocq_edge,
            "argument": rel.get("argument", ""),
            "citations": rel.get("citations", []),
        })
    dup = {e["edge_id"] for e in edges}
    if len(dup) != len(edges):
        sys.exit("corpus-relations: upstream edge_ids are not unique")
    edges.sort(key=lambda e: e["edge_id"])

    doc = {
        "_README":
            "Corpus relations between graph-conjectures rows (upstream data/relations.json), "
            "resolved against the committed manifests. These edges are AI/literature claims that "
            "passed an adversarial review upstream; they are NOT machine-checked — the formally "
            "verified graph is meta/dependency_graph.json, built from (*@EDGE ...*) annotations. "
            "`both_formalized` marks implies/equivalent_to edges whose two endpoints both own a "
            "Rocq statement (candidates for an implications_X2nn.v theorem, cited as "
            "cite=\"gc:<edge_id>\"); `rocq_edge` names the @EDGE that already mirrors the relation "
            "(implies->implies or ->specializes, equivalent_to->equiv, with the @EDGE status "
            "appended; same_conjecture feeds alias decisions and related_only is documentation "
            "only, neither is ever mirrored). An endpoint whose row is an alias of another row owns "
            "no statement, so its formal_name/leg are the ALIAS TARGET's and `via_alias` names the "
            "row id resolved through, while from_slug/to_slug keep naming the upstream endpoint's "
            "own row. Endpoints without a "
            "manifest row keep null slug/leg and are counted in provenance.n_unmapped_endpoints. "
            "Regenerate: `python3 meta/build_corpus_relations.py`; gate: `--check` fails on drift. "
            "Sorted by edge_id for determinism.",
        "schema_version": SCHEMA_VERSION,
        "provenance": {
            "graph_conjectures_commit": clone_commit(gc_dir),
            "graph_conjectures_pin": REG.GRAPH_CONJECTURES_PIN,
            "relations_sha256": sha256_file(rel_path),
            "n_edges": len(edges),
            "by_relation": {r: sum(1 for e in edges if e["relation"] == r)
                            for r in sorted(set(RELATIONS) | {e["relation"] for e in edges})},
            "by_verdict": {v: sum(1 for e in edges if e["verdict"] == v)
                           for v in sorted(set(VERDICTS) | {e["verdict"] for e in edges})},
            "n_unmapped_endpoints": unmapped,
            "both_formalized": sum(1 for e in edges if e["both_formalized"]),
        },
        "edges": edges,
    }
    return doc


def main():
    doc = build()
    new = json.dumps(doc, ensure_ascii=False, indent=1) + "\n"
    p = doc["provenance"]
    if "--check" in sys.argv:
        old = open(OUT).read() if os.path.exists(OUT) else ""
        if old != new:
            sys.exit(f"CORPUS-RELATIONS DRIFT: {os.path.relpath(OUT, MONO)} is stale — regenerate "
                     "with `python3 meta/build_corpus_relations.py`")
        print(f"corpus-relations gate OK: {p['n_edges']} edges {p['by_relation']}, "
              f"{p['both_formalized']} both-formalized, {p['n_unmapped_endpoints']} unmapped "
              f"endpoints, no drift")
    else:
        open(OUT, "w").write(new)
        mirrored = sum(1 for e in doc["edges"] if e["rocq_edge"])
        via = sum(1 for e in doc["edges"] if e["via_alias"]["from"] or e["via_alias"]["to"])
        print(f"wrote {os.path.relpath(OUT, MONO)}: {p['n_edges']} edges {p['by_relation']} "
              f"| {p['by_verdict']} | {p['both_formalized']} both-formalized, {mirrored} mirrored "
              f"by a Rocq @EDGE | {p['n_unmapped_endpoints']} unmapped endpoints, {via} with an "
              f"alias-resolved endpoint")


if __name__ == "__main__":
    main()
