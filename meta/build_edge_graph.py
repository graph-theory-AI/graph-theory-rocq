#!/usr/bin/env python3
"""Federation-wide conjecture dependency-graph extractor + gate (G1).

Scans every graph-theory-rocq package's theories/conjectures/*.v for @EDGE annotations, PLUS
the absorbed digraph-theory's @EDGE annotations that lie BETWEEN corpus nodes (its P9 rows are
part of the 227-corpus). Its legacy INTERNAL _implies_ theorems (short non-corpus node names)
are NOT federation edges and are excluded — only its edges, never its theorems.

  (1) explicit structured annotations (the machine-readable record for every edge):
        (*@EDGE from=<A_statement> to=<B_statement> kind=<implies|equiv|refutes|specializes>
                status=<verified|conditional|candidate|refuted-direction> [proof=<thm>]
                [external="<ext1>[,<ext2>]"] cite="<source>" [note="<free text>"] *)
  (2) Qed-closed relative theorems named  <A>_implies_<B> / <A>_equiv_<B> / <A>_refutes_<B> /
      <A>_specializes_<B>, which BACK the verified/conditional edges (such an edge names its
      theorem via proof=<name>).

`conditional` is a PROVED edge whose proof takes one or more CITED CLASSICAL facts as explicit
hypotheses (never an Axiom, never Admitted): it must carry proof= AND external="<names>", each
name being a `Definition external_*_statement` of some theories/conjectures/*.v that is also
registered in meta/external_theorems.json. The emitted record keeps the annotation's free-text
`note` and the resolved `external` list, so the graph says on what a conditional edge depends.

Output: one meta/dependency_graph.json (`--out <path>` to write/compare elsewhere) with a
DETERMINISTIC, sorted edge list.
Gate (`--check`): regenerates byte-identically (fails on drift) AND every VERIFIED/CONDITIONAL
implies/equiv/specializes edge names an existing proof= theorem in its file (right kind, endpoints
consistent with from/to) — a proved edge can't be merely declared, and a stale/mismatched
annotation fails the endpoint check. Two further invariants hold in `--check` AND in a normal run:
  - no vacuous edge: both endpoints of a verified/conditional edge own a `done` statement leg
    (a blocked/partial endpoint is a placeholder, so the "proof" would relate placeholders);
  - status tripwire: a verified/conditional implies/specializes edge may not point at a row the
    corpus calls `disproved` while its source is not (for `equiv`, exactly one disproved endpoint
    is a contradiction) — known upstream contradictions are whitelisted, with a reason and a
    corpus-feedback item, in meta/edge_status_exceptions.json and reported as warnings.
A LEGACY compatibility report for digraph-theory's own graph is included (reported only).
"""
import json, os, re, sys

META = os.path.dirname(os.path.abspath(__file__))
MONO = os.path.dirname(META)
sys.path.insert(0, META)
import corpus_registry as REG

def arg_after(flag, default):
    """Value of a `--flag <value>` command-line option (default when absent)."""
    if flag in sys.argv[:-1]:
        return sys.argv[sys.argv.index(flag) + 1]
    return default

OUT = arg_after("--out", os.path.join(META, "dependency_graph.json"))
EXCEPTIONS = os.path.join(META, "edge_status_exceptions.json")
EXTERNALS = os.path.join(META, "external_theorems.json")
PACKAGES = sorted(d for d in os.listdir(MONO)
                  if os.path.isdir(os.path.join(MONO, d, "theories", "conjectures")) and d != "digraph-theory")

EDGE_RE = re.compile(r"\(\*@EDGE\s+(.*?)\*\)", re.S)
THM_RE = re.compile(r"^\s*(?:Theorem|Lemma|Corollary)\s+([A-Za-z0-9_']+)_(implies|equiv|refutes|specializes)_([A-Za-z0-9_']+)\s*:", re.M)
EXT_DEF_RE = re.compile(r"^\s*Definition\s+(external_[A-Za-z0-9_']*_statement)\s*:", re.M)
KV_RE = re.compile(r'(\w+)=(?:"([^"]*)"|(\S+))')
KINDS = {"implies", "equiv", "refutes", "specializes"}
STATUSES = {"verified", "conditional", "candidate", "refuted-direction"}
# statuses that assert a Qed-closed proof, and the kinds whose proof= theorem is name-checked
PROVED_STATUSES = ("verified", "conditional")
PROVED_KINDS = ("implies", "equiv", "specializes")
# `proved=` was an early, redundant spelling of the status: it is READ BY NOTHING. Reported once
# per file (not per edge — a hundred annotations still carry it) so it can be swept later.
proved_key_files = {}
# every `Definition external_*_statement` of the scanned tree: name -> sorted "<pkg>/<file>" list
external_defs = {}

def parse_kv(s):
    return {m.group(1): (m.group(2) if m.group(2) is not None else m.group(3)) for m in KV_RE.finditer(s)}

def parse_external(s):
    """external="a,b" -> ["a", "b"] (order preserved, blanks dropped)."""
    return [n for n in (p.strip() for p in (s or "").split(",")) if n]

def scan(pkg):
    edges, thms = [], []
    cdir = os.path.join(MONO, pkg, "theories", "conjectures")
    for fn in sorted(os.listdir(cdir)):
        if not fn.endswith(".v"):
            continue
        txt = open(os.path.join(cdir, fn)).read()
        for m in EXT_DEF_RE.finditer(txt):
            external_defs.setdefault(m.group(1), set()).add(f"{pkg}/{fn}")
        for m in EDGE_RE.finditer(txt):
            kv = parse_kv(m.group(1))
            if not (kv.get("from") and kv.get("to")):
                import sys as _s; _s.stderr.write(f"skip malformed @EDGE (no from/to) in {fn} — likely prose\n")
                continue
            status = kv.get("status")
            if status == "verified-literature":  # agents sometimes use the plan's term for a proved edge
                status = "verified"
            if "proved" in kv:
                proved_key_files[f"{pkg}/{fn}"] = proved_key_files.get(f"{pkg}/{fn}", 0) + 1
            edges.append({"from": kv.get("from"), "to": kv.get("to"), "kind": kv.get("kind"),
                          "status": status, "cite": kv.get("cite", ""), "proof": kv.get("proof", ""),
                          "note": kv.get("note", ""), "external": parse_external(kv.get("external")),
                          "package": pkg, "file": fn})
        for m in THM_RE.finditer(txt):
            thms.append({"name": f"{m.group(1)}_{m.group(2)}_{m.group(3)}", "kind": m.group(2), "package": pkg, "file": fn})
    return edges, thms

all_edges, all_thms = [], []
for pkg in PACKAGES:
    e, t = scan(pkg); all_edges += e; all_thms += t

# The absorbed digraph-theory's P9 rows ARE part of the 227 corpus, so its @EDGE annotations
# BETWEEN corpus nodes are federation edges. (Its legacy INTERNAL _implies_ theorems are NOT
# federation edges — they use short non-corpus node names — so we take digraph's EDGES only,
# never its theorems, and keep only edges whose both endpoints are corpus formal_names.)
# The endpoint domain is the UNION over every existing corpus manifest (opg + v2 once X0b lands)
# via corpus_registry — a v2-endpoint edge hosted in a digraph file must survive this filter.
corpus_nodes = REG.all_corpus_nodes()
if os.path.isdir(os.path.join(MONO, "digraph-theory", "theories", "conjectures")):
    dg_edges, dg_thms = scan("digraph-theory")
    # Dropping is EXPECTED for legacy internal digraph edges, but an endpoint that follows the
    # corpus `*_statement` convention and is still unknown is suspicious (typo, or a row that
    # should exist in a manifest) — warn loudly instead of silently truncating the graph.
    kept_proofs = set()
    for e in dg_edges:
        if e["from"] in corpus_nodes and e["to"] in corpus_nodes:
            all_edges.append(e)
            if e.get("proof"):
                kept_proofs.add(e["proof"])
            continue
        odd = [n for n in (e["from"], e["to"]) if n.endswith("_statement") and n not in corpus_nodes]
        if odd:
            sys.stderr.write(f"WARNING: digraph-hosted @EDGE dropped ({e['file']}): "
                             f"{e['from']} -> {e['to']} — corpus-looking non-corpus endpoint(s) "
                             f"{odd} (add the row to a manifest, or rename if internal)\n")
    # Digraph-hosted theorems are taken ONLY when a kept corpus edge names them as its proof
    # (waves X216/X221 onward host corpus implications in digraph-theory); legacy internal
    # `_implies_` theorems stay out of the federation graph.
    all_thms += [t for t in dg_thms if t["name"] in kept_proofs]

# `proved=` is an IGNORED key (the status field alone says whether an edge is proved). One
# aggregated warning, not one per annotation: the tree still carries ~100 of them.
if proved_key_files:
    sys.stderr.write("WARNING: ignored @EDGE key `proved=` on "
                     f"{sum(proved_key_files.values())} annotation(s) in "
                     f"{len(proved_key_files)} file(s) (the `status=` field is the only source of "
                     "truth; drop `proved=`): "
                     + ", ".join(f"{f} x{n}" for f, n in sorted(proved_key_files.items())) + "\n")

# Alias rows own no statements and may never be edge endpoints (plan §1.4): reject any edge
# touching a formal_name that belongs to an alias_of row (should not exist; fail loudly if it does).
ALIASES = REG.alias_formal_names()
for e in all_edges:
    bad = [n for n in (e["from"], e["to"]) if n in ALIASES]
    if bad:
        sys.exit(f"EDGE-GRAPH INVARIANT VIOLATED: edge {e['from']} -> {e['to']} ({e['file']}) uses "
                 f"alias-row endpoint(s) {bad}; point the edge at the canonical row "
                 f"({', '.join(str(ALIASES[n]) for n in bad)}) instead")

def need(c, m):
    if not c:
        raise AssertionError("EDGE-GRAPH INVARIANT VIOLATED: " + m)
for e in all_edges:
    need(e["from"] and e["to"] and e["kind"] and e["status"], f"edge missing field: {e}")
    need(e["kind"] in KINDS, f"bad kind {e['kind']!r} in {e['file']}")
    need(e["status"] in STATUSES, f"bad status {e['status']!r} in {e['file']}")
    # `external=` is the signature of a conditional edge and is meaningless on any other status
    # (a `verified` edge depends on nothing but its own file; a candidate on nothing at all).
    need(bool(e["external"]) == (e["status"] == "conditional"),
         f"edge {e['from']}->{e['to']} ({e['file']}): status={e['status']!r} with "
         f"external={e['external']!r}; external=\"<name>[,<name>]\" is required for "
         f"status=conditional and forbidden otherwise")
    if e["status"] == "conditional":
        need(e.get("proof"), f"conditional edge {e['from']}->{e['to']} ({e['file']}) must carry "
                             "proof=<theorem name> (the theorem taking the external as hypothesis)")

# ── the same edge may not be asserted with two different statuses ──
# (from,to,kind) is the identity of a relation; its status is a claim ABOUT it. Two files claiming
# different statuses for one relation is a contradiction, not a duplicate: one of them is stale.
by_relation = {}
for e in all_edges:
    by_relation.setdefault((e["from"], e["to"], e["kind"]), {}).setdefault(
        e["status"], set()).add(f"{e['package']}/{e['file']}")
for (f, t, k), per_status in sorted(by_relation.items()):
    if len(per_status) > 1:
        detail = "; ".join(f"status={s} in {', '.join(sorted(per_status[s]))}"
                           for s in sorted(per_status))
        need(False, f"edge {f} -> {t} ({k}) is asserted with {len(per_status)} different "
                    f"statuses — {detail}; one annotation is stale, fix or remove it")

# ── external hypotheses of conditional edges ──
# Each external= name must BE a real `Definition external_*_statement` of some
# theories/conjectures/*.v (so the hypothesis is a Prop of the development, never an Axiom) AND be
# registered in meta/external_theorems.json with kind=theorem (so the cited classical fact is
# documented with its citation and claim, and reviewable independently of the Rocq proof).
ext_reg = {}
if any(e["external"] for e in all_edges):
    if not os.path.exists(EXTERNALS):
        sys.exit(f"EDGE-GRAPH INVARIANT VIOLATED: conditional edge(s) declare external= "
                 f"hypotheses but {EXTERNALS} does not exist (register them there)")
    for t in json.load(open(EXTERNALS))["theorems"]:
        if t["name"] in ext_reg:
            sys.exit(f"EDGE-GRAPH INVARIANT VIOLATED: meta/external_theorems.json lists "
                     f"{t['name']!r} twice")
        ext_reg[t["name"]] = t
for e in all_edges:
    eid = f"{e['from']}->{e['to']}:{e['kind']}"
    for name in e["external"]:
        need(name in external_defs,
             f"edge {eid} ({e['file']}) names external={name!r}, which is no "
             f"`Definition {name} : Prop` of any theories/conjectures/*.v")
        reg = ext_reg.get(name)
        need(reg is not None,
             f"edge {eid} ({e['file']}) names external={name!r}, which is not registered in "
             f"meta/external_theorems.json (add name/file/citation/claim/kind/used_by)")
        if reg is None:
            continue
        need(reg.get("kind") == "theorem",
             f"external {name!r} (meta/external_theorems.json) has kind {reg.get('kind')!r}; "
             f"only kind=\"theorem\" may be assumed by a conditional edge (a conjecture assumed as "
             f"a hypothesis is a candidate edge, not a conditional one)")
        if reg.get("file") and reg["file"].split("/theories/conjectures/")[-1] \
                not in {f.split("/")[-1] for f in external_defs[name]}:
            sys.stderr.write(f"WARNING: external {name!r} is registered as living in "
                             f"{reg['file']}, but its Definition was found in "
                             f"{sorted(external_defs[name])}\n")
        if eid not in (reg.get("used_by") or []):
            sys.stderr.write(f"WARNING: external {name!r} is assumed by edge {eid} "
                             f"({e['file']}), which is not listed in its `used_by`\n")

# ── optional corpus-relation citation:  cite="gc:<edge_id>" ──
# An @EDGE may cite the upstream graph-conjectures relation (meta/corpus_relations.json, built by
# build_corpus_relations.py from the clone's data/relations.json) that it formalizes. That file is
# derived data and may be absent (no clone / not yet built): then a gc: cite is free text, exactly
# as before. When it IS present the cited relation must exist and its two endpoints must be this
# annotation's from/to — an upstream renumbering or a repointed relation must break the gate
# rather than leave a Rocq edge carrying someone else's argument. (An `equivalent_to` relation is
# symmetric, so an `equiv` annotation may cite it in either orientation.)
GC_CITE_RE = re.compile(r"^gc:(e\d+)\s*(?:[;,]\s*.*)?$", re.S)
CORPUS_RELATIONS = os.path.join(META, "corpus_relations.json")
gc_rel = ({e["edge_id"]: e for e in json.load(open(CORPUS_RELATIONS))["edges"]}
          if os.path.exists(CORPUS_RELATIONS) else None)
for e in all_edges:
    cite = (e.get("cite") or "").strip()
    if not cite.startswith("gc:"):
        continue
    m = GC_CITE_RE.match(cite)
    if not m or gc_rel is None:
        msg = (f"malformed corpus-relation cite {cite!r} in {e['file']} "
               f"(expected cite=\"gc:eNNN\", optionally followed by ; free text)")
        if not m and gc_rel is not None:
            sys.exit("EDGE-GRAPH INVARIANT VIOLATED: " + msg)
        if not m:   # nothing to check against: report, do not fail (pre-corpus-relations behaviour)
            sys.stderr.write(f"WARNING: {msg}; meta/corpus_relations.json absent, cite unchecked\n")
        continue
    eid = m.group(1)
    rel = gc_rel.get(eid)
    if rel is None:
        sys.exit(f"EDGE-GRAPH INVARIANT VIOLATED: @EDGE in {e['file']} cites corpus relation "
                 f"{eid!r}, which is not in meta/corpus_relations.json (rebuild it, or fix the cite)")
    ends = [(rel["from_formal_name"], rel["to_formal_name"])]
    if e["kind"] == "equiv" and rel["relation"] == "equivalent_to":
        ends.append((rel["to_formal_name"], rel["from_formal_name"]))
    if (e["from"], e["to"]) not in ends:
        sys.exit(f"EDGE-GRAPH INVARIANT VIOLATED: @EDGE {e['from']} -> {e['to']} ({e['file']}) "
                 f"cites corpus relation {eid}, whose endpoints are "
                 f"{rel['from_formal_name']} -> {rel['to_formal_name']} "
                 f"(rows {rel['from_row']} -> {rel['to_row']}); point the edge at the cited "
                 f"relation or cite the right one")
    if rel["relation"] not in ("implies", "equivalent_to"):
        sys.stderr.write(f"WARNING: @EDGE in {e['file']} cites corpus relation {eid} of type "
                         f"{rel['relation']!r}, which asserts no implication\n")

# a verified/conditional implies/equiv/specializes edge must name its backing Theorem
# (proof=<name>), and that EXACT theorem must exist in the edge's file with the right kind AND
# endpoints consistent with from/to (guards against a stale/mismatched annotation that a
# same-kind-in-file check would wave through). A conditional edge's theorem is checked exactly
# like a verified one: it IS Qed-closed, it merely takes its cited externals as hypotheses.
STMT = "_statement"
def core(node):
    return node[:-len(STMT)] if node.endswith(STMT) else node
for e in [e for e in all_edges
          if e["status"] in PROVED_STATUSES and e["kind"] in PROVED_KINDS]:
    pf = e.get("proof", "")
    need(pf, f"{e['status']} {e['kind']} edge {e['from']}->{e['to']} ({e['file']}) must carry proof=<theorem name>")
    need([t for t in all_thms if t["name"] == pf and t["file"] == e["file"] and t["kind"] == e["kind"]],
         f"{e['status']} edge proof theorem '{pf}' (kind {e['kind']}) not found in {e['file']}")
    a, sep, b = pf.partition(f"_{e['kind']}_")
    fc, tc = core(e["from"]), core(e["to"])
    need(sep and a and b and (a in fc or fc in a) and (b in tc or tc in b),
         f"{e['status']} edge proof '{pf}' endpoints inconsistent with {e['from']}->{e['to']}")

# ── no vacuous edge ──
# A proved edge between PLACEHOLDER statements proves nothing: a `blocked`/`partial` statement leg
# means the corpus row's Prop is not (fully) formalised yet, so a relation "proved" about it relates
# stand-ins. Both endpoints of a verified/conditional edge must own a `done` statement leg (opg and
# v2 rows alike record it in legs.statement).
def statement_leg_by_formal_name():
    out = {}
    for cname in REG.existing_corpora():
        for r in REG.load_manifest(cname)["rows"]:
            fn = r.get("formal_name")
            if fn and fn not in out:
                out[fn] = (r.get("legs") or {}).get("statement")
    return out
LEGS = statement_leg_by_formal_name()
for e in [e for e in all_edges if e["status"] in PROVED_STATUSES]:
    for role, node in (("from", e["from"]), ("to", e["to"])):
        leg = LEGS.get(node)
        need(leg == "done",
             f"{e['status']} edge {e['from']}->{e['to']} ({e['file']}): {role} endpoint is a "
             f"placeholder — statement leg of {node} is {leg!r}, not 'done'; finish the statement "
             f"before claiming a proved edge about it")

# ── status tripwire ──
# The corpus records each row's own status. A proved implies/specializes edge whose TARGET the
# corpus calls `disproved` while its SOURCE is not disproved is a contradiction: the source would
# be disproved too (so either the edge, or one of the two corpus statuses, is wrong). For `equiv`
# the two endpoints must agree: exactly one disproved endpoint is the same contradiction.
# Known upstream contradictions live in meta/edge_status_exceptions.json with a reason and the
# corpus-feedback item that reports them, and are printed as warnings instead of failing.
CSTATUS = REG.status_by_formal_name()
exceptions = {}
if os.path.exists(EXCEPTIONS):
    for x in json.load(open(EXCEPTIONS))["exceptions"]:
        exceptions[x["edge"]] = x
tripped, used_exceptions = [], set()
for e in [e for e in all_edges if e["status"] in PROVED_STATUSES and e["kind"] in ("implies", "equiv", "specializes")]:
    fs, ts = CSTATUS.get(e["from"]), CSTATUS.get(e["to"])
    if e["kind"] == "equiv":
        bad = (fs == "disproved") != (ts == "disproved")
        why = (f"an equivalence may not have exactly one `disproved` endpoint "
               f"(from={fs!r}, to={ts!r})")
    else:
        bad = ts == "disproved" and fs != "disproved"
        why = (f"a proved {e['kind']} edge points at a `disproved` row while its source is "
               f"{fs!r} (target={ts!r}): the source would be disproved too")
    if not bad:
        continue
    eid = f"{e['from']}->{e['to']}:{e['kind']}"
    x = exceptions.get(eid)
    if x:
        used_exceptions.add(eid)
        sys.stderr.write(f"WARNING: corpus-status contradiction on edge {eid} ({e['file']}): {why} "
                         f"— whitelisted in meta/edge_status_exceptions.json: {x['reason']} "
                         f"[corpus feedback: {x.get('corpus_feedback_item')}]\n")
    else:
        tripped.append(f"{eid} ({e['package']}/{e['file']}): {why}")
for eid in sorted(set(exceptions) - used_exceptions):
    sys.stderr.write(f"WARNING: stale entry in meta/edge_status_exceptions.json: {eid} no longer "
                     f"trips the status tripwire (the corpus statuses agree again; drop it)\n")
if tripped:
    sys.exit("EDGE-GRAPH STATUS TRIPWIRE: " + "; ".join(tripped)
             + " — fix the edge, or (if the corpus statuses contradict each other upstream) "
               "whitelist it in meta/edge_status_exceptions.json with a reason and a "
               "corpus-feedback item")

# dedup: collapse edges with identical (from,to,kind,status) — the SAME edge re-asserted in
# multiple files (e.g. a cross-milestone refuted edge noted at both endpoints). Keep one, record
# every file that asserts it under `sources` (sorted, deterministic). Of the free-text `note`s the
# LONGEST is kept (the most informative one; the others say the same thing more briefly); the
# `external` list is the first non-empty one and a divergence is reported.
by_id = {}
for e in all_edges:
    k = (e["from"], e["to"], e["kind"], e["status"])
    if k not in by_id:
        by_id[k] = {"from": e["from"], "to": e["to"], "kind": e["kind"], "status": e["status"],
                    "cite": e["cite"], "proof": e.get("proof", ""), "note": e.get("note", ""),
                    "external": list(e["external"]), "sources": set()}
    kept = by_id[k]
    if len(e.get("note", "")) > len(kept["note"]):
        kept["note"] = e["note"]
    if e["external"] and not kept["external"]:
        kept["external"] = list(e["external"])
    elif e["external"] and kept["external"] != e["external"]:
        sys.stderr.write(f"WARNING: edge {e['from']}->{e['to']}:{e['kind']} is asserted with two "
                         f"different external= lists ({kept['external']} and {e['external']}); "
                         f"keeping the first\n")
    kept["sources"].add(f"{e['package']}/{e['file']}")
edges_sorted = sorted(by_id.values(), key=lambda e: (e["from"], e["to"], e["kind"], e["status"]))
for e in edges_sorted:
    e["sources"] = sorted(e["sources"])

# legacy report — counts only, does not define the format
legacy = {}
dt = os.path.join(MONO, "digraph-theory")
if os.path.isdir(dt):
    thm = 0
    cdir = os.path.join(dt, "theories", "conjectures")
    if os.path.isdir(cdir):
        for f in os.listdir(cdir):
            if f.endswith(".v"):
                thm += len(re.findall(r"(?:Theorem|Lemma|Corollary)\s+[A-Za-z0-9_']+_(?:implies|equiv|refutes|specializes|joint)_[A-Za-z0-9_']+",
                                      open(os.path.join(cdir, f)).read()))
    dgj = os.path.join(dt, "docs", "dependency_graph.json")
    committed = len(json.load(open(dgj)).get("edges", [])) if os.path.isfile(dgj) else None
    legacy = {"repo": "digraph-theory (absorbed)", "implies_theorems_in_source": thm,
              "committed_dependency_graph_edges": committed,
              "note": "Legacy digraph-only graph: source _implies_ theorem count vs the committed graph "
                      "differ (theorem-name pattern includes helper lemmas; the old extractor filtered). "
                      "Reconcile within digraph-theory separately; it does NOT define the federation format."}

graph = {
    "_README": "Federation-wide conjecture dependency graph (G1). Edges from (*@EDGE ...*) annotations across "
               "graph-theory-rocq packages + the absorbed digraph-theory's @EDGEs BETWEEN corpus nodes; the "
               "endpoint domain is the union over every corpus manifest in meta/corpus_registry.py (opg + v2), "
               "so cross-corpus edges are first-class. Digraph's legacy internal theorems are not federation "
               "edges (see `legacy`); alias rows may never be endpoints. Verified edges name their backing "
               "theorem via proof=<name>; a `conditional` edge is likewise Qed-closed but takes the cited "
               "classical facts listed in `external` (each a `Definition external_*_statement` registered in "
               "meta/external_theorems.json) as explicit hypotheses. `note` is the annotation's free-text "
               "summary of the argument. Regenerate: `python3 meta/build_edge_graph.py`; gate: `--check` fails "
               "on drift + validates verified/conditional-edge proofs, refuses placeholder endpoints and trips "
               "on corpus-status contradictions (whitelist: meta/edge_status_exceptions.json). "
               "Sorted (from,to,kind,status) for determinism.",
    "packages": PACKAGES,
    "totals": {"edges": len(edges_sorted),
               "by_status": {s: sum(1 for e in edges_sorted if e["status"] == s) for s in sorted(STATUSES)},
               "by_kind": {k: sum(1 for e in edges_sorted if e["kind"] == k) for k in sorted(KINDS)},
               "proved_theorems": len(all_thms)},
    "edges": edges_sorted,
    "legacy": legacy,
}
new = json.dumps(graph, ensure_ascii=False, indent=1) + "\n"

if "--check" in sys.argv:
    old = open(OUT).read() if os.path.exists(OUT) else ""
    if old != new:
        sys.exit(f"EDGE-GRAPH DRIFT: {os.path.relpath(OUT, MONO)} is stale — run "
                 "`python3 meta/build_edge_graph.py`")
    print(f"edge-graph gate OK: {len(edges_sorted)} edges, no drift; "
          f"{graph['totals']['by_status']}; {len(all_thms)} proved theorems")
else:
    open(OUT, "w").write(new)
    print(f"wrote {os.path.relpath(OUT, MONO)}: {len(edges_sorted)} edges {graph['totals']['by_status']}, "
          f"{len(all_thms)} proved theorems | legacy digraph: {legacy.get('implies_theorems_in_source')} thms / "
          f"{legacy.get('committed_dependency_graph_edges')} committed")
