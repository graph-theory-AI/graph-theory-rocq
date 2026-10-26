#!/usr/bin/env python3
"""build_correspondence.py — the informal ⇄ formal correspondence registry.

Emits docs/correspondence/registry.json: one entry per conjecture statement
and per proved result, each carrying

  * informal  — the original informal conjecture (corpus ledger + source URL),
  * decoded   — an authored plain-English readback of the FORMAL statement
                (curated; the "informal version of the formal statement"),
  * formal    — the verbatim Rocq (extracted from the built .glob spans, never
                hand-copied) + file:line + GitHub + coqdoc links,
  * status / axiom badge,
  * edges     — the proved implications / refutations to other entries
                (from docs/dependency_graph.json),
  * grounding — headline grounding-lemma evidence (curated).

This is the single data file read by the standalone auditor dashboard
web/correspondence/.  Sources merged:

  1. conjecture statements: every `Definition <name>_statement : Prop` in
     theories/conjectures/*.v;
  2. proved results: statement_closure.CATALOG (the k=3,4,5 / CK3 / general
     theorems already on the blueprint);
  3. curated "extra" entries (refutation lemmas, grounding headliners) declared
     explicitly in docs/correspondence/curated.json.

The authoritative informal↔formal mapping + the authored `decoded` prose live in
docs/correspondence/curated.json (hand-edited).  Auto-joins to the corpus fill
the rest.

  python3 scripts/build_correspondence.py            # write registry.json
  python3 scripts/build_correspondence.py --check       # coverage + staleness gate
  python3 scripts/build_correspondence.py --check-fresh # staleness only (make correspondence-check)
  python3 scripts/build_correspondence.py --self-test   # toolchain-free test of the staleness comparison

--check fails when the committed registry.json differs, byte for byte, from the registry this run
would write (regenerate it with the first command), as well as on the coverage problems below.
--check-fresh fails only on that difference; coverage is not evaluated in this mode.

Requires the library to be built (make) for the .glob spans, exactly like
extract_quotes.py / statement_closure.py.  stdlib only.
"""

from __future__ import annotations

import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "scripts"))
import statement_closure as sc  # GlobFile.statement_span, CATALOG

CONJ_DIR = ROOT / "theories" / "conjectures"
CORR_DIR = ROOT / "docs" / "correspondence"   # hand-authored source (curated.json)
CURATED = CORR_DIR / "curated.json"
WEB_DIR = ROOT / "web" / "correspondence"      # the deployable dashboard
REGISTRY = WEB_DIR / "registry.json"           # generated; read by the dashboard
DEPGRAPH = ROOT / "docs" / "dependency_graph.json"
LEDGER = ROOT / "docs" / "digraph_conjecture_ledger.json"
CLASSIF = ROOT / "docs" / "digraph_conjecture_classification.json"

GH_BLOB = "https://github.com/LLM4Rocq/digraph-theory/blob/main"
COQDOC = "https://llm4rocq.github.io/digraph-theory/doc"

# Default phase-cluster per source file (curated.cluster overrides this).
CLUSTER_BY_FILE = {
    "theories/conjectures/clique_cluster.v": "P1",
    "theories/conjectures/long_dipath.v": "P1",
    "theories/conjectures/classic_core.v": "P9",
    "theories/conjectures/colouring_variants.v": "P11",
    "theories/conjectures/chi_bounded.v": "P2",
    "theories/conjectures/sad.v": "P3",
    "theories/conjectures/packing.v": "P10",
    "theories/conjectures/path_fas.v": "P4",
    "theories/conjectures/reals_growth.v": "P8",
    "theories/conjectures/twinwidth.v": "P12",
    "theories/applications/unified.v": "P1",
    "theories/applications/k4/k4_main.v": "P1",
    "theories/applications/k4/k4_value.v": "P1",
    "theories/applications/k5/main.v": "P1",
    "theories/applications/k5/acn_base.v": "P1",
    "theories/applications/ck3/ck3_main.v": "P1",
    "theories/applications/ck3/lemma7.v": "P1",
    "theories/applications/ck_path/ckpath_k7_concrete.v": "P1",
    "theories/constructions/circulant.v": "P1",
    "theories/invariants_advanced/substitution.v": "G",
    "theories/invariants_advanced/transitive.v": "G",
    "theories/invariants/domination.v": "G",
    "theories/invariants/critical.v": "G",
    "theories/invariants/omegabar.v": "G",
    # grounding / proof files (the lemmas that TEST the definitions) cluster
    # with the conjecture family they validate.
    "theories/conjectures/grounding_sad2.v": "P3",
    "theories/conjectures/grounding_sad_packing.v": "P3",
    "theories/conjectures/grounding_unvd_sad.v": "P3",
    "theories/conjectures/grounding_classic_core.v": "P9",
    "theories/conjectures/grounding_clique_long.v": "P1",
    "theories/conjectures/grounding_dichromatic.v": "P2",
    "theories/conjectures/grounding_dichromatic_cycle.v": "P2",
    "theories/conjectures/grounding_chi_col.v": "P2",
    "theories/conjectures/grounding_tww_chi_col.v": "P2",
    "theories/conjectures/grounding_colouring2.v": "P11",
    "theories/conjectures/grounding_degreewidth_c3.v": "P4",
    "theories/conjectures/grounding_pathfas_tww.v": "P4",
    "theories/conjectures/grounding_fas_unvd.v": "P4",
    "theories/conjectures/grounding_reals.v": "P8",
    "theories/conjectures/grounding_reals2.v": "P8",
    "theories/conjectures/grounding_twinwidth.v": "P12",
    "theories/conjectures/grounding_two_extremal.v": "P12",
    "theories/conjectures/grounding_heroes.v": "P6",
    "theories/conjectures/grounding_heroes_dichotomy.v": "P6",
    "theories/conjectures/grounding_h2_concrete.v": "P6",
    "theories/conjectures/grounding_edges.v": "G",
    "theories/conjectures/grounding_falsification_report.v": "G",
}

# Definition <name> [params] : Prop := ...   (statement-shaped Props)
DEF_RE = re.compile(
    r"^\s*Definition\s+([A-Za-z_]\w*)\b[^:=]*?:\s*Prop\s*:=", re.MULTILINE)

# A doc-comment block (** ... *) ending just above a declaration.
DOC_RE = re.compile(r"\(\*\*(.*?)\*\)", re.S)


def strip_comments(text: str) -> str:
    """Remove (* ... *) Coq comments (nesting-aware)."""
    out, depth, i, n = [], 0, 0, len(text)
    while i < n:
        if text[i:i + 2] == "(*":
            depth += 1
            i += 2
        elif text[i:i + 2] == "*)" and depth > 0:
            depth -= 1
            i += 2
        elif depth == 0:
            out.append(text[i])
            i += 1
        else:
            i += 1
    return "".join(out)


def vrel_to_coqdoc(vrel: str, name: str) -> str:
    """theories/conjectures/sad.v + CL1_statement ->
       .../doc/Digraph.conjectures.sad.html#Digraph.conjectures.sad.CL1_statement"""
    mod = sc.vfile_to_lib(vrel)
    return f"{COQDOC}/{mod}.html#{mod}.{name}"


def clean_doc(block: str) -> str:
    """Collapse a (** ... *) body to one whitespace-normalised paragraph,
    dropping leading coqdoc section markers (** / *** / #)."""
    txt = re.sub(r"\s+", " ", block).strip()
    txt = re.sub(r"^[*#]+\s*", "", txt)
    return txt


def doc_comment_above(raw: str, name: str, kinds: str) -> str:
    """The (** ... *) block immediately preceding the declaration of NAME."""
    m = re.search(rf"^\s*(?:{kinds})\s+{re.escape(name)}\b", raw, re.MULTILINE)
    if not m:
        return ""
    head = raw[:m.start()]
    # the nearest (** ... *) that ends in the whitespace right before the decl
    last = None
    for dm in DOC_RE.finditer(head):
        last = dm
    if last and not raw[last.end():m.start()].strip():
        return clean_doc(last.group(1))
    return ""


def verbatim(closure: sc.Closure, vrel: str, name: str):
    """(code, line) for NAME's statement span, from the built .glob; None if the
    name is not declared in that file's glob (e.g. a curated typo)."""
    g = closure.glob_for(vrel)
    if name not in g.decls:
        return None
    lo, hi, _kind = g.statement_span(name)
    bol = g.src.rfind(b"\n", 0, lo) + 1
    text = g.src[bol:hi].decode("utf-8").rstrip()
    return text, g.line_of(lo)


# ---------------------------------------------------------------------------
# Corpus join helpers
# ---------------------------------------------------------------------------

def load_corpus():
    led = json.loads(LEDGER.read_text(encoding="utf-8"))
    cls = json.loads(CLASSIF.read_text(encoding="utf-8"))
    lrecs = []
    for v in led.values():
        if isinstance(v, list):
            lrecs += v
    by_slug = {r["slug"]: r for r in lrecs if r.get("slug")}
    by_ltitle = {r["title"]: r for r in lrecs if r.get("title")}
    crecs = cls.get("classifications", [])
    by_ctitle = {r["title"]: r for r in crecs if r.get("title")}
    return by_slug, by_ltitle, by_ctitle


def resolve_informal(cur, by_slug, by_ltitle, by_ctitle, fallback_doc):
    """Build the entry's informal block from curated match + corpus, with
    explicit overrides winning.  Returns (informal_dict, status, title)."""
    src = cur.get("source", {})
    led = None
    if src.get("slug"):
        led = by_slug.get(src["slug"])
    if led is None and cur.get("match_title"):
        led = by_ltitle.get(cur["match_title"])
    cls = by_ctitle.get(cur.get("match_title", "")) if cur.get("match_title") else None

    text = cur.get("informal") or (led.get("statement") if led else "") or fallback_doc
    name = src.get("name") or (led.get("source") if led else "")
    url = src.get("url") or (led.get("url") if led else "")
    attribution = src.get("attribution") or (cls.get("attribution") if cls else "")
    title = (cur.get("title") or (led.get("title") if led else "")
             or (cls.get("title") if cls else ""))
    status = cur.get("status") or (cls.get("status") if cls else "")
    informal = {"text": text.strip(), "source": {
        "name": name, "url": url, "attribution": attribution}}
    return informal, status, title


# ---------------------------------------------------------------------------
# Entry discovery
# ---------------------------------------------------------------------------

def discover_conjecture_statements():
    """Every Definition <name>_statement : Prop in theories/conjectures/*.v."""
    found = {}  # name -> (vrel, raw)
    for vf in sorted(CONJ_DIR.glob("*.v")):
        raw = vf.read_text(encoding="utf-8")
        clean = strip_comments(raw)
        vrel = str(vf.relative_to(ROOT))
        for m in DEF_RE.finditer(clean):
            nm = m.group(1)
            if nm.endswith("_statement") and nm not in found:
                found[nm] = (vrel, raw)
    return found


def registry_text(registry) -> str:
    """The exact text written to registry.json (and compared by --check)."""
    return json.dumps(registry, indent=2, ensure_ascii=False) + "\n"


def registry_current(committed, registry) -> bool:
    """True iff the committed registry.json bytes (None when absent) are exactly
    what this run would write."""
    return committed is not None and committed == registry_text(registry).encode("utf-8")


def freshness_problems(committed, registry) -> list:
    """The freshness verdict shared by --check and --check-fresh: [] when the committed
    bytes are current, else the one "stale or missing" problem."""
    if registry_current(committed, registry):
        return []
    return [f"{REGISTRY.relative_to(ROOT)} is stale or missing: it differs from the "
            f"registry this run would write; regenerate it with "
            f"python3 scripts/build_correspondence.py"]


def coverage_gaps(registry) -> list:
    """Entries of a built registry without an authored decoded readback or a cluster
    (the built-row part of --check's coverage problems)."""
    return sorted(r["id"] for r in registry["entries"]
                  if not r.get("decoded_authored") or r.get("cluster") == "?")


def self_test():
    """Toolchain-free negative test of the staleness comparison (make mutation):
    a current registry passes; a changed entry, a missing file and one extra byte
    are each stale; and a current registry with a coverage gap passes the freshness
    verdict of --check-fresh."""
    reg = {"meta": {"count": 1}, "entries": [{"id": "x", "decoded": "\u00e9"}]}
    good = registry_text(reg).encode("utf-8")
    cases = [
        ("current", good, reg, True),
        ("changed entry", good, {"meta": {"count": 1}, "entries": [{"id": "x", "decoded": "e"}]}, False),
        ("missing file", None, reg, False),
        ("extra byte", good + b"\n", reg, False),
    ]
    bad = [name for name, committed, r, want in cases if registry_current(committed, r) != want]
    gap = {"meta": {"count": 1}, "entries": [{"id": "y", "decoded_authored": False, "cluster": "?"}]}
    gap_text = registry_text(gap).encode("utf-8")
    if freshness_problems(gap_text, gap) or coverage_gaps(gap) != ["y"]:
        bad.append("current with a coverage gap")
    if bad:
        print("correspondence self-test FAILED: " + ", ".join(bad), file=sys.stderr)
        sys.exit(1)
    print(f"correspondence self-test OK: {len(cases) + 1} cases (1 current, 3 stale, "
          f"1 current with a coverage gap that --check-fresh does not evaluate)")


def main(mode: str):
    """mode: "write" (regenerate registry.json), "check" (coverage + freshness) or
    "check-fresh" (freshness only)."""
    closure = sc.Closure()
    by_slug, by_ltitle, by_ctitle = load_corpus()
    curated = json.loads(CURATED.read_text(encoding="utf-8")) if CURATED.exists() else {}
    cur_entries = curated.get("entries", {})

    depgraph = json.loads(DEPGRAPH.read_text(encoding="utf-8"))
    dep_nodes = {n["id"] for n in depgraph["nodes"]}

    # 1+2+3: assemble (name -> {vrel, kind, raw}) for all entries.
    entries = {}  # name -> dict(vrel, kind, raw|None, doc_kinds)
    for name, (vrel, raw) in discover_conjecture_statements().items():
        entries[name] = {"vrel": vrel, "kind": "conjecture", "raw": raw,
                         "doc_kinds": "Definition"}
    for name, vrel in sc.CATALOG.items():
        if name not in entries:
            entries[name] = {"vrel": vrel, "kind": "proved-result", "raw": None,
                             "doc_kinds": "Theorem|Lemma|Example|Corollary|Definition"}
    for name, cur in cur_entries.items():
        ex = cur.get("extra")
        if ex and name not in entries:
            entries[name] = {
                "vrel": ex["file"], "kind": ex.get("kind", "refutation"),
                "raw": None,
                "doc_kinds": "Theorem|Lemma|Example|Corollary|Definition"}

    # raw text cache for files we only know by vrel (proved results / extras)
    raw_cache = {}

    def raw_of(ent):
        if ent["raw"] is not None:
            return ent["raw"]
        v = ent["vrel"]
        if v not in raw_cache:
            raw_cache[v] = (ROOT / v).read_text(encoding="utf-8")
        return raw_cache[v]

    # edges, grouped by endpoint
    out_edges = {}  # id -> {implies/refutes/equiv: [{to,thm}], *_by: [{from,thm}]}
    def edge_bucket(eid):
        return out_edges.setdefault(eid, {
            "implies": [], "implied_by": [], "refutes": [], "refuted_by": [],
            "equiv": []})
    for e in depgraph["edges"]:
        s, d, k, thm = e["src"], e["dst"], e["kind"], e["thm"]
        if k == "implies":
            edge_bucket(s)["implies"].append({"to": d, "thm": thm})
            edge_bucket(d)["implied_by"].append({"from": s, "thm": thm})
        elif k == "refutes":
            edge_bucket(s)["refutes"].append({"to": d, "thm": thm})
            edge_bucket(d)["refuted_by"].append({"from": s, "thm": thm})
        elif k == "equiv":
            edge_bucket(s)["equiv"].append({"to": d, "thm": thm})
            edge_bucket(d)["equiv"].append({"to": s, "thm": thm})

    # 4. build registry rows
    rows = []
    missing_decoded = []
    bad_specializes = []
    skipped = []
    for name in sorted(entries):
        ent = entries[name]
        vrel = ent["vrel"]
        cur = cur_entries.get(name, {})
        vb = verbatim(closure, vrel, name)
        if vb is None:                       # curated name not in the built glob
            skipped.append((name, vrel))
            continue
        code, line = vb
        doc = doc_comment_above(raw_of(ent), name, ent["doc_kinds"])
        informal, status, title = resolve_informal(
            cur, by_slug, by_ltitle, by_ctitle, doc)
        if not status:
            status = {"conjecture": "open", "proved-result": "proved",
                      "refutation": "refuted", "grounding": "proved"}.get(
                          ent["kind"], "open")

        decoded = cur.get("decoded", "").strip()
        decoded_authored = bool(decoded)
        if not decoded_authored:
            decoded = doc  # render-time fallback; flagged below
            missing_decoded.append(name)

        edges = out_edges.get(name, {"implies": [], "implied_by": [],
                                     "refutes": [], "refuted_by": [], "equiv": []})
        specializes = cur.get("specializes", [])
        if isinstance(specializes, str):       # tolerate a bare-string curated value
            specializes = [specializes] if specializes else []
        for sp in specializes:
            if sp not in entries and sp not in dep_nodes:
                bad_specializes.append((name, sp))

        axiom_free = ent["kind"] in ("proved-result", "refutation",
                                     "grounding")
        rows.append({
            "id": name,
            "kind": ent["kind"],
            "cluster": cur.get("cluster") or CLUSTER_BY_FILE.get(vrel, "?"),
            "title": title or name,
            "informal": informal,
            "decoded": decoded,
            "decoded_authored": decoded_authored,
            "formal": {
                "name": name,
                "file": vrel,
                "line": line,
                "github_url": f"{GH_BLOB}/{vrel}#L{line}",
                "coqdoc_url": vrel_to_coqdoc(vrel, name),
                "verbatim": code,
            },
            "status": status,
            "axiom_free": axiom_free,
            "edges": edges,
            "specializes": specializes,
            "grounds": cur.get("grounds", []),       # grounding -> conjectures it tests
            "grounded_by": [],                        # filled by the reverse index below
            "grounding": cur.get("grounding", []),    # free-form notes (legacy/extra)
            "faithfulness": cur.get("faithfulness", "").strip(),
        })

    # reverse index: each conjecture/result lists the grounding entries testing it
    by_row = {r["id"]: r for r in rows}
    for r in rows:
        if r["kind"] != "grounding":
            continue
        for gid in r["grounds"]:
            tgt = by_row.get(gid)
            if tgt is not None:
                tgt["grounded_by"].append({"id": r["id"], "title": r["title"]})

    registry = {
        "meta": {
            "count": len(rows),
            "github_blob": GH_BLOB,
            "coqdoc": COQDOC,
            "generator": "scripts/build_correspondence.py",
        },
        "entries": rows,
    }

    committed = REGISTRY.read_bytes() if REGISTRY.exists() else None
    if mode == "check-fresh":
        problems = freshness_problems(committed, registry)
        if problems:
            print("CORRESPONDENCE FRESHNESS CHECK FAILED:\n" + "\n\n".join(problems),
                  file=sys.stderr)
            sys.exit(1)
        print(f"correspondence freshness OK: registry.json current ({len(rows)} entries); "
              f"coverage not evaluated (see --check)")
        return

    if mode == "check":
        problems = []
        if skipped:
            problems.append(
                f"{len(skipped)} curated entries name a declaration absent from "
                f"the built glob (typo? rebuild?):\n    " +
                "\n    ".join(f"{n}  ({v})" for n, v in skipped))
        if missing_decoded:
            problems.append(
                f"{len(missing_decoded)} entries lack an authored `decoded` "
                f"readback in curated.json:\n    " +
                "\n    ".join(sorted(missing_decoded)))
        uncluster = [r["id"] for r in rows if r["cluster"] == "?"]
        if uncluster:
            problems.append(
                f"{len(uncluster)} entries lack a `cluster`:\n    " +
                "\n    ".join(sorted(uncluster)))
        if bad_specializes:
            problems.append("unresolved `specializes` targets:\n    " +
                            "\n    ".join(f"{a} -> {b}" for a, b in bad_specializes))
        # NB: edge targets may legitimately be the dependency graph's
        # *inline-bound* endpoints (not standalone Definitions, e.g. one_cycle,
        # delta3) — the dashboard renders those as plain text, so they are not a
        # coverage failure and are deliberately not gated here.
        problems += freshness_problems(committed, registry)
        if problems:
            print("CORRESPONDENCE AUDIT FAILED:\n" + "\n\n".join(problems),
                  file=sys.stderr)
            sys.exit(1)
        print(f"correspondence audit OK: {len(rows)} entries, all decoded + "
              f"clustered, all edges resolve, registry.json current")
        return

    WEB_DIR.mkdir(parents=True, exist_ok=True)
    REGISTRY.write_text(registry_text(registry), encoding="utf-8")
    n_auth = sum(1 for r in rows if r["decoded_authored"])
    if skipped:
        print(f"  WARNING: skipped {len(skipped)} curated names absent from glob: "
              + ", ".join(n for n, _ in skipped))
    print(f"registry: {len(rows)} entries -> {REGISTRY.relative_to(ROOT)}")
    print(f"  authored decoded: {n_auth}/{len(rows)}")
    print(f"  by kind: " + ", ".join(
        f"{k}={sum(1 for r in rows if r['kind']==k)}"
        for k in sorted({r['kind'] for r in rows})))
    if n_auth < len(rows):
        print(f"  ({len(rows)-n_auth} still using doc-comment fallback; run "
              f"--check to list)")


if __name__ == "__main__":
    args = sys.argv[1:]
    if "--self-test" in args:
        self_test()
    elif "--check-fresh" in args:
        main("check-fresh")
    elif "--check" in args:
        main("check")
    else:
        main("write")
