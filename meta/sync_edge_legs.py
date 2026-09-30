#!/usr/bin/env python3
"""Derive the `edges` leg of every corpus row from the machine-checkable edge evidence.

The `edges` leg used to be hand-set per milestone ("candidate edge recorded", "target of
VERIFIED ..."), which drifts from the two files that actually know: the Rocq dependency graph
(meta/dependency_graph.json — what is *proved*) and the upstream corpus relations
(meta/corpus_relations.json — what *ought* to be proved). This script recomputes the leg from
those two, per non-alias row that owns a formal_name F:

  R(F) = corpus relations with relation ∈ {implies, equivalent_to} that touch F and whose BOTH
         endpoints carry a formal_name (a relation whose partner row is not yet formalized owes
         F nothing — it will start owing once that row is classified).
  V(F) = Rocq edges of kind ∈ {implies, equiv, specializes} and status ∈ {verified, conditional}
         that touch F in either direction. `conditional` = proved relative to a named external
         assumption (meta/build_edge_graph.py's `external` list); it is evidence of work, but it
         never *discharges* a relation.

  done    ⇔ R(F) ∪ V(F) ≠ ∅ and every r ∈ R(F) is DISCHARGED, i.e. either
              - mirrored by a `verified` edge of V(F) (a `conditional` edge does not count), or
              - carries a documented disposition: an entry in the wave registry
                meta/edge_waves.json with state refuted-direction/blocked AND a non-empty
                reason, or a `refuted-direction` @EDGE annotation for the relation's pair in
                meta/dependency_graph.json (its `note`, when present, is the reason).
            When R(F) is empty the evidence must include at least one `verified` edge — a row
            whose only edge work is conditional stays `partial` ("conditional does not count
            for done").
  partial ⇔ V(F) ≠ ∅ and not done.
  todo    otherwise (in particular: rows with no formal_name, and rows whose only edge
            evidence is a `candidate` annotation — a candidate is a plan, not an artifact).

Usage:
    python3 meta/sync_edge_legs.py                  # dry run: per-row changes + summary
    python3 meta/sync_edge_legs.py --check          # exit 1 listing overlay slugs that drifted
    python3 meta/sync_edge_legs.py --write          # apply (only the `edges` field + provenance)
    python3 meta/sync_edge_legs.py --explain <slug> # why one row gets its state
    [--commit <sha>]   provenance commit stamped on a leg leaving todo (default: short HEAD)
    [--corpus opg|v2]  restrict to one corpus

`--write` touches ONLY the `edges` field of an existing entry, plus `package`/`commit` when they
are MISSING and the leg leaves todo (check_milestone requires commit+package for every non-todo
leg; an already-recorded provenance pair belongs to the statement leg and is never overwritten).
The overlay's JSON formatting is reproduced byte for byte: every untouched entry is unchanged.
"""
import argparse
import json
import os
import subprocess
import sys

META = os.path.dirname(os.path.abspath(__file__))
MONO = os.path.dirname(META)
sys.path.insert(0, META)
import corpus_registry as REG

DEPGRAPH = os.path.join(META, "dependency_graph.json")
RELATIONS = os.path.join(META, "corpus_relations.json")
WAVES = os.path.join(META, "edge_waves.json")

EDGE_KINDS = ("implies", "equiv", "specializes")
REL_KINDS = ("implies", "equivalent_to")
EVIDENCE_STATUSES = ("verified", "conditional")     # `conditional` is added by build_edge_graph
DOCUMENTED_STATES = ("refuted-direction", "blocked")
STATES = ("todo", "partial", "done")


# ── inputs ────────────────────────────────────────────────────────────────────────────────────
def load_edges():
    """Rocq edges (list of dicts) — tolerant of a dependency_graph.json without `note`/`external`."""
    if not os.path.exists(DEPGRAPH):
        return []
    return json.load(open(DEPGRAPH, encoding="utf-8")).get("edges", [])


def load_relations():
    """Corpus relations (list of dicts) — tolerant of an absent file / of new fields (via_alias)."""
    if not os.path.exists(RELATIONS):
        return []
    return json.load(open(RELATIONS, encoding="utf-8")).get("edges", [])


def load_waves():
    """Optional wave registry: {"edges": {"<from>-><to>:<kind>": {"state":..., "reason":...}}}."""
    if not os.path.exists(WAVES):
        return {}
    data = json.load(open(WAVES, encoding="utf-8"))
    reg = data.get("edges", data) if isinstance(data, dict) else {}
    return reg if isinstance(reg, dict) else {}


def wave_keys(rel):
    """Registry keys that may carry a disposition for this corpus relation.

    Canonical key is `<from>-><to>:<kind>` with the Rocq kind (implies / equiv); the relation's
    own vocabulary (`equivalent_to`) and — for a symmetric relation — the reverse orientation are
    accepted too, so a hand-written registry entry is not silently ignored."""
    a, b, rel_kind = rel["from_formal_name"], rel["to_formal_name"], rel["relation"]
    kinds = ["equiv", "equivalent_to"] if rel_kind == "equivalent_to" else ["implies"]
    keys = [f"{a}->{b}:{k}" for k in kinds]
    if rel_kind == "equivalent_to":
        keys += [f"{b}->{a}:{k}" for k in kinds]
    return keys


# ── the rule ──────────────────────────────────────────────────────────────────────────────────
class EdgeEvidence:
    """The two evidence files + the wave registry, indexed by formal_name."""

    def __init__(self):
        self.edges = load_edges()
        # An endpoint that is an alias row is resolved upstream to the row owning the statement
        # (build_corpus_relations.py's `via_alias`), so `*_formal_name` already names the TARGET —
        # nothing to do here. Two aliases of one row can, however, resolve to the SAME statement:
        # such a reflexive relation is discharged by definition and must not block a `done` leg.
        self.relations = [r for r in load_relations()
                          if r.get("relation") in REL_KINDS
                          and r.get("from_formal_name") and r.get("to_formal_name")
                          and r["from_formal_name"] != r["to_formal_name"]]
        self.waves = load_waves()
        self.V, self.R = {}, {}
        for e in self.edges:
            if e.get("status") in EVIDENCE_STATUSES and e.get("kind") in EDGE_KINDS:
                for node in (e.get("from"), e.get("to")):
                    self.V.setdefault(node, []).append(e)
        for r in self.relations:
            for node in (r["from_formal_name"], r["to_formal_name"]):
                self.R.setdefault(node, []).append(r)
        # verified Rocq edges, and refuted-direction annotations keyed by unordered pair
        self.verified = [e for e in self.edges if e.get("status") == "verified"]
        self.refuted = {}
        for e in self.edges:
            if e.get("status") == "refuted-direction":
                self.refuted.setdefault(frozenset((e.get("from"), e.get("to"))), []).append(e)

    # -- discharge of one corpus relation --
    def mirror_of(self, rel):
        """A `verified` Rocq edge that proves this relation, or None.

        `A implies B` is mirrored by a verified A->B edge (implies/equiv/specializes) or by a
        verified equivalence between A and B in either orientation; `A equivalent_to B` is
        mirrored by a verified edge between A and B in either orientation."""
        a, b = rel["from_formal_name"], rel["to_formal_name"]
        sym = rel["relation"] == "equivalent_to"
        for e in self.verified:
            f, t, k = e.get("from"), e.get("to"), e.get("kind")
            if (f, t) == (a, b):
                return e
            if (f, t) == (b, a) and (sym or k == "equiv"):
                return e
        return None

    def disposition_of(self, rel):
        """(source, reason) documenting why this relation needs no Rocq edge, or None.

        Two documented sources: the wave registry (state refuted-direction/blocked + non-empty
        reason) and a `refuted-direction` @EDGE annotation for the pair in dependency_graph.json
        (self-documenting; its `note` — a field build_edge_graph is growing — is the reason when
        present)."""
        for key in wave_keys(rel):
            w = self.waves.get(key)
            if isinstance(w, dict) and w.get("state") in DOCUMENTED_STATES:
                reason = (w.get("reason") or "").strip()
                if reason:
                    return (f"edge_waves.json[{key}]={w['state']}", reason)
        pair = frozenset((rel["from_formal_name"], rel["to_formal_name"]))
        for e in self.refuted.get(pair, []):
            note = (e.get("note") or "").strip() or (e.get("cite") or "").strip()
            return (f"dependency_graph refuted-direction {e.get('from')}->{e.get('to')}", note)
        return None

    def undischarged(self, formal_name):
        """Relations of R(F) that are neither mirrored nor documented."""
        out = []
        for rel in self.R.get(formal_name, []):
            if self.mirror_of(rel) is None and self.disposition_of(rel) is None:
                out.append(rel)
        return out

    # -- artifact backing a non-todo `edges` leg (used by check_milestone's check 6) --
    def leg_artifact(self, formal_name):
        """Why a non-todo `edges` leg on this row is backed by a machine-checkable artifact, or
        None. Two shapes, both of which may live OUTSIDE the milestone's own implications file
        (another phase's file, or the `atlas` package):
          - F is an endpoint of a verified/conditional edge of the federation graph;
          - every corpus relation touching F is discharged — mirrored by a verified edge, or
            documented as a non-edge (edge_waves.json refuted-direction/blocked with a reason,
            or a refuted-direction @EDGE for the pair) — and there is at least one such relation.
        """
        if not formal_name:
            return None
        evid = self.V.get(formal_name, [])
        if evid:
            e = evid[0]
            return (f"{len(evid)} verified/conditional edge(s), e.g. {e['from']} {e['kind']} "
                    f"{e['to']} [{e['status']}]")
        rels = self.R.get(formal_name, [])
        if rels and not self.undischarged(formal_name):
            how = []
            for rel in rels[:3]:
                disp = self.disposition_of(rel)
                how.append(f"{rel['edge_id']} {'documented via ' + disp[0] if disp else 'mirrored'}")
            return f"{len(rels)} corpus relation(s) discharged ({'; '.join(how)})"
        return None

    # -- the leg --
    def state_for(self, formal_name):
        """(state, reason) for one formal_name (None/'' -> todo)."""
        if not formal_name:
            return "todo", "row owns no formal_name"
        rels, evid = self.R.get(formal_name, []), self.V.get(formal_name, [])
        if not rels and not evid:
            return "todo", "no corpus relation and no verified/conditional Rocq edge"
        open_rels = self.undischarged(formal_name)
        n_verified = sum(1 for e in evid if e.get("status") == "verified")
        if open_rels:
            reason = (f"{len(open_rels)}/{len(rels)} corpus relation(s) undischarged "
                      f"({', '.join(r['edge_id'] for r in open_rels[:4])})")
            return ("partial" if evid else "todo"), reason
        if not rels and n_verified == 0:
            return "partial", f"{len(evid)} conditional edge(s) only (conditional never means done)"
        return "done", (f"{len(rels)} corpus relation(s) discharged, {n_verified} verified edge(s)"
                        if rels else f"{n_verified} verified edge(s), no corpus relation")


# ── overlay I/O (byte-stable) ─────────────────────────────────────────────────────────────────
def overlay_format(path):
    """(indent, ensure_ascii, trailing) that reproduce this file byte for byte, or None."""
    raw = open(path, encoding="utf-8").read()
    doc = json.loads(raw)
    for indent in (1, 2, 4, None):
        for ensure_ascii in (False, True):
            for trailing in ("\n", ""):
                if json.dumps(doc, indent=indent, ensure_ascii=ensure_ascii) + trailing == raw:
                    return indent, ensure_ascii, trailing
    return None


def write_overlay(path, doc, fmt):
    indent, ensure_ascii, trailing = fmt
    tmp = path + ".tmp"
    with open(tmp, "w", encoding="utf-8") as fh:
        fh.write(json.dumps(doc, indent=indent, ensure_ascii=ensure_ascii) + trailing)
    os.replace(tmp, path)


def head_commit():
    try:
        out = subprocess.run(["git", "rev-parse", "--short", "HEAD"], cwd=MONO,
                             capture_output=True, text=True)
        return out.stdout.strip() or "unknown"
    except OSError:
        return "unknown"


def package_of(evidence, formal_name, row):
    """Package that hosts the edge work for this row: the package prefix of the first source file
    of its first verified/conditional edge (else of the documenting refuted-direction edge, else
    the row's own repo)."""
    cands = list(evidence.V.get(formal_name, []))
    for rel in evidence.R.get(formal_name, []):
        pair = frozenset((rel["from_formal_name"], rel["to_formal_name"]))
        cands += evidence.refuted.get(pair, [])
    for e in cands:
        for src in e.get("sources") or []:
            pkg = src.split("/", 1)[0]
            if pkg in REG.NS:
                return pkg
    return row.get("repo") or ""


# ── plan ──────────────────────────────────────────────────────────────────────────────────────
def plan(corpus, evidence):
    """[(slug, current, new, reason, formal_name, row)] for every overlay-tracked non-alias row."""
    manifest = REG.load_manifest(corpus, required=False)
    overlay = REG.load_overlay(corpus, required=False)
    if manifest is None or overlay is None:
        return []
    entries = overlay.get("entries", {})
    out = []
    for row in manifest["rows"]:
        if row.get("alias_of"):
            continue
        slug = row["slug"]
        entry = entries.get(slug)
        if entry is None:
            continue
        formal_name = row.get("formal_name")
        new, reason = evidence.state_for(formal_name)
        out.append((slug, entry.get("edges", "todo"), new, reason, formal_name, row))
    return out


def summarize(rows):
    counts = {s: 0 for s in STATES}
    for _, _, new, _, _, _ in rows:
        counts[new] = counts.get(new, 0) + 1
    return counts


def main():
    ap = argparse.ArgumentParser(description="derive the `edges` leg from the edge evidence")
    ap.add_argument("--write", action="store_true", help="apply the derived legs to the overlays")
    ap.add_argument("--check", action="store_true", help="exit 1 listing slugs that drifted")
    ap.add_argument("--explain", metavar="SLUG", help="explain one row's derived state")
    ap.add_argument("--commit", metavar="SHA", help="provenance commit for legs leaving todo")
    ap.add_argument("--corpus", choices=sorted(REG.CORPORA), help="restrict to one corpus")
    args = ap.parse_args()
    if args.write and args.check:
        sys.exit("sync_edge_legs: --write and --check are exclusive")

    evidence = EdgeEvidence()
    corpora = [args.corpus] if args.corpus else [c for c in REG.CORPORA if c in REG.existing_corpora()]
    plans = {c: plan(c, evidence) for c in corpora}

    # ── --explain ──
    if args.explain:
        for corpus, rows in plans.items():
            for slug, cur, new, reason, formal_name, _row in rows:
                if slug != args.explain:
                    continue
                print(f"{corpus} row {slug}: formal_name={formal_name}")
                print(f"  overlay edges = {cur!r}; derived = {new!r}  ({reason})")
                rels = evidence.R.get(formal_name, [])
                print(f"  R({formal_name}) = {len(rels)} corpus relation(s)")
                for r in rels:
                    mirror = evidence.mirror_of(r)
                    disp = evidence.disposition_of(r)
                    if mirror:
                        how = f"MIRRORED by verified {mirror['from']} {mirror['kind']} {mirror['to']}"
                    elif disp:
                        how = f"DOCUMENTED via {disp[0]}: {disp[1] or '(no reason recorded)'}"
                    else:
                        how = "UNDISCHARGED"
                    print(f"    - {r['edge_id']} {r['from_formal_name']} {r['relation']} "
                          f"{r['to_formal_name']} [{r.get('verdict')}] -> {how}")
                evid = evidence.V.get(formal_name, [])
                print(f"  V({formal_name}) = {len(evid)} verified/conditional Rocq edge(s)")
                for e in evid:
                    ext = e.get("external") or []
                    print(f"    - {e['from']} {e['kind']} {e['to']} [{e['status']}]"
                          + (f" external={ext}" if ext else "")
                          + f" sources={', '.join(e.get('sources') or [])}")
                return 0
        sys.exit(f"sync_edge_legs: slug {args.explain!r} not found in "
                 f"{'/'.join(corpora)} overlay+manifest")

    # ── --check ──
    if args.check:
        drift = []
        for corpus, rows in plans.items():
            for slug, cur, new, reason, _fn, _row in rows:
                if cur != new:
                    drift.append(f"{corpus}/{slug}: overlay edges={cur!r} derived={new!r} ({reason})")
        for corpus, rows in plans.items():
            c = summarize(rows)
            print(f"{corpus}: derived edges legs — {c['done']} done / {c['partial']} partial / "
                  f"{c['todo']} todo over {len(rows)} rows")
        if drift:
            print(f"\nEDGE-LEG DRIFT: {len(drift)} row(s) disagree with the evidence "
                  f"(run `python3 meta/sync_edge_legs.py --write`):")
            for d in drift:
                print("  - " + d)
            return 1
        print("edge-leg gate OK: every overlay `edges` leg matches the derived state")
        return 0

    # ── dry run / --write ──
    commit = args.commit or head_commit()
    total_changed = 0
    for corpus, rows in plans.items():
        changes = [r for r in rows if r[1] != r[2]]
        counts, cur_counts = summarize(rows), {s: 0 for s in STATES}
        for _slug, cur, _new, _r, _fn, _row in rows:
            cur_counts[cur] = cur_counts.get(cur, 0) + 1
        print(f"\n=== {corpus}: {len(rows)} overlay-tracked non-alias rows ===")
        print(f"  current: {cur_counts['done']} done / {cur_counts['partial']} partial / "
              f"{cur_counts['todo']} todo")
        print(f"  derived: {counts['done']} done / {counts['partial']} partial / "
              f"{counts['todo']} todo   ({len(changes)} row(s) would change)")
        promotions = [c for c in changes if STATES.index(c[2]) > STATES.index(c[1])]
        demotions = [c for c in changes if STATES.index(c[2]) < STATES.index(c[1])]
        for label, group in (("promote", promotions), ("demote", demotions)):
            if not group:
                continue
            print(f"  -- {label} ({len(group)}) --")
            for slug, cur, new, reason, _fn, _row in sorted(group):
                print(f"    {slug}: {cur} -> {new}  [{reason}]")
        total_changed += len(changes)
        if args.write and changes:
            path = REG.overlay_path(corpus)
            fmt = overlay_format(path)
            if fmt is None:
                sys.exit(f"sync_edge_legs: cannot reproduce the JSON formatting of {path} "
                         f"byte for byte; refusing to rewrite it")
            doc = json.load(open(path, encoding="utf-8"))
            entries = doc["entries"]
            stamped = 0
            for slug, cur, new, _reason, formal_name, row in changes:
                entry = entries[slug]
                entry["edges"] = new
                if cur == "todo" and new != "todo":
                    if not entry.get("package"):
                        entry["package"] = package_of(evidence, formal_name, row)
                        stamped += 1
                    if not entry.get("commit"):
                        entry["commit"] = commit
                        stamped += 1
            write_overlay(path, doc, fmt)
            print(f"  wrote {os.path.relpath(path, MONO)}: {len(changes)} `edges` leg(s) updated"
                  f"{f', {stamped} missing provenance field(s) stamped (commit {commit})' if stamped else ''}")
    if not args.write:
        print(f"\ndry run — nothing written ({total_changed} row(s) would change). "
              f"Apply with `python3 meta/sync_edge_legs.py --write`.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
