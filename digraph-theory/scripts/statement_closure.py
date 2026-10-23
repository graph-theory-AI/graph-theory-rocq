#!/usr/bin/env python3
"""statement_closure.py — per-result statement closures (PLAN_WEB M18).

For each catalog result, compute the set of constants its *statement*
(header up to `Proof.` / `:=`) references — read off the build's .glob
files — and close transitively through Digraph *definitions* (never
through lemmas, never into proofs). Emit docs/web/closure.json.

The closure is the site's audit contract: every Digraph constant in a
result's closure must be covered by a def-block (checked by the M21 CI
gate via the defblocks curation map docs/web/defblocks.json).

Glob format recap (coq/rocq):
  decl lines:  {kind} {bs}:{be} {secpath} {name}     (span = identifier)
  ref lines:   R{bs}:{be} {lib} {modpath} {name} {kind}
Notation refs (kind `not`) carry the defining file but not the constant;
NOTATION_MAP resolves the Digraph ones.
"""

from __future__ import annotations

import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
OUTPUT = ROOT / "docs" / "web" / "closure.json"

# --------------------------------------------------------------------------
# The catalog: result -> file (PLAN_WEB §1).
# --------------------------------------------------------------------------

CATALOG = {
    # U. the unified theorem
    "conjecture_5_10_at_345": "theories/applications/unified.v",
    "conjecture_5_10_at_k3": "theories/applications/unified.v",
    "question_5_9_fails_at_k3": "theories/applications/unified.v",
    "conjecture_5_10_at_k4": "theories/applications/k4/k4_main.v",
    "question_5_9_fails_at_k4": "theories/applications/k4/k4_main.v",
    "conjecture_5_10_at_k5": "theories/applications/k5/main.v",
    "question_5_9_fails_at_k5": "theories/applications/k5/main.v",
    # A. k = 3
    "AC_kcritical3": "theories/applications/k5/acn_base.v",
    "omegabar_AC": "theories/applications/k5/acn_base.v",
    "omegabar_AC_del": "theories/applications/k5/acn_base.v",
    "card_AC": "theories/constructions/circulant.v",
    "AC_vertex_transitive": "theories/constructions/circulant.v",
    # B. k = 4
    "T4_kcritical4": "theories/applications/k4/k4_main.v",
    "omegabar_T4": "theories/applications/k4/k4_value.v",
    "omegabar_T4_del": "theories/applications/k4/k4_main.v",
    "card_T4": "theories/applications/k4/k4_main.v",
    # C. k = 5
    "T5_kcritical5": "theories/applications/k5/main.v",
    "omegabar_T5": "theories/applications/k5/main.v",
    "omegabar_T5_del": "theories/applications/k5/main.v",
    "card_T5": "theories/applications/k5/main.v",
    # P. paths (Cheng--Keevash)
    "ck_conj1_delta3": "theories/applications/ck3/ck3_main.v",
    "ck_conj1_delta3_path": "theories/applications/ck3/ck3_main.v",
    "ck_conj1_delta2": "theories/applications/ck3/lemma7.v",
    "ck_conj1_delta7": "theories/applications/ck_path/ckpath_k7_concrete.v",
    "ck_conj1_delta7_path": "theories/applications/ck_path/ckpath_k7_concrete.v",
    "ck_conj1_at_7": "theories/applications/ck_path/ckpath_k7_concrete.v",
    "ck_theorem4_oriented": "theories/applications/ck3/lemma7.v",
    "lemma7": "theories/applications/ck3/lemma7.v",
    "no_short_strong3": "theories/applications/ck3/ck3_main.v",
    # G. general tournament theory
    "omegabar_lexprod_ge": "theories/invariants_advanced/substitution.v",
    "vt_kcritical": "theories/invariants_advanced/transitive.v",
    "omegabar_del_vt": "theories/invariants_advanced/transitive.v",
    "domnum_le_omegabar": "theories/invariants/domination.v",
    "kcritical2_uniq": "theories/invariants/critical.v",
    "kcritical_proper_sub": "theories/invariants/critical.v",
    "omegabar_transb": "theories/invariants/omegabar.v",
}

# --------------------------------------------------------------------------
# Digraph notations -> underlying constants.
# --------------------------------------------------------------------------

NOTATION_MAP = {
    ("Digraph.invariants.omegabar", ":::'ω̄('_x_')'"): ["omegabar"],
    ("Digraph.core.digraph", "::digraph_scope:x_'-->'_x"): ["arc"],
    ("Digraph.core.dipath", ":::'ℓ('_x_')'"): ["ell"],
}

# External notations we deliberately ignore (pure syntax: scopes, comma).
EXTERNAL_NOISE_KINDS = {"var", "lib", "mod", "modtype", "sec", "binder"}

# Digraph constants treated as leaves (hand-written def-blocks; do not
# recurse into HB-generated structure plumbing).
LEAVES = {
    "arc",
    "tournament",
    "diGraphType",
    "orientedType",
}

# HB / structure plumbing: fold into the def-block of the visible
# concept instead of recursing (name-pattern based).
PLUMBING_RE = re.compile(
    r"(__|^HB_|^hb_|_Exports$|^Build$|\.sort$|^sort$|^eta$|"
    r"^DiGraph$|^Oriented$|^Tournament$|^HasArc$|"
    r"^DiGraph_IsOriented$|^Oriented_IsTournament$|^DiGraph_IsTournament$)"
)

DECL_KINDS = {
    "def", "abbrev", "ind", "constr", "proj", "rec", "fix", "cofix",
    "scheme", "class", "inst", "meth", "defax", "syndef", "not",
}
THM_KINDS = {"thm", "prf", "ax"}


def vfile_to_lib(vpath: str) -> str:
    """theories/core/digraph.v -> Digraph.core.digraph"""
    parts = Path(vpath).with_suffix("").parts
    assert parts[0] == "theories"
    return ".".join(("Digraph",) + parts[1:])


class GlobFile:
    """Parsed .glob: decls (name -> ident offset) and refs (offset-sorted)."""

    def __init__(self, vpath: Path):
        self.vpath = vpath
        self.src = vpath.read_bytes()
        self.lib = vfile_to_lib(str(vpath.relative_to(ROOT)))
        gpath = vpath.with_suffix(".glob")
        if not gpath.exists():
            sys.exit(f"missing {gpath} — build the library first (make)")
        self.decls: dict[str, tuple[str, int, int]] = {}  # name -> kind,bs,be
        self.refs: list[tuple[int, int, str, str, str, str]] = []
        for line in gpath.read_text(encoding="utf-8").splitlines():
            m = re.match(r"^R(\d+):(\d+) (\S+) (\S+) (\S+) (\S+)$", line)
            if m:
                bs, be = int(m.group(1)), int(m.group(2))
                self.refs.append((bs, be, m.group(3), m.group(4),
                                  m.group(5), m.group(6)))
                continue
            m = re.match(r"^(\w+) (\d+):(\d+) (\S+) (\S+)$", line)
            if m and m.group(1) in {"def", "prf", "thm", "ind", "constr",
                                    "proj", "rec", "fix", "abbrev", "not",
                                    "ax", "defax", "scheme", "class",
                                    "inst"}:
                kind, bs, be = m.group(1), int(m.group(2)), int(m.group(3))
                self.decls[m.group(5)] = (kind, bs, be)

    def line_of(self, off: int) -> int:
        return self.src[:off].count(b"\n") + 1

    def statement_span(self, name: str) -> tuple[int, int, str]:
        """(start, end, kind) of NAME's *statement*: from the keyword
        before the identifier to `Proof`/`:=` (thm) or the closing `.`
        of the sentence chain up to the next declaration (definitions)."""
        if name not in self.decls:
            sys.exit(f"{self.vpath}: no declaration {name!r} in glob")
        kind, bs, be = self.decls[name]
        # Statement runs from the identifier to the proof marker.
        if kind in THM_KINDS or kind == "prf":
            m = re.compile(rb"\bProof\b|:=").search(self.src, be)
            end = m.start() if m else len(self.src)
            return bs, end, kind
        # Definition-like: the enclosing Rocq sentence — up to the first
        # `.` followed by whitespace (`.+1`, `.-1`, `%N].` are safe: the
        # dot there is not followed by whitespace), capped at the next
        # recorded declaration.
        nexts = sorted(b for (_, b, _) in self.decls.values() if b > bs)
        cap = nexts[0] if nexts else len(self.src)
        m = re.compile(rb"\.(?=\s)").search(self.src, be, cap)
        end = m.end() if m else cap
        return bs, end, kind

    def refs_in(self, lo: int, hi: int):
        return [r for r in self.refs if lo <= r[0] < hi]


class Closure:
    def __init__(self):
        self.globs: dict[str, GlobFile] = {}

    def glob_for(self, vrel: str) -> GlobFile:
        if vrel not in self.globs:
            self.globs[vrel] = GlobFile(ROOT / vrel)
        return self.globs[vrel]

    def find_digraph_decl(self, lib: str, name: str) -> GlobFile | None:
        vrel = "theories/" + "/".join(lib.split(".")[1:]) + ".v"
        if not (ROOT / vrel).exists():
            return None
        g = self.glob_for(vrel)
        return g if name in g.decls else None

    def close(self, result: str, vrel: str):
        g = self.glob_for(vrel)
        lo, hi, _ = g.statement_span(result)
        digraph: dict[str, dict] = {}
        external: dict[str, dict] = {}
        seen: set[tuple[str, str]] = set()
        queue: list[tuple[str, str, str]] = []   # (lib, name, kind)

        def enqueue(refs, via: str):
            for bs, be, lib, mod, name, kind in refs:
                if kind in EXTERNAL_NOISE_KINDS:
                    continue
                if lib.startswith("Digraph"):
                    if kind == "not":
                        for c in NOTATION_MAP.get((lib, name), []):
                            key = (lib, c)
                            if key not in seen:
                                seen.add(key)
                                queue.append((lib, c, "def"))
                        if (lib, name) not in NOTATION_MAP:
                            sys.exit(f"{result}: unmapped Digraph notation "
                                     f"{name!r} from {lib} (via {via}) — "
                                     f"add it to NOTATION_MAP")
                        continue
                    key = (lib, name)
                    if key not in seen:
                        seen.add(key)
                        queue.append((lib, name, kind))
                else:
                    key = f"{lib}:{name}"
                    if key not in external:
                        external[key] = {"lib": lib, "name": name,
                                         "kind": kind}

        enqueue(g.refs_in(lo, hi), result)
        while queue:
            lib, name, kind = queue.pop()
            if PLUMBING_RE.search(name):
                digraph.setdefault(name, {"lib": lib, "kind": kind,
                                          "plumbing": True})
                continue
            entry = {"lib": lib, "kind": kind, "plumbing": False}
            digraph[name] = entry
            if name in LEAVES:
                continue
            owner = self.find_digraph_decl(lib, name)
            if owner is None:
                entry["plumbing"] = True       # generated, no source decl
                continue
            # Recurse into the declaration's *statement* span: for a
            # definition that is its body; for a Fact/Lemma it stops at
            # `Proof.` — meaning flows through statement types, proofs
            # never enter the closure.
            dlo, dhi, dkind = owner.statement_span(name)
            entry["kind"] = dkind
            enqueue(owner.refs_in(dlo, dhi), name)

        stmt = g.src[lo:hi].decode("utf-8").rstrip().rstrip(".").rstrip()
        return {
            "file": vrel,
            "line": g.line_of(lo),
            "statement": stmt,
            "digraph": dict(sorted(digraph.items())),
            "external": dict(sorted(external.items())),
        }


DEFBLOCKS = ROOT / "docs" / "web" / "defblocks.json"


def check(out: dict) -> int:
    """The audit gate: every Digraph constant in every closure must map
    to a def-block, and every mapped block must exist. Returns the
    number of violations (0 = green)."""
    cur = json.loads(DEFBLOCKS.read_text(encoding="utf-8"))
    blocks, cmap = cur["blocks"], cur["map"]
    bad = 0
    for result, r in out.items():
        for cname in r["digraph"]:
            blk = cmap.get(cname)
            if blk is None:
                print(f"UNMAPPED: {cname} (in closure of {result}) — "
                      f"add it to docs/web/defblocks.json")
                bad += 1
            elif blk not in blocks:
                print(f"DANGLING BLOCK: {cname} -> {blk} (no such block)")
                bad += 1
    # blocks pointing at quotes that no longer exist in the source
    for bid, b in blocks.items():
        if b.get("quote") in (None, "HB"):
            continue
        for q in b["quote"]:
            qfile = q["file"] if isinstance(q, dict) else b["file"]
            qname = q["name"] if isinstance(q, dict) else q
            src = (ROOT / qfile).read_text(encoding="utf-8")
            qq = re.escape(qname)
            decl = re.search(
                rf"^(Definition|Notation|Lemma|Theorem|Fact"
                rf"|Local Notation)\s+{qq}\b", src, re.M)
            hb_short = re.search(rf'short\(type="{qq}"\)', src)
            hb_field = re.search(rf"\{{\s*{qq}\s*:", src)
            if not (decl or hb_short or hb_field):
                print(f"STALE QUOTE: {bid} expects a declaration "
                      f"{qname!r} in {qfile}")
                bad += 1
    return bad


def main() -> None:
    cl = Closure()
    out = {}
    for result, vrel in CATALOG.items():
        out[result] = cl.close(result, vrel)
    OUTPUT.parent.mkdir(parents=True, exist_ok=True)
    OUTPUT.write_text(json.dumps(out, indent=2, ensure_ascii=False) + "\n",
                      encoding="utf-8")
    ndef = len({n for r in out.values() for n in r["digraph"]})
    print(f"{len(out)} results, {ndef} distinct Digraph constants "
          f"-> {OUTPUT.relative_to(ROOT)}")
    if "--check" in sys.argv:
        bad = check(out)
        if bad:
            sys.exit(f"closure check FAILED: {bad} violation(s)")
        print("closure check OK: every closure constant has a def-block")


if __name__ == "__main__":
    main()
