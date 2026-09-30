#!/usr/bin/env python3
"""Doc-block gate for corpus statements (plan WP4).

Every statement definition in `*/theories/{conjectures,foundations,applications}/*.v` must
carry, immediately before it, a doc block tying it to its corpus row:

    (** Corpus row: arxiv:1611.03196#02
        Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/1611.03196__02/
        Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/1611.03196__02.json
        English statement: (Aharoni, Alon, Berger, ... 2016, Conjecture 1.14)
          If the edge set of a graph H is partitioned into E_1, ..., E_m, then some matching M
          satisfies |M inter E_i| >= floor(|E_i| / (Delta(H)+2)) for every i.
        Definitions: [x15_matching M] - a set of pairwise disjoint edges; [Delta H] - maximum
          degree (GTBase).
        Notes: optional free text about load-bearing modelling choices. *)
    Definition fair_matching_edge_partition_statement : Prop :=

Keys in that order; `Notes:` optional. `Site:`/`Review:` must equal
`corpus_registry.row_urls(row_id)` byte for byte (the literal `none` only for rows without a
site page: erdos / derived / studies). A statement with no corpus row instead carries
`(** No corpus row: <reason> *)`.

A third block kind documents an EXTERNAL, cited classical fact that the development carries as an
explicit hypothesis (`Definition external_*_statement : Prop`, never an `Axiom`, never `Admitted`
— the shape a `status=conditional` @EDGE depends on, see meta/external_theorems.json):

    (** External theorem: <authors>, <title/venue> <year>, <link>.
        Claim: <what the cited theorem says, and which instance the Prop below states>.
        Not formalized here. *)
    Definition external_circular_5_flow_statement : Prop :=

`External theorem:` and `Claim:` are the only keys of that block; the `External theorem:` value is
the citation line and must carry a year. It is accepted ONLY on definitions named
`external_*_statement`, and never on a corpus formal_name (a corpus row's statement is a
conjecture of the corpus, not a cited theorem).

Targets are `Definition`/`Let` declarations whose name ends in `_statement` or is a
`formal_name` of either corpus manifest; files named `_assum_*`, `_faith_*` or
`rocq_mcp_cache_*` are skipped. Manifests are read through `corpus_registry.load_manifest`
at run time (never cached), so the gate follows manifest regenerations.

Rollout: `meta/statement_docs_baseline.json` lists the targets that are still undocumented.
The gate fails on any undocumented target outside the baseline and on any baseline entry that
has become documented or disappeared, so the baseline can only shrink (`--write-baseline`
rewrites it, `--list` prints what is left).

Usage:
    python3 meta/check_statement_docs.py [<package> ...] [--warnings] [--strict]
    python3 meta/check_statement_docs.py --write-baseline
    python3 meta/check_statement_docs.py --list
"""
from __future__ import annotations

import argparse
import glob
import json
import os
import re
import sys

META = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, META)
import corpus_registry as REG           # noqa: E402
import gate_contracts as CONTRACTS      # noqa: E402

SCAN_DIRS = ("conjectures", "foundations", "applications")
SKIP_FILE_PREFIXES = ("_assum_", "_faith_", "rocq_mcp_cache_")
BASELINE_PATH = os.path.join(META, "statement_docs_baseline.json")

# Order-significant grammar of the doc block.
ROW_KEYS = ("Corpus row", "Site", "Review", "English statement", "Definitions", "Notes")
OPTIONAL_KEYS = ("Notes",)
# the `External theorem:` block (a cited classical fact carried as an explicit hypothesis)
EXTERNAL_KEYS = ("External theorem", "Claim")
EXTERNAL_NAME_RE = re.compile(r"^external_[A-Za-z0-9_']*_statement$")
# a citation line names a year; without one "External theorem: it is known that ..." would pass
CITATION_YEAR_RE = re.compile(r"\b(?:1[89]|20)\d{2}\b")
KEY_RE = re.compile(
    r"^\s*(No corpus row|Corpus row|Site|Review|English statement|Definitions|Notes"
    r"|External theorem|Claim)\s*:\s*(.*)$"
)

# WP4b: local vocabulary duplicating a coq-graph-theory / GTBase notion (warning only).
LIBRARY_SUFFIXES = {
    "edge_set", "edges", "matching", "perfect_matching", "connected", "conn", "path", "cycle",
    "hamiltonian", "minor", "treewidth", "tree", "forest", "tournament", "regular", "clique",
    "stable", "independent", "dominating", "bipartite", "complete", "acyclic", "colouring",
    "coloring",
}

COVERED_STATEMENT_LEGS = ("done", "partial", "blocked")


# ── corpus index ────────────────────────────────────────────────────────────────────────────
class CorpusIndex:
    """Row id -> row, plus the set of formal_names, read fresh from both manifests."""

    def __init__(self):
        self.rows = {}          # row_id -> dict(row_id, corpus, formal_name, repo, alias_of, leg)
        self.formal_names = set()
        v2 = REG.load_manifest("v2", required=False)
        for row in (v2 or {}).get("rows", []):
            rid = row.get("row_id")
            if not rid:
                continue
            self.rows[rid] = {
                "row_id": rid,
                "corpus": "v2",
                "formal_name": row.get("formal_name"),
                "repo": row.get("repo"),
                "alias_of": row.get("alias_of"),
                "leg": (row.get("legs") or {}).get("statement"),
            }
        opg = REG.load_manifest("opg", required=False)
        for row in (opg or {}).get("rows", []):
            slug = row.get("slug")
            if not slug:
                continue
            rid = f"opg:{slug}"
            self.rows[rid] = {
                "row_id": rid,
                "corpus": "opg",
                "formal_name": row.get("formal_name"),
                "repo": row.get("repo"),
                "alias_of": row.get("alias_of"),
                "leg": (row.get("legs") or {}).get("statement"),
            }
        self.formal_names = {r["formal_name"] for r in self.rows.values() if r.get("formal_name")}

    def rows_needing_coverage(self):
        """Rows that must own at least one documented definition (reverse coverage)."""
        out = []
        for row in self.rows.values():
            if row.get("alias_of") or not row.get("formal_name"):
                continue
            if row["corpus"] == "opg" or row.get("leg") in COVERED_STATEMENT_LEGS:
                out.append(row)
        return out


# ── target discovery ────────────────────────────────────────────────────────────────────────
class Target:
    __slots__ = ("key", "path", "rel", "package", "name", "line", "start", "block")

    def __init__(self, package, rel, path, name, line, start):
        self.package, self.rel, self.path = package, rel, path
        self.name, self.line, self.start = name, line, start
        self.key = f"{rel}#{name}"
        self.block = None


def packages_with_theories(root, wanted=None):
    names = sorted(
        d for d in os.listdir(root)
        if os.path.isdir(os.path.join(root, d, "theories")) and not d.startswith(".")
    )
    if wanted:
        unknown = [w for w in wanted if w not in names]
        if unknown:
            raise SystemExit(f"check_statement_docs: unknown package(s) {unknown}; "
                             f"known: {names}")
        names = [n for n in names if n in wanted]
    return names


def source_files(root, packages):
    for pkg in packages:
        for sub in SCAN_DIRS:
            for path in sorted(glob.glob(os.path.join(root, pkg, "theories", sub, "*.v"))):
                base = os.path.basename(path)
                if base.startswith(SKIP_FILE_PREFIXES):
                    continue
                rel = f"{pkg}/theories/{sub}/{base}"
                yield pkg, rel, path


def definitions_in(src):
    """(name, start_offset) of every Definition/Let declaration outside comments.

    ``DEFINITION_DECL_RE`` starts with ``^\\s*``, and ``\\s`` matches newlines, so a match can
    begin lines above the command (comment bodies are blanked by ``strip_comments`` while
    keeping their offsets): skip the leading whitespace to land on the keyword itself.
    """
    clean = CONTRACTS.strip_comments(src)
    out = []
    for m in CONTRACTS.DEFINITION_DECL_RE.finditer(clean):
        text = m.group(0)
        out.append((m.group(1), m.start() + len(text) - len(text.lstrip())))
    return out


def is_target(name, corpus_names):
    return name.endswith("_statement") or name in corpus_names


def attached_comment(src, spans, start):
    """The last top-level comment ending before ``start`` with only whitespace in between."""
    best = None
    for span_start, span_end in spans:
        if span_end <= start and not src[span_end:start].strip():
            best = (span_start, span_end)
    return best


# ── doc-block parsing ───────────────────────────────────────────────────────────────────────
def parse_block(text):
    """Parse a comment body into (kind, values, errors).

    kind is 'row', 'orphan', 'external' or None (no recognisable doc block).
    """
    inner = text
    if inner.startswith("(*"):
        inner = inner[2:]
    if inner.endswith("*)"):
        inner = inner[:-2]
    inner = inner.lstrip("*")

    order, values, errors = [], {}, []
    current = None
    for raw in inner.splitlines():
        m = KEY_RE.match(raw)
        if m:
            key, rest = m.group(1), m.group(2)
            if key in values:
                errors.append(f"doc block: duplicate key `{key}:`")
            order.append(key)
            values[key] = [rest.strip()]
            current = key
        elif current is not None:
            values[current].append(raw.strip())
    if not order:
        return None, {}, errors
    joined = {k: " ".join(p for p in v if p).strip() for k, v in values.items()}

    if order[0] == "No corpus row":
        if len(order) > 1:
            errors.append(f"doc block: `No corpus row:` must be the only key (found {order[1:]})")
        if not joined["No corpus row"]:
            errors.append("doc block: `No corpus row:` needs a reason")
        return "orphan", joined, errors

    if order[0] == "External theorem":
        extra = [k for k in order if k not in EXTERNAL_KEYS]
        if extra:
            errors.append(f"doc block: an `External theorem:` block may only use "
                          f"{list(EXTERNAL_KEYS)} (found {extra})")
        for key in EXTERNAL_KEYS:
            if key not in values:
                errors.append(f"doc block: missing key `{key}:`")
            elif not joined[key]:
                errors.append(f"doc block: `{key}:` is empty")
        if joined.get("External theorem") and not CITATION_YEAR_RE.search(joined["External theorem"]):
            errors.append("doc block: `External theorem:` must be a citation line "
                          "(authors, title/venue, year, link); no year found")
        return "external", joined, errors

    if "No corpus row" in order:
        errors.append("doc block: `No corpus row:` mixed with corpus keys")
    for key in EXTERNAL_KEYS:
        if key in order:
            errors.append(f"doc block: `{key}:` mixed with corpus keys (an `External theorem:` "
                          "block starts with that key and carries no corpus row)")
    expected = [k for k in ROW_KEYS if k in order]
    present = [k for k in order if k in ROW_KEYS]
    for key in ROW_KEYS:
        if key not in OPTIONAL_KEYS and key not in values:
            errors.append(f"doc block: missing key `{key}:`")
    if present != expected:
        errors.append(f"doc block: keys out of order {present} (expected {expected})")
    for key in ("English statement", "Definitions"):
        if key in joined and not joined[key]:
            errors.append(f"doc block: `{key}:` is empty")
    return "row", joined, errors


def check_block(target, kind, values, index):
    """Semantic checks of a parsed block against the corpus manifests."""
    errors = []
    name = target.name
    if kind == "orphan":
        if name in index.formal_names:
            errors.append(f"`No corpus row` on {name}, which is a corpus formal_name")
        return errors, None

    if kind == "external":
        # the block kind is reserved for the cited-classical-fact hypotheses: a corpus conjecture
        # documented as an "external theorem" would silently launder a conjecture into a theorem.
        if not EXTERNAL_NAME_RE.match(name):
            errors.append(f"`External theorem:` block on {name}, which is not an "
                          "`external_*_statement` definition (that block kind documents a cited "
                          "classical fact carried as an explicit hypothesis)")
        if name in index.formal_names:
            errors.append(f"`External theorem:` on {name}, which is a corpus formal_name "
                          "(a corpus row states a conjecture, not a cited theorem)")
        return errors, None

    row_id = values.get("Corpus row", "")
    row = index.rows.get(row_id)
    if not row_id:
        errors.append("doc block: `Corpus row:` is empty")
        return errors, None
    if row is None:
        errors.append(f"unknown corpus row `{row_id}`")
        return errors, None
    if row.get("alias_of"):
        errors.append(f"corpus row `{row_id}` is an alias of `{row['alias_of']}` "
                      "(alias rows never own a statement)")
    if row.get("formal_name") != name:
        errors.append(f"corpus row `{row_id}` has formal_name "
                      f"{row.get('formal_name')!r}, not {name!r}")
    if row.get("repo") != target.package:
        errors.append(f"corpus row `{row_id}` has repo {row.get('repo')!r}, "
                      f"but the definition lives in {target.package!r}")

    site, review = REG.row_urls(row_id)
    for key, expected in (("Site", site), ("Review", review)):
        got = values.get(key, "")
        want = expected if expected is not None else "none"
        if got != want:
            errors.append(f"doc block: `{key}:` is {got!r}, expected {want!r}")
    return errors, (row_id if not errors else None)


# ── warnings (WP4b duplicate vocabulary) ────────────────────────────────────────────────────
def vocabulary_warnings(rel, src):
    out = []
    for name, start in definitions_in(src):
        if "_" not in name:
            continue
        line = src.count("\n", 0, start) + 1
        suffix = name.rsplit("_", 1)[1]
        pair = "_".join(name.rsplit("_", 2)[1:]) if name.count("_") >= 2 else None
        hit = pair if pair in LIBRARY_SUFFIXES else (suffix if suffix in LIBRARY_SUFFIXES else None)
        if hit and name != hit:
            out.append((rel, line, name,
                        f"warning: local definition duplicates the library/GTBase notion "
                        f"`{hit}` (WP4b)"))
    return out


# ── the gate ────────────────────────────────────────────────────────────────────────────────
def scan(root, packages, index):
    """Return (targets, warnings); every target carries its parsed block (or None)."""
    targets, warnings = [], []
    for pkg, rel, path in source_files(root, packages):
        with open(path, encoding="utf-8") as fh:
            src = fh.read()
        spans = CONTRACTS.comment_spans(src)
        for name, start in definitions_in(src):
            if not is_target(name, index.formal_names):
                continue
            line = src.count("\n", 0, start) + 1
            target = Target(pkg, rel, path, name, line, start)
            span = attached_comment(src, spans, start)
            target.block = parse_block(src[span[0]:span[1]]) if span else (None, {}, [])
            targets.append(target)
        warnings.extend(vocabulary_warnings(rel, src))
    return targets, warnings


def load_baseline(path):
    if not os.path.exists(path):
        return []
    return json.load(open(path, encoding="utf-8"))


def run(root=None, packages=None, show_warnings=False, strict=False, write_baseline=False,
        list_baseline=False, baseline_path=None, out=None, ignore_baseline=False):
    root = root or REG.MONO
    out = out or sys.stdout
    baseline_path = baseline_path or BASELINE_PATH
    index = CorpusIndex()

    if write_baseline:
        # Always scan the whole tree: a partial scan would silently shrink the baseline.
        pkgs = packages_with_theories(root)
        targets, _ = scan(root, pkgs, index)
        undocumented = sorted(t.key for t in targets if t.block[0] is None)
        with open(baseline_path, "w", encoding="utf-8") as fh:
            json.dump(undocumented, fh, indent=1)
            fh.write("\n")
        print(f"wrote {baseline_path}: {len(undocumented)} undocumented target(s) "
              f"out of {len(targets)}", file=out)
        return 0

    pkgs = packages_with_theories(root, packages)
    targets, warnings = scan(root, pkgs, index)
    baseline = load_baseline(baseline_path)
    baseline_set = set(baseline)
    in_scope = {f"{p}/" for p in pkgs}

    if list_baseline:
        remaining = sorted(e for e in baseline_set
                           if any(e.startswith(p) for p in in_scope))
        for entry in remaining:
            print(entry, file=out)
        print(f"{len(remaining)} baseline entr{'y' if len(remaining) == 1 else 'ies'} remaining",
              file=out)
        return 0

    problems, covered = [], set()
    seen_keys = set()
    for target in targets:
        seen_keys.add(target.key)
        kind, values, errors = target.block
        if kind is None:
            if target.key in baseline_set:
                continue
            problems.append((target.rel, target.line, target.name,
                             "missing doc block (add `(** Corpus row: ... *)` or "
                             "`(** No corpus row: <reason> *)`)"))
            continue
        if target.key in baseline_set and not ignore_baseline:
            problems.append((target.rel, target.line, target.name,
                             "baseline entry is now documented; re-run "
                             "`python3 meta/check_statement_docs.py --write-baseline`"))
        errs = list(errors)
        semantic, row_id = check_block(target, kind, values, index)
        errs.extend(semantic)
        if row_id:
            covered.add(row_id)
        for err in errs:
            problems.append((target.rel, target.line, target.name, err))

    for entry in sorted(baseline_set):
        if ignore_baseline or not any(entry.startswith(p) for p in in_scope):
            continue
        if entry not in seen_keys:
            rel, _, name = entry.partition("#")
            problems.append((rel, 0, name,
                             "baseline entry no longer exists; re-run "
                             "`python3 meta/check_statement_docs.py --write-baseline`"))

    for rel, line, name, message in sorted(problems):
        print(f"{rel}:{line}: {name}: {message}", file=out)

    if show_warnings:
        for rel, line, name, message in sorted(warnings):
            print(f"{rel}:{line}: {name}: {message}", file=out)
        by_pkg = {}
        for rel, _, _, _ in warnings:
            by_pkg[rel.split("/", 1)[0]] = by_pkg.get(rel.split("/", 1)[0], 0) + 1
        for pkg in sorted(by_pkg):
            print(f"warnings: {pkg}: {by_pkg[pkg]}", file=out)
        print(f"warnings: total {len(warnings)}", file=out)

    needed = [r for r in index.rows_needing_coverage()
              if not packages or r.get("repo") in set(packages)]
    uncovered = [r for r in needed if r["row_id"] not in covered]
    print(f"statement docs: {len(targets)} target(s), "
          f"{sum(1 for t in targets if t.block[0] is not None)} documented, "
          f"{len(baseline_set)} in baseline, {len(problems)} error(s); "
          f"reverse coverage: {len(needed) - len(uncovered)}/{len(needed)} rows covered, "
          f"{len(uncovered)} uncovered", file=out)
    if uncovered and strict:
        for row in sorted(uncovered, key=lambda r: r["row_id"])[:50]:
            print(f"uncovered corpus row: {row['row_id']} ({row['formal_name']})", file=out)
        return 1
    return 1 if problems else 0


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("packages", nargs="*", help="restrict the scan to these package directories")
    ap.add_argument("--warnings", action="store_true",
                    help="also print WP4b duplicate-vocabulary warnings")
    ap.add_argument("--strict", action="store_true",
                    help="fail when a corpus row owns no documented definition")
    ap.add_argument("--write-baseline", action="store_true",
                    help="rewrite meta/statement_docs_baseline.json (whole tree)")
    ap.add_argument("--list", dest="list_baseline", action="store_true",
                    help="print the remaining baseline entries")
    ap.add_argument("--ignore-baseline", action="store_true",
                    help="do not complain about baseline entries that became documented "
                         "(for a documentation pass in progress; still undocumented baseline "
                         "entries are still tolerated)")
    args = ap.parse_args(argv)
    return run(packages=args.packages or None, show_warnings=args.warnings, strict=args.strict,
               write_baseline=args.write_baseline, list_baseline=args.list_baseline,
               ignore_baseline=args.ignore_baseline)


if __name__ == "__main__":
    sys.exit(main())
