#!/usr/bin/env python3
"""Syntactic suspicion lint for conjecture statements.

The lint deliberately has high recall and does not claim that a finding is a
mathematical defect.  ``make audit`` prints the legacy backlog as warnings;
``make gate`` runs ``--new-waves --check`` and rejects unallowlisted findings
in prospective waves (X211 onward by policy).
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from collections import Counter
from dataclasses import dataclass
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
META = ROOT / "meta"
POLICY = json.loads((META / "faithfulness_policy.json").read_text())
ALLOWLIST = META / "faithfulness_lint_allowlist.json"
DEF_START_RE = re.compile(r"^\s*Definition\s+([A-Za-z_][A-Za-z0-9_']*)\b", re.M)


@dataclass(frozen=True)
class Finding:
    path: str
    line: int
    statement: str
    rule: str
    message: str

    @property
    def key(self) -> str:
        return f"{self.path}:{self.statement}:{self.rule}"


def strip_comments(src: str) -> str:
    """Remove nested Rocq comments while preserving offsets and line numbers."""
    out: list[str] = []
    i = depth = 0
    while i < len(src):
        if src.startswith("(*", i):
            depth += 1
            out.extend("  ")
            i += 2
        elif depth and src.startswith("*)", i):
            depth -= 1
            out.extend("  ")
            i += 2
        elif depth:
            out.append("\n" if src[i] == "\n" else " ")
            i += 1
        else:
            out.append(src[i])
            i += 1
    return "".join(out)


def sentence_end(src: str, start: int) -> int:
    i = start
    while True:
        j = src.find(".", i)
        if j < 0:
            return len(src)
        nxt = src[j + 1:j + 2]
        if not nxt or nxt.isspace():
            return j + 1
        i = j + 1


def definition_commands(src: str) -> list[tuple[str, int, str, str]]:
    clean = strip_comments(src)
    out = []
    for match in DEF_START_RE.finditer(clean):
        end = sentence_end(clean, match.start())
        line = clean.count("\n", 0, match.start()) + 1
        out.append((match.group(1), line, clean[match.start():end], src[match.start():end]))
    return out


def registry_watchlist() -> dict[str, list[dict]]:
    sys.path.insert(0, str(META))
    import foundation_fidelity as fidelity

    return {
        primitive: [e for e in entries if e["verdict"] != "FAITHFUL"]
        for primitive, entries in fidelity.verdicts_by_primitive().items()
        if any(e["verdict"] != "FAITHFUL" for e in entries)
    }


def lint_source(path: str, src: str, watchlist: dict[str, list[dict]]) -> list[Finding]:
    findings: list[Finding] = []
    source_lines = src.splitlines()
    definitions = definition_commands(src)
    bodies = {name: command.split(":=", 1)[1] if ":=" in command else command
              for name, _line, command, _raw in definitions}

    def dependency_closure(name: str) -> str:
        pending = [name]
        seen = set()
        chunks = []
        while pending:
            current = pending.pop()
            if current in seen or current not in bodies:
                continue
            seen.add(current)
            body = bodies[current]
            chunks.append(body)
            for candidate in bodies:
                if candidate not in seen and re.search(
                        rf"(?<![A-Za-z0-9_']){re.escape(candidate)}(?![A-Za-z0-9_'])", body):
                    pending.append(candidate)
        return "\n".join(chunks)

    def add(line: int, statement: str, rule: str, message: str) -> None:
        findings.append(Finding(path, line, statement, rule, message))

    for name, line, command, _raw_command in definitions:
        if not name.endswith("_statement"):
            continue
        body = command.split(":=", 1)[1] if ":=" in command else command
        expanded_body = dependency_closure(name)

        if re.search(
            r"\bforall\s+(?:\([^,\n]*:\s*[^,\n)]*->\s*Prop\s*\)|"
            r"[A-Za-z_][A-Za-z0-9_']*\s*:\s*[^,\n]*->\s*Prop\s*,)",
            body,
        ):
            add(line, name, "quantified-prop-predicate",
                "top-level quantification over a Prop-valued predicate can make the row "
                "stronger, weaker, or vacuous")

        graph_forall = re.search(
            r"\bforall\b[\s\S]{0,180}?\bG\s*:\s*sgraph\b", body
        )
        if graph_forall and re.search(r"\bexists\s+(?:\([^)]*\)|[A-Za-z_][A-Za-z0-9_']*)",
                                      body[graph_forall.end():]):
            add(line, name, "exists-after-graph-forall",
                "an existential follows an outer graph quantifier; verify that the witness is "
                "not meant to be class-uniform")

        if re.search(r"\bfg_event_at_(?:least|most)_ratio\b", expanded_body):
            add(line, name, "fixed-ratio-whp",
                "a one-space fixed-ratio event appears in a statement; almost-all/whp claims "
                "must use fg_whp")

        girth = re.search(r"\bhas_girth\b", body)
        if girth and "->" in body[girth.end():]:
            add(line, name, "exact-girth-hypothesis",
                "has_girth means exact girth; verify that the source does not say girth at least")

        if re.search(r"\blogn\b", body):
            add(line, name, "logn-is-valuation",
                "MathComp logn is a 2-adic valuation, not floor log2; use trunc_log when intended")

        if re.search(r"(?<![<>=])\s-\s", body):
            context = "\n".join(source_lines[max(0, line - 13):line - 1]).lower()
            guarded = re.search(
                r"load-bearing|guard|truncat|subtraction|positive|nonzero|lower bound", context
            )
            if not guarded:
                add(line, name, "unguarded-nat-subtraction",
                    "natural-number subtraction appears without a nearby guard/truncation note")

        if re.search(r"\bx[0-9]+_(?:cost|cert_size)\b", body):
            add(line, name, "free-cost-field",
                "a paper-local cost/certificate-size field appears in the statement; verify that "
                "it is coupled to the algorithm or verifier")

        for primitive, entries in watchlist.items():
            if re.search(rf"(?<![A-Za-z0-9_']){re.escape(primitive)}(?![A-Za-z0-9_'])",
                         expanded_body):
                verdicts = "/".join(sorted({e["verdict"] for e in entries}))
                notes = "; ".join(e["note"] for e in entries)
                add(line, name, "foundation-fidelity",
                    f"uses {verdicts} primitive {primitive}: {notes}")

    return findings


def wave_files(*, wave: str | None = None, new_only: bool = False) -> list[Path]:
    data = json.loads((META / "v2_statement_waves.json").read_text()).get("waves", {})
    minimum = int(POLICY["prospective_v2_wave_min"])
    files: list[Path] = []
    for key, spec in data.items():
        phase = spec.get("phase", key)
        if wave is not None and phase != wave and key != wave:
            continue
        if new_only:
            match = re.fullmatch(r"X(\d+)", phase)
            if not match or int(match.group(1)) < minimum:
                continue
        files.append(ROOT / spec["repo"] / "theories" / "conjectures" / spec["defines_file"])
    return sorted(set(files))


def all_conjecture_files() -> list[Path]:
    return sorted(
        p for p in ROOT.glob("*/theories/conjectures/*.v")
        if not p.name.startswith(("grounding_", "implications_", "_assum_", "_faith_"))
    )


def load_allowlist() -> dict[str, str]:
    data = json.loads(ALLOWLIST.read_text())
    if data.get("schema_version") != 1 or not isinstance(data.get("entries"), dict):
        raise ValueError("faithfulness_lint_allowlist.json has an invalid schema")
    return data["entries"]


def validate() -> int:
    fixture = """
Definition fixture_statement : Prop :=
  forall (C : sgraph -> Prop) (G : sgraph),
    has_girth G 4 ->
    exists f : nat -> nat,
      fg_event_at_least_ratio nat_finType (fun _ => 1) (fun _ => true) 9 10 /\\
      logn (f 0) <= x211_cost G - 1 /\\
      clustered_chromatic_at_most G 2.
"""
    rules = {f.rule for f in lint_source("fixture.v", fixture, registry_watchlist())}
    expected = {
        "quantified-prop-predicate", "exists-after-graph-forall", "fixed-ratio-whp",
        "exact-girth-hypothesis", "logn-is-valuation", "unguarded-nat-subtraction",
        "free-cost-field", "foundation-fidelity",
    }
    missing = sorted(expected - rules)
    if missing:
        print(f"faithfulness-lint self-test FAILED: missing rules {missing}", file=sys.stderr)
        return 1
    print(f"faithfulness-lint self-test OK: {len(expected)} rule families exercised")
    return 0


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    scope = parser.add_mutually_exclusive_group()
    scope.add_argument("--all", action="store_true")
    scope.add_argument("--new-waves", action="store_true")
    scope.add_argument("--wave")
    scope.add_argument("--files", nargs="+")
    parser.add_argument("--check", action="store_true",
                        help="fail on findings not present in the allowlist")
    parser.add_argument("--json", action="store_true")
    parser.add_argument("--max-findings", type=int, default=60)
    parser.add_argument("--validate", action="store_true")
    args = parser.parse_args(argv)

    if args.validate:
        return validate()
    if args.files:
        files = [Path(p) if Path(p).is_absolute() else ROOT / p for p in args.files]
    elif args.wave:
        files = wave_files(wave=args.wave)
    elif args.new_waves:
        files = wave_files(new_only=True)
    else:
        files = all_conjecture_files()

    missing_files = [str(p) for p in files if not p.is_file()]
    if missing_files:
        print(f"faithfulness-lint: missing files: {missing_files}", file=sys.stderr)
        return 2

    watchlist = registry_watchlist()
    findings: list[Finding] = []
    for path in files:
        rel = str(path.relative_to(ROOT))
        findings.extend(lint_source(rel, path.read_text(), watchlist))

    allowlist = load_allowlist()
    stale = sorted(set(allowlist) - {f.key for f in findings})
    active = [f for f in findings if f.key not in allowlist]
    if args.json:
        print(json.dumps({
            "files": len(files),
            "findings": [f.__dict__ | {"key": f.key, "allowlisted": f.key in allowlist}
                         for f in findings],
            "stale_allowlist": stale,
        }, indent=2))
    else:
        counts = Counter(f.rule for f in active)
        mode = "hard" if args.check else "warning"
        print(f"faithfulness-lint ({mode}): {len(files)} files, {len(active)} active findings"
              + (f", {len(findings) - len(active)} allowlisted" if findings else ""))
        for finding in active[:args.max_findings]:
            print(f"  {finding.path}:{finding.line}: [{finding.rule}] "
                  f"{finding.statement}: {finding.message}")
        if len(active) > args.max_findings:
            print(f"  ... {len(active) - args.max_findings} more findings omitted")
        if counts:
            print("  by rule: " + ", ".join(f"{rule}={counts[rule]}" for rule in sorted(counts)))
        if stale:
            print(f"  stale allowlist entries: {stale}")

    if stale and args.check:
        return 1
    return 1 if args.check and active else 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
