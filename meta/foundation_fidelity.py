#!/usr/bin/env python3
"""Validate and summarize the audited foundation-fidelity registry."""

from __future__ import annotations

import argparse
import json
import re
import sys
from collections import Counter
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
META = ROOT / "meta"
REGISTRY = META / "foundation_fidelity.json"
DECL_RE = re.compile(
    r"^\s*(?:Local\s+|Global\s+|Polymorphic\s+|Program\s+)*"
    r"(?:Definition|Inductive|CoInductive|Record|Class|Fixpoint|CoFixpoint)\s+"
    r"([A-Za-z_][A-Za-z0-9_']*)\b",
    re.M,
)
PROOF_RE = re.compile(
    r"^\s*(?:Local\s+|Global\s+|Polymorphic\s+|Program\s+)*"
    r"(?:Lemma|Theorem|Corollary|Proposition|Fact|Remark)\s+"
    r"([A-Za-z_][A-Za-z0-9_']*)\b",
    re.M,
)


def load_registry() -> dict:
    return json.loads(REGISTRY.read_text())


def expand_registry(data: dict | None = None) -> tuple[list[dict], list[str]]:
    data = data or load_registry()
    allowed = set(data.get("verdicts", []))
    entries: list[dict] = []
    errors: list[str] = []
    seen: set[str] = set()

    if data.get("schema_version") != 1:
        errors.append("schema_version must be 1")
    if allowed != {"FAITHFUL", "LIGHTWEIGHT", "BROKEN"}:
        errors.append("verdicts must be exactly FAITHFUL/LIGHTWEIGHT/BROKEN")

    for module, spec in sorted(data.get("modules", {}).items()):
        rel = spec.get("path", "")
        path = ROOT / rel
        if not path.is_file():
            errors.append(f"{module}: path does not exist: {rel}")
            continue
        src = path.read_text()
        declarations = set(DECL_RE.findall(src))
        proofs = set(PROOF_RE.findall(src))
        default = spec.get("default")
        overrides = spec.get("overrides", {})

        unknown = sorted(set(overrides) - declarations)
        if unknown:
            errors.append(f"{module}: overrides name undeclared primitives: {unknown}")
        missing_evidence = sorted(set(spec.get("machine_evidence", [])) - proofs)
        if missing_evidence:
            errors.append(f"{module}: machine_evidence names are not proof declarations: "
                          f"{missing_evidence}")

        selected = declarations if default is not None else set(overrides)
        for primitive in sorted(selected):
            verdict_spec = overrides.get(primitive, default)
            verdict = (verdict_spec or {}).get("verdict")
            note = (verdict_spec or {}).get("note", "")
            qname = f"{module}.{primitive}"
            if verdict not in allowed:
                errors.append(f"{qname}: invalid or missing verdict {verdict!r}")
                continue
            if not note:
                errors.append(f"{qname}: missing audit note")
            if qname in seen:
                errors.append(f"duplicate registry primitive {qname}")
            seen.add(qname)
            entries.append({
                "module": module,
                "primitive": primitive,
                "qualified_name": qname,
                "path": rel,
                "verdict": verdict,
                "note": note,
                "machine_evidence": list(spec.get("machine_evidence", [])),
            })
    return entries, errors


def verdicts_by_primitive(data: dict | None = None) -> dict[str, list[dict]]:
    entries, errors = expand_registry(data)
    if errors:
        raise ValueError("; ".join(errors))
    out: dict[str, list[dict]] = {}
    for entry in entries:
        out.setdefault(entry["primitive"], []).append(entry)
    return out


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args(argv)

    entries, errors = expand_registry()
    counts = Counter(e["verdict"] for e in entries)
    if args.json:
        print(json.dumps({"counts": dict(counts), "entries": entries, "errors": errors}, indent=2))
    else:
        print("foundation-fidelity registry: "
              + ", ".join(f"{v.lower()}={counts[v]}"
                           for v in ("FAITHFUL", "LIGHTWEIGHT", "BROKEN")))
        for entry in entries:
            if entry["verdict"] != "FAITHFUL":
                print(f"  {entry['verdict']:11s} {entry['qualified_name']}: {entry['note']}")
        for error in errors:
            print(f"  ERROR: {error}", file=sys.stderr)
    return 1 if errors else 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
