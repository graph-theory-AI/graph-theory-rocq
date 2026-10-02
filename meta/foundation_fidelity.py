#!/usr/bin/env python3
"""Validate and summarize the audited foundation-fidelity registry."""

from __future__ import annotations

import argparse
import json
import re
import sys
from collections import Counter
from pathlib import Path

from family_registry import RegistryError, load_fidelity_registry

ROOT = Path(__file__).resolve().parents[1]
META = ROOT / "meta"
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
    return load_fidelity_registry(ROOT)


def selected_primitives(spec: dict) -> set[str]:
    """Return only explicitly enrolled primitives; never infer trust from a file."""
    return set(spec.get("audited_primitives", [])) | set(spec.get("overrides", {}))


def strip_comments(src: str) -> str:
    """Remove nested Rocq comments before looking for declarations."""
    out: list[str] = []
    i = depth = 0
    while i < len(src):
        if src.startswith("(*", i):
            depth += 1
            i += 2
        elif depth and src.startswith("*)", i):
            depth -= 1
            i += 2
        elif depth:
            out.append("\n" if src[i] == "\n" else " ")
            i += 1
        else:
            out.append(src[i])
            i += 1
    return "".join(out)


def expand_registry(data: dict | None = None) -> tuple[list[dict], list[str]]:
    if data is None:
        try:
            data = load_registry()
        except RegistryError as exc:
            return [], [str(exc)]
    allowed = set(data.get("verdicts", []))
    entries: list[dict] = []
    errors: list[str] = []
    seen: set[str] = set()

    if data.get("schema_version") != 2:
        errors.append("schema_version must be 2")
    if allowed != {"FAITHFUL", "LIGHTWEIGHT", "BROKEN"}:
        errors.append("verdicts must be exactly FAITHFUL/LIGHTWEIGHT/BROKEN")

    for module, spec in sorted(data.get("modules", {}).items()):
        rel = spec.get("path", "")
        path = ROOT / rel
        if not path.is_file():
            errors.append(f"{module}: path does not exist: {rel}")
            continue
        src = strip_comments(path.read_text())
        declarations = set(DECL_RE.findall(src))
        proofs = set(PROOF_RE.findall(src))
        default = spec.get("default")
        overrides = spec.get("overrides", {})

        audited = spec.get("audited_primitives", [])
        if default is not None and "audited_primitives" not in spec:
            errors.append(
                f"{module}: default verdict requires an explicit audited_primitives list"
            )
        if not isinstance(audited, list) or not all(isinstance(name, str) for name in audited):
            errors.append(f"{module}: audited_primitives must be a string list")
            audited = []
        if len(audited) != len(set(audited)):
            errors.append(f"{module}: audited_primitives contains duplicates")
        unknown_audited = sorted(set(audited) - declarations)
        if unknown_audited:
            errors.append(f"{module}: audited_primitives name undeclared primitives: "
                          f"{unknown_audited}")

        unknown = sorted(set(overrides) - declarations)
        if unknown:
            errors.append(f"{module}: overrides name undeclared primitives: {unknown}")
        missing_evidence = sorted(set(spec.get("machine_evidence", [])) - proofs)
        if missing_evidence:
            errors.append(f"{module}: machine_evidence names are not proof declarations: "
                          f"{missing_evidence}")

        # A module default is only shorthand for the explicitly audited names.
        # Newly added declarations remain unaudited until this list is updated.
        selected = selected_primitives(spec)
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
    parser.add_argument("--validate", action="store_true")
    args = parser.parse_args(argv)

    if args.validate:
        fixture = {
            "default": {"verdict": "FAITHFUL", "note": "fixture"},
            "audited_primitives": ["audited"],
            "overrides": {"exception": {"verdict": "BROKEN", "note": "fixture"}},
        }
        selected = selected_primitives(fixture)
        ok = selected == {"audited", "exception"} and "new_unreviewed" not in selected
        print(f"foundation-fidelity self-test {'OK' if ok else 'FAILED'}")
        return 0 if ok else 1

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
