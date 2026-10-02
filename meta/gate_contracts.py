#!/usr/bin/env python3
"""Shared, testable contracts used by the milestone acceptance gate."""

from __future__ import annotations

import re
import sys
from collections.abc import Iterable


IDENT = r"[A-Za-z_][A-Za-z0-9_']*"
IDENT_RE = re.compile(rf"^{IDENT}$")
IDENT_CHARS = "A-Za-z0-9_'"
PROOF_DECL_RE = re.compile(
    rf"^\s*(?:(?:Local|Global|Polymorphic|Monomorphic|Program)\s+)*"
    rf"(?:Lemma|Theorem|Corollary|Proposition|Fact|Remark|Example)\s+({IDENT})\b",
    re.M,
)
CANDIDATE_DECL_RE = re.compile(
    rf"^\s*(?:(?:Local|Global|Polymorphic|Monomorphic|Program)\s+)*"
    rf"(?:Lemma|Theorem|Corollary|Proposition|Fact|Remark|Example|"
    rf"Definition|Let|Instance)\s+({IDENT})\b",
    re.M,
)
DEFINITION_DECL_RE = re.compile(
    rf"^\s*(?:(?:Local|Global|Polymorphic|Monomorphic|Program)\s+)*"
    rf"(?:Definition|Let)\s+({IDENT})\b",
    re.M,
)
NOTATION_ALIAS_RE = re.compile(
    rf"^\s*(?:(?:Local|Global)\s+)*Notation\s+({IDENT})\s*:=",
    re.M,
)


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


def comment_spans(src: str) -> list[tuple[int, int]]:
    """Offsets ``(start, end)`` of every top-level Rocq comment (``end`` exclusive).

    Same nesting walk as :func:`strip_comments`; nested comments are folded into the
    enclosing top-level span, and an unterminated comment yields no span. Used by the
    statement-doc gate to pick the comment attached to a declaration.
    """
    spans: list[tuple[int, int]] = []
    i = depth = 0
    start = -1
    while i < len(src):
        if src.startswith("(*", i):
            if depth == 0:
                start = i
            depth += 1
            i += 2
        elif depth and src.startswith("*)", i):
            depth -= 1
            i += 2
            if depth == 0:
                spans.append((start, i))
        else:
            i += 1
    return spans


def sentence_from(src: str, start: int) -> str:
    """Return the Rocq command beginning at ``start`` through its final period."""
    i = start
    while True:
        j = src.find(".", i)
        if j < 0:
            return src[start:]
        nxt = src[j + 1:j + 2]
        if not nxt or nxt.isspace():
            return src[start:j + 1]
        i = j + 1


def mentions(command: str, name: str) -> bool:
    return bool(re.search(
        rf"(?<![{IDENT_CHARS}]){re.escape(name)}(?![{IDENT_CHARS}])", command
    ))


def declaration_commands(src: str, pattern: re.Pattern[str]) -> dict[str, str]:
    clean = strip_comments(src)
    return {
        match.group(1): sentence_from(clean, match.start())
        for match in pattern.finditer(clean)
    }


def faithfulness_candidate_records(
    sources: Iterable[tuple[str, str, str]], target_names: Iterable[str]
) -> dict[str, list[tuple[str, str, str]]]:
    """Find proof declarations that may be convertible to a forbidden row type.

    Direct textual references are supplemented by a fixed-point over transparent
    ``Definition``/``Let`` aliases and simple identifier ``Notation`` aliases.
    The later Rocq ``Fail Check`` remains the authority, so this intentionally
    conservative scan cannot create a semantic false positive.
    """
    parsed: list[tuple[str, str, dict[str, str], dict[str, str]]] = []
    aliases: list[tuple[str, str]] = []
    for module, rel, src in sources:
        proofs = declaration_commands(src, CANDIDATE_DECL_RE)
        definitions = declaration_commands(src, DEFINITION_DECL_RE)
        parsed.append((module, rel, proofs, definitions))
        aliases.extend(definitions.items())
        aliases.extend(declaration_commands(src, NOTATION_ALIAS_RE).items())

    candidates: dict[str, list[tuple[str, str, str]]] = {}
    for target in target_names:
        reachable = {target}
        changed = True
        while changed:
            changed = False
            for alias, command in aliases:
                if alias not in reachable and any(mentions(command, name) for name in reachable):
                    reachable.add(alias)
                    changed = True

        found: list[tuple[str, str, str]] = []
        for module, rel, proofs, _definitions in parsed:
            for proof, command in proofs.items():
                if any(mentions(command, name) for name in reachable):
                    found.append((f"{module}.{proof}", rel, proof))
        candidates[target] = found
    return candidates


def forbidden_exact_types(
    status: str,
    statement: str,
    candidate: str,
    verified_resolutions: set[tuple[str, str, str]],
) -> list[tuple[str, str]]:
    """Keep every original probe except an exact, freshly verified resolution.

    A resolution authorizes one constant in one direction for one statement.
    Neither the source row's status nor another proof constant is exempted.
    """
    cases = []
    if status != "disproved" and (statement, candidate, "disprove") not in verified_resolutions:
        cases.append(("unconditional-refutation", f"~ {statement}"))
    if status in ("open", "partial") and (statement, candidate, "prove") not in verified_resolutions:
        cases.append(("direct-proof-undecided", statement))
    return cases


def incl_flags_from_cqp(cqp_txt: str) -> list[str]:
    """``-Q``/``-R`` include flags of a ``_CoqProject``, as an argv list.

    Copied verbatim (behaviour-wise) from the private helper of
    ``check_milestone.py`` so that ``check_edges.py`` can compile a probe with a
    package's own logical paths without importing the milestone gate. Returned as
    a list so no path is ever interpolated into a shell string.
    """
    incl_flags: list[str] = []
    for m in re.findall(r"-[QR]\s+\S+\s+\S+", cqp_txt):
        incl_flags += m.split()
    return incl_flags


def namespace_from_cqp(cqp_txt: str) -> str | None:
    """The package's own logical namespace: the ``-R theories <NS>`` binding."""
    m = re.search(r"^\s*-R\s+theories\s+(\S+)", cqp_txt, re.M)
    return m.group(1) if m else None


def validate_grounding_contract(
    slug: str,
    formal_name: str,
    helpers: list[str],
    grounding: object,
    grounding_src: str,
) -> tuple[list[tuple[str, str]], list[str]]:
    """Validate certificate metadata and return exact ``(theorem, claim)`` checks.

    Each certificate names a proposition-valued claim and a proof theorem.  Its
    explicit references must anchor that claim to the row or to a classified
    helper.  ``check_milestone.py`` asks Rocq to verify both ``claim : Prop`` and
    ``theorem : claim`` and then runs ``Print Assumptions theorem``.
    """
    prefix = f"{slug}: grounding"
    errors: list[str] = []
    checks: list[tuple[str, str]] = []
    if not isinstance(grounding, dict):
        return [], [f"{slug}: missing grounding metadata object"]

    clean = strip_comments(grounding_src)
    proofs = declaration_commands(clean, PROOF_DECL_RE)
    claims = declaration_commands(clean, DEFINITION_DECL_RE)
    allowed_references = {formal_name, *helpers}
    covered_helpers: set[str] = set()

    def validate_one(label: str, value: object, *, helper_certificate: bool) -> None:
        nonlocal covered_helpers
        item_prefix = f"{prefix}.{label}"
        if not isinstance(value, dict):
            errors.append(f"{item_prefix} must be a certificate object")
            return
        missing = [field for field in ("theorem", "claim", "references") if field not in value]
        if missing:
            errors.append(f"{item_prefix} misses {missing}")
            return
        theorem, claim, references = (
            value.get("theorem"), value.get("claim"), value.get("references")
        )
        if not isinstance(theorem, str) or not IDENT_RE.fullmatch(theorem):
            errors.append(f"{item_prefix}.theorem must be one unqualified Rocq identifier")
            return
        if not isinstance(claim, str) or not IDENT_RE.fullmatch(claim):
            errors.append(f"{item_prefix}.claim must be one unqualified Rocq identifier")
            return
        if theorem == claim:
            errors.append(f"{item_prefix}: theorem and claim must be distinct declarations")
        if not isinstance(references, list) or not references or not all(
            isinstance(ref, str) and IDENT_RE.fullmatch(ref) for ref in references
        ):
            errors.append(f"{item_prefix}.references must be a nonempty identifier list")
            return
        refs = set(references)
        unknown = sorted(refs - allowed_references)
        if unknown:
            errors.append(f"{item_prefix}: unknown references {unknown}")
        helper_refs = refs & set(helpers)
        if helper_certificate:
            if not helper_refs:
                errors.append(f"{item_prefix} must reference at least one classified helper")
            covered_helpers.update(helper_refs)
        elif formal_name not in refs:
            errors.append(f"{item_prefix} must reference row statement {formal_name}")

        if theorem not in proofs:
            errors.append(f"{item_prefix}: theorem is not a proof declaration: {theorem}")
        if claim not in claims:
            errors.append(f"{item_prefix}: claim is not a Definition/Let declaration: {claim}")
        else:
            absent = sorted(ref for ref in refs if not mentions(claims[claim], ref))
            if absent:
                errors.append(f"{item_prefix}: claim {claim} does not mention {absent}")
        if theorem in proofs and claim in claims and not mentions(proofs[theorem], claim):
            errors.append(f"{item_prefix}: theorem declaration does not name claim {claim}")
        checks.append((theorem, claim))

    validate_one("hyp_inhabited", grounding.get("hyp_inhabited"), helper_certificate=False)
    validate_one("not_trivially_true", grounding.get("not_trivially_true"), helper_certificate=False)
    helper_specs = grounding.get("helper_sanity")
    if not isinstance(helper_specs, list):
        errors.append(f"{prefix}.helper_sanity must be a list of certificate objects")
    else:
        for index, spec in enumerate(helper_specs):
            validate_one(f"helper_sanity[{index}]", spec, helper_certificate=True)
    missing_helpers = sorted(set(helpers) - covered_helpers)
    if missing_helpers:
        errors.append(f"{prefix}: helpers lack sanity certificates {missing_helpers}")
    if not helpers and helper_specs:
        errors.append(f"{prefix}.helper_sanity must be empty when the wave has no helpers")
    return checks, errors


def validate_self_test() -> int:
    alias_source = """
Definition open_statement : Prop := True.
Definition statement_alias : Prop := open_statement.
Definition second_alias : Prop := statement_alias.
Lemma hidden_proof : second_alias. Proof. exact I. Qed.
Definition hidden_definition : second_alias := I.
Notation hidden_type := second_alias.
Lemma hidden_notation_proof : hidden_type. Proof. exact I. Qed.
"""
    candidates = faithfulness_candidate_records(
        [("Fixture", "fixture.v", alias_source)], ["open_statement"]
    )
    candidate_names = {record[2] for record in candidates["open_statement"]}
    alias_ok = {
        "hidden_proof", "hidden_definition", "hidden_notation_proof"
    } <= candidate_names

    grounding_source = """
Definition row_hyp_claim : Prop := row_statement -> row_statement.
Lemma row_hyp_proof : row_hyp_claim. Proof. firstorder. Qed.
Definition row_nontrivial_claim : Prop := row_statement -> row_statement.
Lemma row_nontrivial_proof : row_nontrivial_claim. Proof. firstorder. Qed.
Definition helper_claim : Prop := helper_pred = helper_pred.
Lemma helper_proof : helper_claim. Proof. reflexivity. Qed.
Definition unrelated_number : nat := 0.
"""
    good = {
        "hyp_inhabited": {"theorem": "row_hyp_proof", "claim": "row_hyp_claim",
                           "references": ["row_statement"]},
        "not_trivially_true": {"theorem": "row_nontrivial_proof",
                                "claim": "row_nontrivial_claim",
                                "references": ["row_statement"]},
        "helper_sanity": [{"theorem": "helper_proof", "claim": "helper_claim",
                            "references": ["helper_pred"]}],
    }
    checks, good_errors = validate_grounding_contract(
        "fixture", "row_statement", ["helper_pred"], good, grounding_source
    )
    bad = dict(good)
    bad["hyp_inhabited"] = {
        "theorem": "unrelated_number", "claim": "row_hyp_claim",
        "references": ["row_statement"],
    }
    _bad_checks, bad_errors = validate_grounding_contract(
        "fixture", "row_statement", ["helper_pred"], bad, grounding_source
    )
    grounding_ok = len(checks) == 3 and not good_errors \
        and any("not a proof declaration" in error for error in bad_errors)
    ok = alias_ok and grounding_ok
    print(f"gate-contract self-test {'OK' if ok else 'FAILED'}")
    if not ok:
        print(f"  alias_ok={alias_ok} good_errors={good_errors} bad_errors={bad_errors}",
              file=sys.stderr)
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(validate_self_test())
