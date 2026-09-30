#!/usr/bin/env python3
"""Shared, testable contracts used by the milestone acceptance gate."""

from __future__ import annotations

import re
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
