#!/usr/bin/env python3
"""Repository-wide classification of the helpers outside every registered family (G-4).

meta/library_helper_classification.json classifies every residual repeated
normalized name (a name repeated in the helper inventory and claimed by no
family's normalized_names) and every residual repeated body shape (a repeated
non-empty body whose members are in no repeated-name group and are no family's
source definition). Singletons and the empty-body group are out of scope; the
file's header says so. Each entry, or each of its disjoint parts, has a class:

  paper_specific    different notions or carriers behind one name, or one
                    paper's vocabulary: kept local;
  family_companion  a companion, bridge or projection of a REGISTERED family
                    (Marc's "compatibility alias"); each member lies outside
                    every family's source_definitions and references the
                    family's source definitions, canonical or API names;
  candidate_family  a reusable notion not yet registered, with its proposed
                    family id and a milestone of the file's milestones table;
                    with `joins_registered: true`, a further unmigrated copy of
                    a REGISTERED family's notion (family_id names that family).

The check is toolchain-free and runs from `library_inventory.py --check`.
"""
from __future__ import annotations

from collections import Counter
import json
from pathlib import Path
import re

import library_inventory as INV

CLASSIFICATION = INV.META / "library_helper_classification.json"
CLASSES = {"paper_specific", "family_companion", "candidate_family"}
KINDS = {"companion", "bridge", "projection"}
EMPTY_BODY = INV.sha256("")
ID_RE = re.compile(r"[a-z0-9][a-z0-9-]*")
PART_KEYS = {
    "paper_specific": {"class", "reason", "members"},
    "family_companion": {"class", "reason", "members", "family", "kind"},
    "candidate_family": {"class", "reason", "members", "family_id", "milestone"},
}


def residual_names(inventory: dict, registry: dict[str, dict]) -> dict[str, list[str]]:
    claimed = {name for spec in registry.values() for name in spec.get("normalized_names", [])}
    return {name: members for name, members in inventory["groups"]["normalized_name"].items()
            if name not in claimed}


def residual_body_shapes(inventory: dict, registry: dict[str, dict]) -> dict[str, list[str]]:
    named = {member for members in inventory["groups"]["normalized_name"].values() for member in members}
    sources = {name for spec in registry.values() for name in spec.get("source_definitions", [])}
    out = {}
    for shape, members in inventory["groups"]["body_shape_hash"].items():
        if shape == EMPTY_BODY:
            continue
        residual = sorted(member for member in members if member not in named and member not in sources)
        if residual:
            out[shape] = residual
    return out


def family_names(spec: dict) -> set[str]:
    """The short names a family_companion may reference: sources, canonical, API."""
    qualified = [*spec.get("source_definitions", []), spec.get("canonical_name") or "", *spec.get("api_theorems", [])]
    return {name.rsplit(".", 1)[-1] for name in qualified if name}


def declaration_text(helper: dict, cache: dict[str, str]) -> str:
    """The comment-stripped command of an inventory helper, found by its line."""
    path = helper["path"]
    if path not in cache:
        cache[path] = INV.strip_comments((INV.ROOT / path).read_text())
    clean = cache[path]
    for match in INV.DECL_RE.finditer(clean):
        if match.group(2) == helper["name"] and clean.count("\n", 0, match.start()) + 1 == helper["line"]:
            return clean[match.start():INV.sentence_end(clean, match.start())]
    raise ValueError(f"{helper['qualified_name']}: declaration not found at {path}:{helper['line']}")


def references(text: str, names: set[str]) -> bool:
    return any(re.search(rf"(?<![A-Za-z0-9_']){re.escape(name)}(?![A-Za-z0-9_'])", text) for name in names)


def check_part(where: str, part: object, expected: list[str] | None, registry: dict[str, dict],
               milestones: dict, helpers: dict[str, dict], cache: dict[str, str],
               used: set[str], errors: list[str]) -> list[str]:
    if not isinstance(part, dict):
        errors.append(f"{where}: an entry or part must be an object")
        return []
    cls = part.get("class")
    if cls not in CLASSES:
        errors.append(f"{where}: unknown class {cls!r}")
        members = part.get("members")
        return [m for m in members if isinstance(m, str)] if isinstance(members, list) else []
    optional = {"joins_registered"} if cls == "candidate_family" else set()
    if not PART_KEYS[cls] <= set(part) <= PART_KEYS[cls] | optional:
        errors.append(f"{where}: {cls} needs exactly the keys {sorted(PART_KEYS[cls])}"
                      + (f" (optionally {sorted(optional)})" if optional else ""))
    reason = part.get("reason")
    if not isinstance(reason, str) or len(reason.strip()) < 20:
        errors.append(f"{where}: reason must contain at least 20 characters")
    members = part.get("members")
    if not isinstance(members, list) or not members or not all(isinstance(m, str) for m in members) \
            or members != sorted(set(members)):
        errors.append(f"{where}: members must be a non-empty sorted list of distinct names")
        return [m for m in members if isinstance(m, str)] if isinstance(members, list) else []
    if expected is not None and members != expected:
        errors.append(f"{where}: members {members} != the inventory group {expected}")
    if cls == "family_companion":
        family = part.get("family")
        if part.get("kind") not in KINDS:
            errors.append(f"{where}: kind must be one of {sorted(KINDS)}")
        if family not in registry:
            errors.append(f"{where}: unknown registered family {family!r}")
        else:
            sources = {name for spec in registry.values() for name in spec.get("source_definitions", [])}
            names = family_names(registry[family])
            for member in members:
                if member in sources:
                    errors.append(f"{where}: {member} is a family source definition, not a companion")
                elif member not in helpers:
                    errors.append(f"{where}: {member} is not an inventory helper")
                else:
                    try:
                        text = declaration_text(helpers[member], cache)
                    except (OSError, ValueError) as exc:
                        errors.append(f"{where}: {exc}")
                        continue
                    if not references(text, names):
                        errors.append(f"{where}: {member} references no source, canonical or API name of {family}")
    if cls == "candidate_family":
        family_id = part.get("family_id")
        joins = part.get("joins_registered", False)
        if joins is not True and joins is not False:
            errors.append(f"{where}: joins_registered must be true or false")
        elif joins and family_id not in registry:
            errors.append(f"{where}: joins_registered needs family_id to name a registered family")
        elif not joins and (not isinstance(family_id, str) or not ID_RE.fullmatch(family_id) or family_id in registry):
            errors.append(f"{where}: family_id must be a new lower-case family id")
        milestone = part.get("milestone")
        if milestone not in milestones:
            errors.append(f"{where}: milestone {milestone!r} is not in the milestones table")
        else:
            used.add(milestone)
    return members


def check_entry(where: str, entry: object, expected: list[str], registry: dict[str, dict],
                milestones: dict, helpers: dict[str, dict], cache: dict[str, str],
                used: set[str], errors: list[str], by_class: Counter) -> None:
    if isinstance(entry, dict) and "parts" in entry:
        parts = entry["parts"]
        if set(entry) != {"parts"} or not isinstance(parts, list) or len(parts) < 2:
            errors.append(f"{where}: a mixed entry has only `parts`, a list of at least 2 parts")
            return
        seen: list[str] = []
        for i, part in enumerate(parts):
            seen.extend(check_part(f"{where} part {i}", part, None, registry, milestones, helpers, cache, used, errors))
            if isinstance(part, dict) and part.get("class") in CLASSES:
                by_class[part["class"]] += 1
        if len(seen) != len(set(seen)):
            errors.append(f"{where}: parts overlap")
        if sorted(set(seen)) != expected:
            errors.append(f"{where}: the union of the parts != the inventory group {expected}")
        by_class["mixed"] += 1
        return
    check_part(where, entry, expected, registry, milestones, helpers, cache, used, errors)
    if isinstance(entry, dict) and entry.get("class") in CLASSES:
        by_class[entry["class"]] += 1


def validate_classification(inventory: dict, registry: dict[str, dict], path: Path = CLASSIFICATION,
                            also_used: set[str] = frozenset()) -> tuple[list[str], str]:
    """Errors, and the counts line printed by --check. also_used: milestone ids cited elsewhere (G-5)."""
    errors: list[str] = []
    try:
        data = INV.load_json(path)
    except (OSError, ValueError) as exc:
        return [f"cannot load {path.name}: {exc}"], ""
    where = path.name
    if data.get("schema_version") != 1:
        errors.append(f"{where}: schema_version must be 1")
    if not isinstance(data.get("header"), list) or not all(isinstance(line, str) for line in data["header"]):
        errors.append(f"{where}: header must be a list of lines")
    milestones = data.get("milestones")
    if not isinstance(milestones, dict):
        errors.append(f"{where}: milestones must be an object")
        milestones = {}
    for key, value in sorted(milestones.items()):
        if not ID_RE.fullmatch(key):
            errors.append(f"{where}: milestone id {key!r} must be lower-case")
        if not isinstance(value, dict) or set(value) != {"description", "owner", "after"} \
                or not all(isinstance(value[k], str) and value[k].strip() for k in value) \
                or len(value["description"].strip()) < 20:
            errors.append(f"{where}: milestone {key} needs description (>= 20 characters), owner and after")
    helpers = {helper["qualified_name"]: helper for helper in inventory["helpers"]}
    cache: dict[str, str] = {}
    used: set[str] = set()
    counts = {}
    for section, residual in (("names", residual_names(inventory, registry)),
                              ("body_shapes", residual_body_shapes(inventory, registry))):
        entries = data.get(section)
        if not isinstance(entries, dict):
            errors.append(f"{where}: {section} must be an object")
            entries = {}
        for key in sorted(set(residual) - set(entries)):
            errors.append(f"{where}: {section}: residual group {key} is unclassified")
        for key in sorted(set(entries) - set(residual)):
            errors.append(f"{where}: {section}: stale entry {key} (claimed by a family or no longer repeated)")
        by_class: Counter = Counter()
        for key in sorted(set(entries) & set(residual)):
            check_entry(f"{where}: {section}.{key}", entries[key], residual[key], registry, milestones,
                        helpers, cache, used, errors, by_class)
        counts[section] = (len(residual), by_class)
    for key in sorted(set(milestones) - used - set(also_used)):
        errors.append(f"{where}: milestone {key} is referenced by no entry (stale)")
    line = "helper classification: " + "; ".join(
        f"{section} {n} ({', '.join(f'{c} {k}' for c, k in sorted(by.items()))})"
        for section, (n, by) in counts.items()) + f"; {len(milestones)} milestones"
    return errors, line


def alias_milestone_citations(data: object) -> set[str]:
    """The milestone ids cited by the file's G-5 alias_milestones (remove-after:<id>), so that the stand-alone G-4 check does not
    call a milestone stale that only G-5 cites; their validation stays library_inventory.py --check's (validate_milestones)."""
    authored = data.get("alias_milestones") if isinstance(data, dict) else None
    if not isinstance(authored, dict):
        return set()
    return {value.split(":", 1)[1] for value in authored.values()
            if isinstance(value, str) and value.startswith("remove-after:")}


if __name__ == "__main__":
    import sys
    from family_registry import load_library_registry
    inventory = INV.build_inventory()
    try:
        cited = alias_milestone_citations(INV.load_json(CLASSIFICATION))
    except ValueError:
        cited = set()   # validate_classification reports the unreadable file itself
    problems, summary = validate_classification(inventory, load_library_registry(INV.ROOT)["primitives"], also_used=cited)
    print(summary)
    for problem in problems:
        print(f"  ERROR: {problem}", file=sys.stderr)
    raise SystemExit(1 if problems else 0)
