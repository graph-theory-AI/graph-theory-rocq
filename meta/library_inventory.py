#!/usr/bin/env python3
"""Inventory conjecture-local helpers and enforce prospective ownership metadata.

The committed inventory is a deterministic snapshot of non-statement declarations
in conjecture source files. Legacy duplicate families are reported as warnings.
For prospective v2 waves, every helper must be explicitly paper-specific or a
registered compatibility alias.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
from collections import Counter, defaultdict
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
META = ROOT / "meta"
INVENTORY = META / "library_helper_inventory.json"
REGISTRY = META / "library_primitives.json"
POLICY = META / "faithfulness_policy.json"
WAVES = META / "v2_statement_waves.json"

DECL_RE = re.compile(
    r"^\s*(?:(?:Local|Global|Polymorphic|Monomorphic|Program)\s+)*"
    r"(Definition|Let|Fixpoint|CoFixpoint|Inductive|CoInductive|Record|Variant|Class|"
    r"Instance|Lemma|Theorem|Corollary|Proposition|Fact|Remark|Example)\s+"
    r"([A-Za-z_][A-Za-z0-9_']*)\b",
    re.M,
)
REPOSITORY_DECL_RE = re.compile(
    r"^\s*(?:(?:Local|Global|Polymorphic|Monomorphic|Program)\s+)*"
    r"(?:Definition|Let|Fixpoint|CoFixpoint|Inductive|CoInductive|Record|Variant|Class|"
    r"Instance|Lemma|Theorem|Corollary|Proposition|Fact|Remark|Example)\s+"
    r"([A-Za-z_][A-Za-z0-9_']*)\b",
    re.M,
)
IDENT_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_']*")
WAVE_PREFIX_RE = re.compile(r"^(?:x|xe)\d+_", re.I)
WAVE_REF_RE = re.compile(r"\b(?:x|xe)\d+_([A-Za-z_][A-Za-z0-9_']*)", re.I)
SKIP_FILE_PREFIXES = (
    "grounding_", "implications_", "_assum_", "_faith_", "scratch_", "gcheck",
)
ALLOWED_STATUSES = {
    "proposed", "auditing", "canonical", "migrating", "deprecated", "complete",
}
ALLOWED_FIDELITY = {"PENDING", "FAITHFUL", "LIGHTWEIGHT", "BROKEN"}
ALLOWED_OWNERSHIP = {"paper_specific", "compatibility_alias"}


def sha256(text: str) -> str:
    return hashlib.sha256(text.encode()).hexdigest()


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


def normalize_space(text: str) -> str:
    return " ".join(text.split())


def normalized_name(name: str) -> str:
    return WAVE_PREFIX_RE.sub("", name)


def normalized_shape(text: str) -> str:
    return normalize_space(WAVE_REF_RE.sub(r"\1", text))


def is_manifest_statement(name: str, statement_names: set[str]) -> bool:
    return name in statement_names


def conjecture_files() -> list[Path]:
    return sorted(
        path
        for path in ROOT.glob("*/theories/conjectures/*.v")
        if not path.name.startswith(SKIP_FILE_PREFIXES)
    )


def package_namespaces() -> dict[str, str]:
    sys.path.insert(0, str(META))
    import corpus_registry

    return corpus_registry.NS


def manifest_statement_names() -> set[str]:
    sys.path.insert(0, str(META))
    import corpus_registry

    return corpus_registry.all_corpus_nodes()


def repository_declaration_names(namespaces: dict[str, str]) -> set[str]:
    declarations: set[str] = set()
    for path in sorted(ROOT.glob("*/theories/**/*.v")):
        # Concurrent acceptance checks create short-lived probe sources.  They
        # are never repository API and must not perturb registry validation.
        if path.name.startswith(SKIP_FILE_PREFIXES):
            continue
        rel = path.relative_to(ROOT)
        package = rel.parts[0]
        namespace = "GTBase" if package == "base" else namespaces.get(package, package)
        module_parts = rel.parts[2:]
        module_parts = (*module_parts[:-1], Path(module_parts[-1]).stem)
        module = ".".join((namespace, *module_parts))
        clean = strip_comments(path.read_text())
        declarations.update(
            f"{module}.{match.group(1)}"
            for match in REPOSITORY_DECL_RE.finditer(clean)
        )
    return declarations


def parse_file(
    path: Path, namespaces: dict[str, str], statement_names: set[str]
) -> tuple[list[dict], int]:
    src = path.read_text()
    clean = strip_comments(src)
    rel = path.relative_to(ROOT).as_posix()
    package = rel.split("/", 1)[0]
    namespace = namespaces.get(package, package)
    module = f"{namespace}.conjectures.{path.stem}"
    matches = list(DECL_RE.finditer(clean))
    local_names = {match.group(2) for match in matches}
    declarations = []
    for match in matches:
        declarations.append({
            "name": match.group(2),
            "command": clean[match.start():sentence_end(clean, match.start())],
        })
    helpers: list[dict] = []
    statements = 0

    for match in matches:
        kind, name = match.groups()
        # Only actual manifest nodes are statements.  A helper does not escape
        # ownership merely by adopting the conventional `_statement` suffix.
        if is_manifest_statement(name, statement_names):
            statements += 1
            continue
        end = sentence_end(clean, match.start())
        command = clean[match.start():end]
        after_name = command[match.end() - match.start():]
        if ":=" in after_name:
            signature, body = after_name.split(":=", 1)
        else:
            signature, body = after_name, ""
        signature = normalize_space(signature.rstrip("."))
        body = normalize_space(body.rstrip("."))
        dependencies = sorted(
            candidate
            for candidate in local_names
            if candidate != name and re.search(
                rf"(?<![A-Za-z0-9_']){re.escape(candidate)}(?![A-Za-z0-9_'])", command
            )
        )
        consumers = sorted(
            f"{module}.{declaration['name']}"
            for declaration in declarations
            if declaration["name"] != name and re.search(
                rf"(?<![A-Za-z0-9_']){re.escape(name)}(?![A-Za-z0-9_'])",
                declaration["command"],
            )
        )
        helpers.append({
            "qualified_name": f"{module}.{name}",
            "name": name,
            "normalized_name": normalized_name(name),
            "kind": kind,
            "package": package,
            "path": rel,
            "line": clean.count("\n", 0, match.start()) + 1,
            "phase": path.stem if re.fullmatch(r"X\d+", path.stem) else None,
            "signature": signature,
            "signature_shape_hash": sha256(normalized_shape(signature)),
            "body_hash": sha256(body),
            "body_shape_hash": sha256(normalized_shape(body)),
            "declaration_hash": sha256(normalize_space(command)),
            "local_dependencies": dependencies,
            "direct_consumers": consumers,
        })
    return helpers, statements


def grouped(helpers: list[dict], field: str) -> dict[str, list[str]]:
    groups: dict[str, list[str]] = defaultdict(list)
    for helper in helpers:
        groups[helper[field]].append(helper["qualified_name"])
    return {
        key: sorted(names)
        for key, names in sorted(groups.items())
        if len(names) > 1 and key
    }


def build_inventory() -> dict:
    namespaces = package_namespaces()
    statement_names = manifest_statement_names()
    helpers: list[dict] = []
    statement_count = 0
    files = conjecture_files()
    for path in files:
        file_helpers, file_statements = parse_file(path, namespaces, statement_names)
        helpers.extend(file_helpers)
        statement_count += file_statements
    helpers.sort(key=lambda h: (h["path"], h["line"], h["name"]))
    name_groups = grouped(helpers, "normalized_name")
    body_groups = grouped(helpers, "body_shape_hash")
    signature_groups = grouped(helpers, "signature_shape_hash")
    return {
        "schema_version": 1,
        "scope": {
            "glob": "*/theories/conjectures/*.v",
            "excluded_prefixes": list(SKIP_FILE_PREFIXES),
            "excluded_declarations": ["manifest-owned formal_names"],
        },
        "counts": {
            "files": len(files),
            "statements_excluded": statement_count,
            "helpers": len(helpers),
            "x_wave_helpers": sum(bool(WAVE_PREFIX_RE.match(h["name"])) for h in helpers),
            "repeated_normalized_names": len(name_groups),
            "repeated_body_shapes": len(body_groups),
            "repeated_signature_shapes": len(signature_groups),
        },
        "helpers": helpers,
        "groups": {
            "normalized_name": name_groups,
            "body_shape_hash": body_groups,
            "signature_shape_hash": signature_groups,
        },
    }


def load_json(path: Path) -> dict:
    try:
        return json.loads(path.read_text())
    except (OSError, json.JSONDecodeError) as exc:
        raise ValueError(f"cannot load {path.relative_to(ROOT)}: {exc}") from exc


def validate_registry(inventory: dict) -> tuple[dict[str, dict], list[str]]:
    errors: list[str] = []
    try:
        data = load_json(REGISTRY)
    except ValueError as exc:
        return {}, [str(exc)]
    if data.get("schema_version") != 1:
        errors.append("library_primitives.json: schema_version must be 1")
    entries = data.get("primitives")
    if not isinstance(entries, dict):
        return {}, errors + ["library_primitives.json: primitives must be an object"]

    helpers = {h["qualified_name"]: h for h in inventory["helpers"]}
    repository_declarations = repository_declaration_names(package_namespaces())
    claimed: dict[str, str] = {}
    for primitive_id, spec in sorted(entries.items()):
        prefix = f"library_primitives.json:{primitive_id}"
        if not re.fullmatch(r"[a-z][a-z0-9-]*", primitive_id):
            errors.append(f"{prefix}: invalid primitive id")
        if spec.get("status") not in ALLOWED_STATUSES:
            errors.append(f"{prefix}: invalid status {spec.get('status')!r}")
        if spec.get("fidelity") not in ALLOWED_FIDELITY:
            errors.append(f"{prefix}: invalid fidelity {spec.get('fidelity')!r}")
        if spec.get("status") in {"canonical", "migrating", "deprecated", "complete"}:
            canonical_name = spec.get("canonical_name")
            if not canonical_name:
                errors.append(f"{prefix}: canonical_name is required at this status")
            elif canonical_name not in repository_declarations:
                errors.append(
                    f"{prefix}: canonical declaration does not exist: {canonical_name}"
                )
            if spec.get("fidelity") == "PENDING":
                errors.append(f"{prefix}: a public or migrating primitive needs a fidelity verdict")
        if not isinstance(spec.get("owner"), str) or not spec["owner"]:
            errors.append(f"{prefix}: owner is required")
        normalized_names = spec.get("normalized_names")
        if not isinstance(normalized_names, list) or not normalized_names or not all(
            isinstance(name, str) and name for name in normalized_names
        ):
            errors.append(f"{prefix}: normalized_names must be a nonempty string list")
            normalized_names = []
        sources = spec.get("source_definitions")
        if not isinstance(sources, list) or not all(isinstance(name, str) for name in sources):
            errors.append(f"{prefix}: source_definitions must be a string list")
            sources = []
        missing = sorted(set(sources) - set(helpers))
        if missing:
            errors.append(f"{prefix}: source definitions missing from inventory: {missing[:5]}")
        matched = sorted(
            qname for qname, helper in helpers.items()
            if helper["normalized_name"] in normalized_names
        )
        if sorted(sources) != matched:
            errors.append(
                f"{prefix}: source_definitions drift (registered={len(sources)}, "
                f"matched={len(matched)})"
            )
        for qname in sources:
            if qname in claimed:
                errors.append(f"{prefix}: {qname} already claimed by {claimed[qname]}")
            claimed[qname] = primitive_id
        consumers = sorted({
            consumer
            for qname in sources if qname in helpers
            for consumer in helpers[qname]["direct_consumers"]
        })
        if spec.get("consumers_remaining") != len(consumers):
            errors.append(
                f"{prefix}: consumers_remaining must equal current direct consumer count "
                f"{len(consumers)}"
            )
        audit = spec.get("upstream_audit")
        if not isinstance(audit, dict):
            errors.append(f"{prefix}: upstream_audit object is required")
        else:
            for field in ("searched_modules", "result", "note", "audited_at"):
                if field not in audit or not audit[field]:
                    errors.append(f"{prefix}: upstream_audit.{field} is required")
        compatibility = spec.get("compatibility_theorems", [])
        if not isinstance(compatibility, list) or not all(
            isinstance(name, str) and name for name in compatibility
        ):
            errors.append(f"{prefix}: compatibility_theorems must be a string list")
        else:
            missing_compatibility = sorted(
                set(compatibility) - repository_declarations
            )
            if missing_compatibility:
                errors.append(
                    f"{prefix}: compatibility declarations do not exist: "
                    f"{missing_compatibility[:5]}"
                )
            if spec.get("status") in {"migrating", "deprecated", "complete"} \
                    and not compatibility:
                errors.append(
                    f"{prefix}: migrating or migrated primitive needs compatibility theorems"
                )
        api_theorems = spec.get("api_theorems", [])
        if not isinstance(api_theorems, list) or not all(
            isinstance(name, str) and name for name in api_theorems
        ):
            errors.append(f"{prefix}: api_theorems must be a string list")
        else:
            missing_api = sorted(set(api_theorems) - repository_declarations)
            if missing_api:
                errors.append(
                    f"{prefix}: API theorem declarations do not exist: {missing_api[:5]}"
                )
    return entries, errors


def validate_policy() -> list[str]:
    errors: list[str] = []
    whole_policy = load_json(POLICY)
    if whole_policy.get("schema_version") != 2:
        errors.append("faithfulness_policy.json: schema_version must be 2")
    grounding = whole_policy.get("grounding", {})
    certificate_schema = grounding.get("certificate_schema", {})
    if set(certificate_schema.get("required_fields", [])) != {
        "theorem", "claim", "references"
    }:
        errors.append("faithfulness_policy.json: grounding certificate fields must be "
                      "theorem, claim, and references")
    policy = whole_policy.get("library_helpers", {})
    if policy.get("metadata_field") != "helper_ownership":
        errors.append("faithfulness_policy.json: library_helpers.metadata_field must be "
                      "helper_ownership")
    classifications = policy.get("required_classifications")
    if set(classifications or []) != ALLOWED_OWNERSHIP:
        errors.append("faithfulness_policy.json: required helper classifications must be "
                      "paper_specific and compatibility_alias")
    return errors


def prospective_waves(phase: str | None = None) -> list[tuple[str, dict]]:
    policy = load_json(POLICY)
    minimum = int(policy["prospective_v2_wave_min"])
    waves = load_json(WAVES).get("waves", {})
    out = []
    for key, wave in waves.items():
        wave_phase = wave.get("phase", key)
        match = re.fullmatch(r"X(\d+)", wave_phase)
        if not match or int(match.group(1)) < minimum:
            continue
        if phase is not None and wave_phase != phase and key != phase:
            continue
        out.append((key, wave))
    return sorted(out)


def validate_ownership(
    inventory: dict, registry: dict[str, dict], phase: str | None = None
) -> list[str]:
    errors: list[str] = []
    by_path: dict[str, list[dict]] = defaultdict(list)
    for helper in inventory["helpers"]:
        by_path[helper["path"]].append(helper)

    selected_waves = prospective_waves(phase)
    if phase is not None and not selected_waves:
        return [f"{phase}: no prospective wave metadata found"]
    for key, wave in selected_waves:
        rel = f"{wave.get('repo')}/theories/conjectures/{wave.get('defines_file')}"
        errors.extend(validate_wave_ownership(key, wave, by_path.get(rel, []), registry))
    return errors


def validate_wave_ownership(
    key: str, wave: dict, helpers: list[dict], registry: dict[str, dict]
) -> list[str]:
    errors: list[str] = []
    ownership = wave.get("helper_ownership", {})
    if not isinstance(ownership, dict):
        errors.append(f"{key}: helper_ownership must be an object")
        ownership = {}
    names = {helper["name"] for helper in helpers}
    missing = sorted(names - set(ownership))
    stale = sorted(set(ownership) - names)
    if missing:
        errors.append(f"{key}: unclassified helpers {missing}")
    if stale:
        errors.append(f"{key}: helper_ownership has stale names {stale}")
    for name in sorted(names & set(ownership)):
        spec = ownership[name]
        prefix = f"{key}:{name}"
        if not isinstance(spec, dict):
            errors.append(f"{prefix}: ownership entry must be an object")
            continue
        classification = spec.get("classification")
        if classification not in ALLOWED_OWNERSHIP:
            errors.append(f"{prefix}: invalid classification {classification!r}")
        reason = spec.get("reason")
        if not isinstance(reason, str) or len(reason.strip()) < 20:
            errors.append(f"{prefix}: reason must contain at least 20 characters")
        if classification == "compatibility_alias":
            primitive = spec.get("primitive")
            if primitive not in registry:
                errors.append(f"{prefix}: unknown registry primitive {primitive!r}")
                continue
            helper = next(item for item in helpers if item["name"] == name)
            primitive_spec = registry[primitive]
            if helper["qualified_name"] not in primitive_spec.get("source_definitions", []):
                errors.append(
                    f"{prefix}: compatibility alias is not registered in "
                    f"{primitive}.source_definitions"
                )
            if helper["normalized_name"] not in primitive_spec.get("normalized_names", []):
                errors.append(
                    f"{prefix}: normalized name {helper['normalized_name']!r} does not match "
                    f"registry primitive {primitive}"
                )
            theorem = spec.get("compatibility_theorem")
            if theorem not in primitive_spec.get("compatibility_theorems", []):
                errors.append(
                    f"{prefix}: compatibility_theorem must name a theorem registered for "
                    f"{primitive}"
                )
    return errors


def print_summary(inventory: dict, registry: dict[str, dict], max_groups: int) -> None:
    counts = inventory["counts"]
    print(
        "library-helper inventory: "
        f"{counts['helpers']} helpers in {counts['files']} conjecture files; "
        f"{counts['x_wave_helpers']} wave-prefixed; "
        f"{counts['repeated_normalized_names']} repeated-name families; "
        f"{len(registry)} registered families"
    )
    groups = inventory["groups"]["normalized_name"]
    ranked = sorted(groups.items(), key=lambda item: (-len(item[1]), item[0]))
    registered_names = {
        name: (primitive_id, spec["status"])
        for primitive_id, spec in registry.items()
        for name in spec.get("normalized_names", [])
    }
    for name, members in ranked[:max_groups]:
        if name in registered_names:
            primitive_id, status = registered_names[name]
            print(
                f"  REGISTERED {name}: {len(members)} definitions "
                f"({primitive_id}, {status})"
            )
        else:
            print(f"  LEGACY {name}: {len(members)} definitions")
    if len(ranked) > max_groups:
        print(f"  ... {len(ranked) - max_groups} more repeated-name families omitted")


def validate_self_test() -> int:
    fixture = """
(* nested (* comment *) *)
Definition x211_edge_set (G : sgraph) : {set {set G}} := set0.
Definition x211_claim_statement : Prop := x211_edge_set unit = set0.
Lemma x211_edge_set_sound : True. Proof. exact I. Qed.
Definition x211_aux_statement : nat := 0.
"""
    clean = strip_comments(fixture)
    matches = list(DECL_RE.finditer(clean))
    parser_ok = (
        [match.group(2) for match in matches] == [
            "x211_edge_set", "x211_claim_statement", "x211_edge_set_sound",
            "x211_aux_statement",
        ]
        and normalized_name("x211_edge_set") == "edge_set"
        and sentence_end(clean, matches[0].start()) < matches[1].start()
        and is_manifest_statement("x211_claim_statement", {"x211_claim_statement"})
        and not is_manifest_statement("x211_aux_statement", {"x211_claim_statement"})
    )
    helpers = [{"name": "x211_edge_set", "qualified_name": "Fixture.X211.x211_edge_set",
                "normalized_name": "edge_set"}]
    registry = {"simple-graph-edge-set": {
        "normalized_names": ["edge_set"],
        "source_definitions": ["Fixture.X211.x211_edge_set"],
        "compatibility_theorems": ["Fixture.X211.x211_edge_set_compat"],
    }}
    missing = validate_wave_ownership("X211", {}, helpers, registry)
    valid = validate_wave_ownership("X211", {"helper_ownership": {
        "x211_edge_set": {
            "classification": "compatibility_alias",
            "primitive": "simple-graph-edge-set",
            "compatibility_theorem": "Fixture.X211.x211_edge_set_compat",
            "reason": "Temporary alias used during the edge migration pilot."
        }
    }}, helpers, registry)
    paper_specific = validate_wave_ownership("X211", {"helper_ownership": {
        "x211_edge_set": {
            "classification": "paper_specific",
            "reason": "This helper encodes the exceptional family named by the source."
        }
    }}, helpers, registry)
    unrelated = validate_wave_ownership("X211", {"helper_ownership": {
        "x211_edge_set": {
            "classification": "compatibility_alias",
            "primitive": "simple-graph-edge-set",
            "compatibility_theorem": "Fixture.X211.not_registered",
            "reason": "This claim deliberately names no registered compatibility theorem."
        }
    }}, helpers, registry)
    ok = parser_ok and any("unclassified helpers" in error for error in missing) \
        and not valid and not paper_specific \
        and any("compatibility_theorem" in error for error in unrelated)
    print(f"library-inventory self-test {'OK' if ok else 'FAILED'}")
    return 0 if ok else 1


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write", action="store_true", help="refresh the committed inventory")
    parser.add_argument("--check", action="store_true", help="fail if the inventory has drifted")
    scope = parser.add_mutually_exclusive_group()
    scope.add_argument("--new-waves", action="store_true",
                       help="enforce helper ownership for all prospective waves")
    scope.add_argument("--wave", help="enforce helper ownership for one prospective phase")
    parser.add_argument("--json", action="store_true")
    parser.add_argument("--max-groups", type=int, default=20)
    parser.add_argument("--validate", action="store_true")
    args = parser.parse_args(argv)

    if args.validate:
        return validate_self_test()
    inventory = build_inventory()
    registry, errors = validate_registry(inventory)
    errors.extend(validate_policy())
    if args.new_waves or args.wave:
        errors.extend(validate_ownership(inventory, registry, args.wave))

    rendered = json.dumps(inventory, indent=2, sort_keys=True) + "\n"
    if args.write:
        INVENTORY.write_text(rendered)
    if args.check:
        try:
            committed = INVENTORY.read_text()
        except OSError as exc:
            errors.append(f"cannot load {INVENTORY.relative_to(ROOT)}: {exc}")
        else:
            if committed != rendered:
                errors.append(
                    "library_helper_inventory.json has drifted; run "
                    "python3 meta/library_inventory.py --write"
                )

    if args.json:
        print(json.dumps({"counts": inventory["counts"], "errors": errors}, indent=2))
    else:
        print_summary(inventory, registry, args.max_groups)
        for error in errors:
            print(f"  ERROR: {error}", file=sys.stderr)
    return 1 if errors else 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
