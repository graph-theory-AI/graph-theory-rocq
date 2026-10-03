"""Strict readers for independently owned migration-family registry documents.

The returned objects retain the logical schemas used by the inventory and
fidelity gates. Storage has one authoritative library document per family;
optional fidelity fragments add explicit primitive verdicts without changing
the historical module defaults in foundation_fidelity.json.
"""
from __future__ import annotations

import copy
import json
from pathlib import Path, PurePosixPath
import re


ROOT = Path(__file__).resolve().parents[1]
FAMILY = re.compile(r"[a-z][a-z0-9-]*")
STATUSES = {"proposed", "auditing", "canonical", "migrating", "deprecated", "complete"}
FIDELITIES = {"PENDING", "FAITHFUL", "LIGHTWEIGHT", "BROKEN"}


class RegistryError(ValueError):
    pass


def _unique_object(pairs: list[tuple[str, object]]) -> dict:
    result = {}
    for key, value in pairs:
        if key in result:
            raise RegistryError(f"duplicate JSON key {key!r}")
        result[key] = value
    return result


def read_object(path: Path) -> dict:
    try:
        data = json.loads(path.read_text(), object_pairs_hook=_unique_object)
    except (OSError, ValueError) as exc:
        raise RegistryError(f"{path}: {exc}") from exc
    if not isinstance(data, dict):
        raise RegistryError(f"{path}: document must be an object")
    return data


def _string_list(value: object, where: str, *, nonempty: bool = False) -> None:
    if not isinstance(value, list) or (nonempty and not value) or not all(
        isinstance(item, str) and item for item in value
    ) or len(value) != len(set(value)):
        raise RegistryError(f"{where}: expected {'nonempty ' if nonempty else ''}unique string list")


def _document(root: Path, relative: object, where: str, *, allow_missing: bool = False) -> Path:
    if not isinstance(relative, str):
        raise RegistryError(f"{where}: document path must be a string")
    path = PurePosixPath(relative)
    if path.is_absolute() or '..' in path.parts or str(path) != relative:
        raise RegistryError(f"{where}: document path must be canonical and repository-relative")
    actual = root / relative
    if not actual.resolve().is_relative_to(root.resolve()) or (not actual.is_file() and not (allow_missing and not actual.exists())):
        raise RegistryError(f"{where}: missing document or path escapes repository: {relative}")
    return actual


def load_library_registry(root: Path = ROOT, *, allow_missing_reports: bool = False) -> dict:
    """Read meta/library_primitives/<family>.json; never fall back to an aggregate."""
    root = Path(root)
    old = root / 'meta/library_primitives.json'
    if old.exists():
        raise RegistryError(f"{old}: obsolete aggregate registry; use per-family documents")
    directory = root / 'meta/library_primitives'
    if not directory.is_dir():
        raise RegistryError(f"{directory}: missing family registry directory")
    paths = sorted(directory.glob('*.json'))
    if not paths:
        raise RegistryError(f"{directory}: no family registry documents")
    entries = {}
    source_owners = {}
    for path in paths:
        _document(root, path.relative_to(root).as_posix(), str(path))
        data = read_object(path)
        if set(data) != {'schema_version', 'family', 'primitive'} or type(data.get('schema_version')) is not int or data['schema_version'] != 1:
            raise RegistryError(f"{path}: expected schema_version=1, family and primitive")
        family = data['family']
        if not isinstance(family, str) or not FAMILY.fullmatch(family):
            raise RegistryError(f"{path}: invalid family identifier")
        if family in entries:
            raise RegistryError(f"{path}: duplicate family {family!r}")
        if path.stem != family:
            raise RegistryError(f"{path}: filename must match family {family!r}")
        spec = data['primitive']
        if not isinstance(spec, dict):
            raise RegistryError(f"{path}: primitive must be an object")
        required = {'canonical_name', 'owner', 'status', 'fidelity', 'normalized_names',
                    'source_definitions', 'consumers_remaining', 'compatibility_theorems', 'upstream_audit'}
        if missing := required - spec.keys():
            raise RegistryError(f"{path}: missing primitive fields: {sorted(missing)}")
        if not isinstance(spec['status'], str) or spec['status'] not in STATUSES:
            raise RegistryError(f"{path}: invalid primitive status")
        if not isinstance(spec['fidelity'], str) or spec['fidelity'] not in FIDELITIES:
            raise RegistryError(f"{path}: invalid fidelity")
        if not isinstance(spec['owner'], str) or not spec['owner']:
            raise RegistryError(f"{path}: owner must be a nonempty string")
        if spec['canonical_name'] is not None and not isinstance(spec['canonical_name'], str):
            raise RegistryError(f"{path}: canonical_name must be a string or null")
        if type(spec['consumers_remaining']) is not int or spec['consumers_remaining'] < 0:
            raise RegistryError(f"{path}: consumers_remaining must be a nonnegative integer")
        _string_list(spec['normalized_names'], f'{path}:normalized_names', nonempty=True)
        for field in ('source_definitions', 'compatibility_theorems', 'api_theorems'):
            _string_list(spec.get(field, []), f'{path}:{field}')
        sources = spec.get('repository_sources', {})
        if not isinstance(sources, dict):
            raise RegistryError(f"{path}: repository_sources must be an object")
        for name, source in sources.items():
            if name not in spec['source_definitions']:
                raise RegistryError(f"{path}: repository source outside source_definitions: {name}")
            if not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)+", name):
                raise RegistryError(f"{path}: invalid repository source name: {name}")
            if not isinstance(source, dict) or set(source) != {'path', 'commit', 'blob', 'declaration_hash'}:
                raise RegistryError(f"{path}: repository source needs path, commit, blob, declaration_hash: {name}")
            for field, length in (('commit', 40), ('blob', 40), ('declaration_hash', 64)):
                if not isinstance(source[field], str) or not re.fullmatch(r'[0-9a-f]{' + str(length) + '}', source[field]):
                    raise RegistryError(f"{path}: invalid repository source {field}: {name}")
            actual = _document(root, source['path'], f'{path}:repository_sources:{name}')
            parts = PurePosixPath(source['path']).parts
            public = (len(parts) == 3 and parts[:2] == ('base', 'theories')) or (
                len(parts) >= 4 and parts[1:3] == ('theories', 'foundations'))
            if (not public or actual.suffix != '.v'
                    or actual.name.startswith(('grounding_', 'implications_', '_assum_', '_faith_', 'scratch_', 'gcheck'))
                    or actual.resolve() != root.resolve() / source['path']):
                raise RegistryError(f"{path}: repository source must be a regular public source without aliases: {name}")
        for name in spec['source_definitions']:
            if name in source_owners:
                raise RegistryError(f"{path}: duplicate source ownership: {name} ({source_owners[name]})")
            source_owners[name] = family
        if not isinstance(spec['upstream_audit'], dict):
            raise RegistryError(f"{path}: upstream_audit must be an object")
        for field in ('migration_report', 'migration_spec', 'independent_review', 'foundation_fidelity'):
            if field in spec:
                _document(root, spec[field], f'{path}:{field}',
                          allow_missing=allow_missing_reports and field == 'migration_report')
        if 'foundation_fidelity' in spec and spec['foundation_fidelity'] != f'meta/foundation_fidelity/{family}.json':
            raise RegistryError(f"{path}: foundation_fidelity must name this family's fragment")
        entries[family] = spec
    return {'schema_version': 1, 'primitives': entries}


def load_fidelity_registry(root: Path = ROOT) -> dict:
    """Merge family verdicts, rejecting overlapping ownership and changed module paths."""
    root = Path(root)
    base = root / 'meta/foundation_fidelity.json'
    data = copy.deepcopy(read_object(base))
    if type(data.get('schema_version')) is not int or data['schema_version'] != 2 or not isinstance(data.get('modules'), dict):
        raise RegistryError(f"{base}: expected schema_version=2 and modules object")
    modules = data['modules']
    for module, spec in modules.items():
        if not isinstance(spec, dict):
            raise RegistryError(f"{base}:{module}: module entry must be an object")
        _string_list(spec.get('audited_primitives', []), f'{base}:{module}:audited_primitives')
        _string_list(spec.get('machine_evidence', []), f'{base}:{module}:machine_evidence')
        if not isinstance(spec.get('overrides', {}), dict):
            raise RegistryError(f"{base}:{module}: overrides must be an object")
    families = load_library_registry(root)['primitives']
    expected = {spec['foundation_fidelity']: family for family, spec in families.items()
                if 'foundation_fidelity' in spec}
    directory = root / 'meta/foundation_fidelity'
    paths = sorted(directory.glob('*.json'))
    found = {path.relative_to(root).as_posix() for path in paths}
    if found != set(expected):
        raise RegistryError(f"{directory}: fidelity fragment ownership mismatch; "
                            f"missing={sorted(set(expected) - found)}, unowned={sorted(found - set(expected))}")
    for path in paths:
        fragment = read_object(path)
        family = expected[path.relative_to(root).as_posix()]
        if set(fragment) != {'schema_version', 'family', 'modules'} or type(fragment.get('schema_version')) is not int or fragment['schema_version'] != 1 or fragment['family'] != family:
            raise RegistryError(f"{path}: expected schema_version=1, family={family!r} and modules")
        additions = fragment['modules']
        if not isinstance(additions, dict) or not additions:
            raise RegistryError(f"{path}: modules must be a nonempty object")
        for module, spec in additions.items():
            if not isinstance(spec, dict) or set(spec) != {'path', 'overrides', 'machine_evidence'}:
                raise RegistryError(f"{path}:{module}: family entries require path, overrides and machine_evidence; module defaults stay in the base registry")
            _document(root, spec['path'], f'{path}:{module}:path')
            overrides = spec['overrides']
            if not isinstance(overrides, dict) or not overrides:
                raise RegistryError(f"{path}:{module}: overrides must explicitly enroll primitives")
            for name, verdict in overrides.items():
                if not isinstance(verdict, dict) or not isinstance(verdict.get('verdict'), str) or verdict['verdict'] not in FIDELITIES - {'PENDING'} or not isinstance(verdict.get('note'), str) or not verdict['note'].strip():
                    raise RegistryError(f"{path}:{module}.{name}: explicit verdict and note are required")
            _string_list(spec['machine_evidence'], f'{path}:{module}:machine_evidence', nonempty=True)
            previous = modules.setdefault(module, {'path': spec['path'], 'overrides': {}, 'machine_evidence': []})
            if previous.get('path') != spec['path']:
                raise RegistryError(f"{path}:{module}: module path conflicts with an existing entry")
            enrolled = set(previous.get('audited_primitives', [])) | set(previous.get('overrides', {}))
            if overlap := enrolled & overrides.keys():
                raise RegistryError(f"{path}:{module}: duplicate primitive ownership: {sorted(overlap)}")
            previous.setdefault('overrides', {}).update(overrides)
            previous['machine_evidence'] = list(dict.fromkeys(previous.get('machine_evidence', []) + spec['machine_evidence']))
    return data
