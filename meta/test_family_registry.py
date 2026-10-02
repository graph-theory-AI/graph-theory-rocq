#!/usr/bin/env python3
"""Fail-closed registry storage and family ownership regressions; no Rocq needed."""
from __future__ import annotations

import copy
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import family_registry as R
import foundation_fidelity as F
import library_inventory as I
import check_library_migration as M


class FamilyRegistries(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory(prefix='family-registry-')
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        (self.root / 'meta/library_primitives').mkdir(parents=True)
        (self.root / 'meta/foundation_fidelity').mkdir()
        (self.root / 'base/theories').mkdir(parents=True)
        (self.root / 'base/theories/common.v').write_text(
            'Definition original : Prop := True.\n'
            'Definition added : Prop := True.\n'
            'Definition second : Prop := True.\n'
            'Lemma evidence : True. Proof. exact I. Qed.\n')
        self.primitive = {
            'canonical_name': None, 'owner': 'base', 'status': 'auditing',
            'fidelity': 'PENDING', 'normalized_names': ['fixture'],
            'source_definitions': [], 'consumers_remaining': 0,
            'compatibility_theorems': [], 'upstream_audit': {},
        }
        self.base = {
            'schema_version': 2, 'verdicts': ['FAITHFUL', 'LIGHTWEIGHT', 'BROKEN'],
            'modules': {'GTBase.common': {
                'path': 'base/theories/common.v',
                'default': {'verdict': 'LIGHTWEIGHT', 'note': 'Original module contract.'},
                'audited_primitives': ['original'], 'overrides': {}, 'machine_evidence': [],
            }},
        }
        self.write_family()
        self.write_json('meta/foundation_fidelity.json', self.base)

    def write_json(self, path, data):
        actual = self.root / path
        actual.parent.mkdir(parents=True, exist_ok=True)
        actual.write_text(json.dumps(data))
        return actual

    def write_family(self, family='fixture', spec=None):
        return self.write_json(f'meta/library_primitives/{family}.json', {
            'schema_version': 1, 'family': family,
            'primitive': copy.deepcopy(self.primitive if spec is None else spec),
        })

    def write_fragment(self, family='fixture', name='added'):
        spec = copy.deepcopy(self.primitive)
        spec['foundation_fidelity'] = f'meta/foundation_fidelity/{family}.json'
        self.write_family(family, spec)
        fragment = {'schema_version': 1, 'family': family, 'modules': {'GTBase.common': {
            'path': 'base/theories/common.v',
            'overrides': {name: {'verdict': 'FAITHFUL', 'note': 'Family contract.'}},
            'machine_evidence': ['evidence'],
        }}}
        self.write_json(spec['foundation_fidelity'], fragment)
        return fragment

    def test_library_documents_preserve_logical_shape(self):
        self.write_family('another')
        result = R.load_library_registry(self.root)
        self.assertEqual(result['schema_version'], 1)
        self.assertEqual(list(result['primitives']), ['another', 'fixture'])
        self.assertEqual(result['primitives']['fixture'], self.primitive)

    def test_missing_or_empty_directory_is_rejected(self):
        (self.root / 'meta/library_primitives/fixture.json').unlink()
        with self.assertRaisesRegex(R.RegistryError, 'no family registry documents'):
            R.load_library_registry(self.root)
        (self.root / 'meta/library_primitives').rmdir()
        with self.assertRaisesRegex(R.RegistryError, 'missing family registry directory'):
            R.load_library_registry(self.root)

    def test_aggregate_is_never_an_alternative_authority(self):
        self.write_json('meta/library_primitives.json', {'schema_version': 1, 'primitives': {}})
        with self.assertRaisesRegex(R.RegistryError, 'obsolete aggregate'):
            R.load_library_registry(self.root)

    def test_malformed_json_and_duplicate_keys_are_rejected(self):
        for text in ('{', '[]', '{"family":"a","family":"b"}',
                     '{"primitive":{"status":"auditing","status":"complete"}}'):
            with self.subTest(text=text):
                (self.root / 'meta/library_primitives/fixture.json').write_text(text)
                with self.assertRaises(R.RegistryError):
                    R.load_library_registry(self.root)

    def test_duplicate_family_and_filename_mismatch_are_rejected(self):
        data = R.read_object(self.root / 'meta/library_primitives/fixture.json')
        extra = self.write_json('meta/library_primitives/z-copy.json', data)
        with self.assertRaisesRegex(R.RegistryError, 'duplicate family'):
            R.load_library_registry(self.root)
        extra.unlink()
        data['family'] = 'other'
        self.write_json('meta/library_primitives/fixture.json', data)
        with self.assertRaisesRegex(R.RegistryError, 'filename must match family'):
            R.load_library_registry(self.root)

    def test_invalid_envelopes_and_primitive_shapes_are_rejected(self):
        base = R.read_object(self.root / 'meta/library_primitives/fixture.json')
        for field, value in [('schema_version', True), ('schema_version', 2),
                             ('primitive', []), ('primitive', {}), ('family', '../fixture')]:
            with self.subTest(field=field, value=value):
                data = copy.deepcopy(base)
                data[field] = value
                self.write_json('meta/library_primitives/fixture.json', data)
                with self.assertRaises(R.RegistryError):
                    R.load_library_registry(self.root)
        for field, value in [('status', []), ('fidelity', 'UNKNOWN'), ('owner', ''),
                             ('consumers_remaining', True), ('normalized_names', []),
                             ('source_definitions', ['duplicate', 'duplicate']),
                             ('api_theorems', [None]), ('upstream_audit', None)]:
            with self.subTest(field=field, value=value):
                spec = copy.deepcopy(self.primitive)
                spec[field] = value
                self.write_family(spec=spec)
                with self.assertRaises(R.RegistryError):
                    R.load_library_registry(self.root)

    def test_document_links_cannot_be_missing_or_escape(self):
        for path in ('meta/missing.md', '../outside.md', '/tmp/outside.md'):
            with self.subTest(path=path):
                self.write_family(spec={**self.primitive, 'migration_report': path})
                with self.assertRaises(R.RegistryError):
                    R.load_library_registry(self.root)

    def test_report_writer_can_bootstrap_only_generated_reports(self):
        self.write_family(spec={**self.primitive, 'migration_report': 'meta/migration_reports/fixture.md'})
        R.load_library_registry(self.root, allow_missing_reports=True)
        with self.assertRaises(R.RegistryError):
            R.load_library_registry(self.root)
        self.write_family(spec={**self.primitive, 'independent_review': 'meta/missing.md'})
        with self.assertRaises(R.RegistryError):
            R.load_library_registry(self.root, allow_missing_reports=True)
        self.write_family(spec={**self.primitive, 'migration_report': '../escape.md'})
        with self.assertRaises(R.RegistryError):
            R.load_library_registry(self.root, allow_missing_reports=True)

    def test_fidelity_fragments_preserve_module_contracts(self):
        self.write_fragment()
        self.write_fragment('second-family', 'second')
        merged = R.load_fidelity_registry(self.root)
        common = merged['modules']['GTBase.common']
        self.assertEqual(common['default'], self.base['modules']['GTBase.common']['default'])
        self.assertEqual(common['audited_primitives'], ['original'])
        self.assertEqual(set(common['overrides']), {'added', 'second'})
        self.assertEqual(common['machine_evidence'], ['evidence'])
        with patch.object(F, 'ROOT', self.root):
            entries, errors = F.expand_registry()
        self.assertEqual(errors, [])
        self.assertEqual({entry['primitive']: entry['verdict'] for entry in entries},
                         {'original': 'LIGHTWEIGHT', 'added': 'FAITHFUL', 'second': 'FAITHFUL'})

    def test_missing_and_unowned_fidelity_fragments_are_rejected(self):
        self.write_fragment()
        path = self.root / 'meta/foundation_fidelity/fixture.json'
        path.unlink()
        with self.assertRaisesRegex(R.RegistryError, 'missing document'):
            R.load_fidelity_registry(self.root)
        self.write_fragment()
        self.write_family()
        with self.assertRaisesRegex(R.RegistryError, 'unowned'):
            R.load_fidelity_registry(self.root)

    def test_duplicate_fidelity_ownership_is_rejected(self):
        self.write_fragment(name='original')
        with self.assertRaisesRegex(R.RegistryError, 'duplicate primitive ownership'):
            R.load_fidelity_registry(self.root)
        self.write_fragment()
        self.write_fragment('second-family')
        with self.assertRaisesRegex(R.RegistryError, 'duplicate primitive ownership'):
            R.load_fidelity_registry(self.root)

    def test_family_cannot_change_module_default_or_path(self):
        fragment = self.write_fragment()
        fragment['modules']['GTBase.common']['default'] = {'verdict': 'FAITHFUL', 'note': 'Hijack.'}
        self.write_json('meta/foundation_fidelity/fixture.json', fragment)
        with self.assertRaisesRegex(R.RegistryError, 'module defaults stay'):
            R.load_fidelity_registry(self.root)
        fragment = self.write_fragment()
        self.write_json('base/theories/other.v', {})
        fragment['modules']['GTBase.common']['path'] = 'base/theories/other.v'
        self.write_json('meta/foundation_fidelity/fixture.json', fragment)
        with self.assertRaisesRegex(R.RegistryError, 'module path conflicts'):
            R.load_fidelity_registry(self.root)

    def test_invalid_fidelity_verdict_is_rejected(self):
        for verdict in ([], {}, 'PENDING', None):
            with self.subTest(verdict=verdict):
                fragment = self.write_fragment()
                fragment['modules']['GTBase.common']['overrides']['added']['verdict'] = verdict
                self.write_json('meta/foundation_fidelity/fixture.json', fragment)
                with self.assertRaises(R.RegistryError):
                    R.load_fidelity_registry(self.root)

    def test_readers_fail_before_compilation_on_malformed_registry(self):
        (self.root / 'meta/library_primitives/fixture.json').write_text('{')
        with patch.object(I, 'ROOT', self.root):
            entries, errors = I.validate_registry({'helpers': []})
        self.assertEqual(entries, {})
        self.assertTrue(errors)
        with patch.object(M, 'ROOT', self.root), patch.object(M.subprocess, 'run') as run:
            self.assertEqual(M.main(), 1)
            run.assert_not_called()
        with patch.object(F, 'ROOT', self.root):
            entries, errors = F.expand_registry()
        self.assertEqual(entries, [])
        self.assertTrue(errors)


if __name__ == '__main__':
    unittest.main(verbosity=2)
