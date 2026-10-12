# Migration report: disjoint-union

Inputs: `meta/migration_reports/disjoint_union.spec.json` and `meta/library_primitives/disjoint-union.json`.
Regenerate: `python3 meta/migration_report.py disjoint_union --write`.
Full evidence: `python3 meta/migration_report.py disjoint_union --details /tmp/migration-details`.

- Canonical: `GraphTheory.core.sgraph.sjoin`.
- Baseline: `ec5fb25603796f719fa67cdfeb0bea4ebc928242`.
- Scope: 4 helpers, 2 statements, 14 frozen objects, 29 recorded references.
- Source checks: 108/108 pass; consistent.

| Statement / corpus row | Compatibility theorem |
|---|---|
| `Chromatic.conjectures.X66.good_trees_disjoint_union_good_statement` / arxiv:2202.09118#03 | `Chromatic.migration.disjoint_union.good_trees_disjoint_union_good_statement_compat` |
| `Digraph.conjectures.X2.delta_plus_maderian_disjoint_union_statement` / arxiv:1610.00876#02 | `Digraph.migration.disjoint_union.delta_plus_maderian_disjoint_union_statement_compat` |

Source checks compare frozen text, registry and statement coverage, bridge endpoints, and unchanged statement metadata. They do not prove theorem types.
`python3 meta/migration_report.py disjoint_union --check --kernel` checks exact closed statement equivalences and all named theorem assumptions in already-built modules.
Helper types, Section context, notation/constructor resolution and compiled dependency closure still require independent review and family-specific Section and kernel dependency evidence.

Excluded distinct variants: `Digraph.conjectures.heroes.djoin`, `Digraph.conjectures.X122.x122_dijoin`.

Prior snapshot limitations (explanations and replacement certificates in the inputs): `digraph-theory/theories/migration/path_vertices.v#X2UnionLegacy.statement`.
