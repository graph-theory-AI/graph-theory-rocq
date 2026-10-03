# Migration report: minimum-degree

Inputs: `meta/migration_reports/min_degree.spec.json` and `meta/library_primitives/minimum-degree.json`.
Regenerate: `python3 meta/migration_report.py min_degree --write`.
Full evidence: `python3 meta/migration_report.py min_degree --details /tmp/migration-details`.

- Canonical: `GTBase.base.min_degree`.
- Baseline: `623a89ef8a3194f06f96ae7076d8cad00a8c3ece`.
- Scope: 2 helpers, 2 statements, 7 frozen objects, 15 recorded references.
- Source checks: 77/77 pass; consistent.

| Statement / corpus row | Compatibility theorem |
|---|---|
| `Extremal.conjectures.XE2.erdos_803_statement` / erdos:803 | `Extremal.migration.min_degree.erdos_803_statement_compat` |
| `GTMisc.conjectures.X227.hat_guessing_degree_degeneracy_bounds_statement` / arxiv:1812.09752#00 | `GTMisc.migration.min_degree.hat_guessing_degree_degeneracy_bounds_statement_compat` |

Source checks compare frozen text, registry and statement coverage, bridge endpoints, and unchanged statement metadata. They do not prove theorem types.
`python3 meta/migration_report.py min_degree --check --kernel` checks exact closed statement equivalences and all named theorem assumptions in already-built modules.
Helper types, Section context, notation/constructor resolution and compiled dependency closure still require independent review and family-specific Section and kernel dependency evidence.

Excluded distinct variants: `GTMisc.conjectures.X14.x14_subcubic`, `GTMisc.conjectures.X114.x114_subcubic`, `Chromatic.conjectures.U5.cubic`, `Cycle.conjectures.U6.cubic`.

Prior snapshot limitations (explanations and replacement certificates in the inputs): `extremal-graph-theory/theories/migration/subgraph_of.v#XE2Legacy.erdos_803_statement`, `extremal-graph-theory/theories/migration/edge_count.v#XE2Legacy.erdos_803_statement`, `extremal-graph-theory/theories/migration/edge_count.v#XE2Original.erdos_803_statement`.
