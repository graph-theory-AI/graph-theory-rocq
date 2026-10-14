# Migration report: linear-forest

Inputs: `meta/migration_reports/linear_forest.spec.json` and `meta/library_primitives/linear-forest.json`.
Regenerate: `python3 meta/migration_report.py linear_forest --write`.
Full evidence: `python3 meta/migration_report.py linear_forest --details /tmp/migration-details`.

- Canonical: `GTBase.path_trees.linear_forest`.
- Baseline: `1123673d3b2910361a05bc5381fdecd68c610951`.
- Scope: 3 helpers, 3 statements, 36 frozen objects, 35 recorded references.
- Source checks: 223/223 pass; consistent.

| Statement / corpus row | Compatibility theorem |
|---|---|
| `Chromatic.conjectures.X34.planar_odd_degree_linear_forests_plus_matching_statement` / arxiv:2302.13312#00 | `Chromatic.migration.linear_forest.planar_odd_degree_linear_forests_plus_matching_statement_compat` |
| `Cycle.conjectures.X212.linear_arboricity_regular_statement` / bm:bm-016 | `Cycle.migration.linear_forest.linear_arboricity_regular_statement_compat` |
| `Topological.conjectures.X23.planar_linear_arboricity_statement` / studies:std_planar_linear_arboricity_conjecture | `Topological.migration.linear_forest.planar_linear_arboricity_statement_compat` |

Source checks compare frozen text, registry and statement coverage, bridge endpoints, and unchanged statement metadata. They do not prove theorem types.
`python3 meta/migration_report.py linear_forest --check --kernel` checks exact closed statement equivalences and all named theorem assumptions in already-built modules.
Helper types, Section context, notation/constructor resolution and compiled dependency closure still require independent review and family-specific Section and kernel dependency evidence.

Excluded distinct variants: `GTBase.path_trees.path_tree`, `Digraph.conjectures.path_fas.linear_forest`, `GTMisc.conjectures.X74.x74_induced_linear_forest`.
