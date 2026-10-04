# Migration report: edge-colour-class

Inputs: `meta/migration_reports/edge_colour_class.spec.json` and `meta/library_primitives/edge-colour-class.json`.
Regenerate: `python3 meta/migration_report.py edge_colour_class --write`.
Full evidence: `python3 meta/migration_report.py edge_colour_class --details /tmp/migration-details`.

- Canonical: `GTBase.edge_colourings.edge_colour_class`.
- Baseline: `2f37b10a711c81b9bfb6dcb1581ac2c527974baa`.
- Scope: 6 helpers, 3 statements, 27 frozen objects, 48 recorded references.
- Source checks: 187/187 pass; consistent.

| Statement / corpus row | Compatibility theorem |
|---|---|
| `Chromatic.conjectures.X34.planar_odd_degree_linear_forests_plus_matching_statement` / arxiv:2302.13312#00 | `Chromatic.migration.edge_colour_class.planar_odd_degree_linear_forests_plus_matching_statement_compat` |
| `Cycle.conjectures.X212.linear_arboricity_regular_statement` / bm:bm-016 | `Cycle.migration.edge_colour_class.linear_arboricity_regular_statement_compat` |
| `Topological.conjectures.X23.planar_linear_arboricity_statement` / studies:std_planar_linear_arboricity_conjecture | `Topological.migration.edge_colour_class.planar_linear_arboricity_statement_compat` |

Source checks compare frozen text, registry and statement coverage, bridge endpoints, and unchanged statement metadata. They do not prove theorem types.
`python3 meta/migration_report.py edge_colour_class --check --kernel` checks exact closed statement equivalences and all named theorem assumptions in already-built modules.
Helper types, Section context, notation/constructor resolution and compiled dependency closure still require independent review and family-specific Section and kernel dependency evidence.
