# Migration report: complete-multipartite

Inputs: `meta/migration_reports/complete_multipartite_graphs.spec.json` and `meta/library_primitives/complete-multipartite.json`.
Regenerate: `python3 meta/migration_report.py complete_multipartite_graphs --write`.
Full evidence: `python3 meta/migration_report.py complete_multipartite_graphs --details /tmp/migration-details`.

- Canonical: `GTBase.complete_multipartite_graphs.complete_multipartite_graph`.
- Baseline: `9e3f1efa368ca76a654e4c11c796758f72af3ec9`.
- Scope: 4 helpers, 2 statements, 11 frozen objects, 41 recorded references.
- Source checks: 112/112 pass; consistent.

| Statement / corpus row | Compatibility theorem |
|---|---|
| `Chromatic.conjectures.U4.choice_number_of_k_chromatic_graphs_of_bounded_order_statement` / opg:choice_number_of_k_chromatic_graphs_of_bounded_order | `Chromatic.migration.complete_multipartite_graphs.choice_number_of_k_chromatic_graphs_of_bounded_order_statement_compat` |
| `Chromatic.conjectures.X218.every_forest_is_multibounding_statement` / arxiv:2303.11766#00 | `Chromatic.migration.complete_multipartite_graphs.every_forest_is_multibounding_statement_compat` |

Source checks compare frozen text, registry and statement coverage, bridge endpoints, and unchanged statement metadata. They do not prove theorem types.
`python3 meta/migration_report.py complete_multipartite_graphs --check --kernel` checks exact closed statement equivalences and all named theorem assumptions in already-built modules.
Helper types, Section context, notation/constructor resolution and compiled dependency closure still require independent review and family-specific Section and kernel dependency evidence.

Excluded distinct variants: `Extremal.conjectures.XE1.xe1_complete_multipartite_with_sizes`, `Digraph.conjectures.X221.x221_oriented_complete_multipartite`.
