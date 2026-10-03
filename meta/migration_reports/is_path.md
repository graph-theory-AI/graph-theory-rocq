# Migration report: is-path

Inputs: `meta/migration_reports/is_path.spec.json` and `meta/library_primitives/is-path.json`.
Regenerate: `python3 meta/migration_report.py is_path --write`.
Full evidence: `python3 meta/migration_report.py is_path --details /tmp/migration-details`.

- Canonical: `GTBase.walks_paths.seq_simple_walk`.
- Baseline: `632e0b124089c15c11fc2e801435479a9c741c5c`.
- Scope: 2 helpers, 2 statements, 6 frozen objects, 20 recorded references.
- Source checks: 86/86 pass; consistent.

| Statement / corpus row | Compatibility theorem |
|---|---|
| `Hom.conjectures.U3.do_any_three_longest_paths_in_a_connected_graph_have_statement` / opg:do_any_three_longest_paths_in_a_connected_graph_have_a_vertex_in_common | `Hom.migration.is_path.do_any_three_longest_paths_in_a_connected_graph_have_statement_compat` |
| `Cycle.conjectures.U6.decomposing_a_connected_graph_into_paths_statement` / opg:decomposing_a_connected_graph_into_paths | `Cycle.migration.is_path.decomposing_a_connected_graph_into_paths_statement_compat` |

Source checks compare frozen text, registry and statement coverage, bridge endpoints, and unchanged statement metadata. They do not prove theorem types.
`python3 meta/migration_report.py is_path --check --kernel` checks exact closed statement equivalences and all named theorem assumptions in already-built modules.
Helper types, Section context, notation/constructor resolution and compiled dependency closure still require independent review and family-specific Section and kernel dependency evidence.

Excluded distinct variants: `Packing.conjectures.U9.spath`, `Extremal.conjectures.XE2.xe2_path_in_graph`.
