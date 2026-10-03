# Migration report: cycle-vertices

Inputs: `meta/migration_reports/cycle_vertices.spec.json` and `meta/library_primitives/cycle-vertices.json`.
Regenerate: `python3 meta/migration_report.py cycle_vertices --write`.
Full evidence: `python3 meta/migration_report.py cycle_vertices --details /tmp/migration-details`.

- Canonical: `GTBase.walks_paths.seq_vertices`.
- Baseline: `13c00aa204725a73e12d05f57c51f5f970d89c15`.
- Scope: 6 helpers, 6 statements, 18 frozen objects, 40 recorded references.
- Source checks: 163/163 pass; consistent.

| Statement / corpus row | Compatibility theorem |
|---|---|
| `Chromatic.conjectures.X153.planar_girth5_two_cycles_list_critical_subgraph_statement` / arxiv:1302.2158#00 | `Chromatic.migration.cycle_vertices.planar_girth5_two_cycles_list_critical_subgraph_statement_compat` |
| `Cycle.conjectures.X10.smith_longest_cycles_r_connected_statement` / studies:std_smith_s_conjecture_longest_cycles_in_r_connected | `Cycle.migration.cycle_vertices.smith_longest_cycles_r_connected_statement_compat` |
| `Cycle.conjectures.X212.smith_two_longest_cycles_statement` / bm:bm-064 | `Cycle.migration.cycle_vertices.smith_two_longest_cycles_statement_compat` |
| `Cycle.conjectures.X5.min_degree_half_disjoint_four_cycles_statement` / erdos:577 | `Cycle.migration.cycle_vertices.min_degree_half_disjoint_four_cycles_statement_compat` |
| `Cycle.conjectures.X5.cycle_with_external_three_neighbours_statement` / erdos:916 | `Cycle.migration.cycle_vertices.cycle_with_external_three_neighbours_statement_compat` |
| `Digraph.conjectures.X19.lichiardopol_distinct_length_dicycle_packing_statement` / studies:std_lichiardopol_s_conjecture | `Digraph.migration.cycle_vertices.lichiardopol_distinct_length_dicycle_packing_statement_compat` |

Source checks compare frozen text, registry and statement coverage, bridge endpoints, and unchanged statement metadata. They do not prove theorem types.
`python3 meta/migration_report.py cycle_vertices --check --kernel` checks exact closed statement equivalences and all named theorem assumptions in already-built modules.
Helper types, Section context, notation/constructor resolution and compiled dependency closure still require independent review and family-specific Section and kernel dependency evidence.

Excluded distinct variants: `Cycle.conjectures.XE2.xe2_same_vertex_set`.

Prior snapshot limitations (explanations and replacement certificates in the inputs): `cycle-theory/theories/migration/genuine_cycle.v#X212Legacy.smith_two_longest_cycles_statement`, `cycle-theory/theories/migration/longest_cycle.v#X10Legacy.smith_longest_cycles_r_connected_statement`, `cycle-theory/theories/migration/longest_cycle.v#X212Legacy.smith_two_longest_cycles_statement`, `cycle-theory/theories/migration/edge_count.v#X5Legacy.cycle_with_external_three_neighbours_statement`.
