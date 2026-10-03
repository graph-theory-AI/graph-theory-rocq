# Migration report: proper-edge-colouring

Inputs: `meta/migration_reports/proper_edge_colouring.spec.json` and `meta/library_primitives/proper-edge-colouring.json`.
Regenerate: `python3 meta/migration_report.py proper_edge_colouring --write`.
Full evidence: `python3 meta/migration_report.py proper_edge_colouring --details /tmp/migration-details`.

- Canonical: `GTBase.edge_colourings.proper_edge_colouring`.
- Baseline: `3011c280a09f292461a3b1e5a99f7be3febfbbb9`.
- Scope: 5 helpers, 7 statements, 22 frozen objects, 51 recorded references.
- Source checks: 210/210 pass; consistent.

| Statement / corpus row | Compatibility theorem |
|---|---|
| `Chromatic.conjectures.X142.flandrin_neighbour_sum_distinguishing_edge_colouring_statement` / studies:std_flandrin_et_al_conjecture_neighbour_sum_distingu | `Chromatic.migration.edge_colourings.flandrin_neighbour_sum_distinguishing_edge_colouring_statement_compat` |
| `Chromatic.conjectures.X213.one_factorization_conjecture_statement` / bm:bm-057 | `Chromatic.migration.edge_colourings.one_factorization_conjecture_statement_compat` |
| `Chromatic.conjectures.X213.vizing_kempe_interchange_statement` / bm:bm-060 | `Chromatic.migration.edge_colourings.vizing_kempe_interchange_statement_compat` |
| `GTMisc.conjectures.X14.andersen_rainbow_path_statement` / studies:std_andersen_s_conjecture | `GTMisc.migration.edge_colourings.andersen_rainbow_path_statement_compat` |
| `GTMisc.conjectures.X62.rainbow_paths_linear_edge_cover_statement` / arxiv:2301.08707#01 | `GTMisc.migration.edge_colourings.rainbow_paths_linear_edge_cover_statement_compat` |
| `Extremal.conjectures.D2chr.star_chromatic_index_of_complete_graphs_statement` / opg:star_chromatic_index_of_complete_graphs | `Extremal.migration.edge_colourings.star_chromatic_index_of_complete_graphs_statement_compat` |
| `Extremal.conjectures.X229.expander_proper_colouring_two_connected_palettes_statement` / arxiv:2309.04460#01 | `Extremal.migration.edge_colourings.expander_proper_colouring_two_connected_palettes_statement_compat` |

Source checks compare frozen text, registry and statement coverage, bridge endpoints, and unchanged statement metadata. They do not prove theorem types.
`python3 meta/migration_report.py proper_edge_colouring --check --kernel` checks exact closed statement equivalences and all named theorem assumptions in already-built modules.
Helper types, Section context, notation/constructor resolution and compiled dependency closure still require independent review and family-specific Section and kernel dependency evidence.

Excluded distinct variants: `Chromatic.conjectures.U5.acyclic_edge_colouring`, `Chromatic.conjectures.U5.star_edge_colouring`, `Chromatic.conjectures.X43.x43_strong_edge_colourable`, `Chromatic.conjectures.XE1.xe1_strong_edge_colouring`, `Chromatic.conjectures.X219.x219_edge_choosable`, `Cycle.conjectures.X9.x9_cycle_incident_edges_properly_coloured`, `Chromatic.conjectures.X100.x100_modular_edge_colouring`.
