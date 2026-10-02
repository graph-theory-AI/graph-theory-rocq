# Migration report: induced-free

Inputs: `meta/migration_reports/induced_free.spec.json` and `meta/library_primitives/induced-free.json`.
Regenerate: `python3 meta/migration_report.py induced_free --write`.
Full evidence: `python3 meta/migration_report.py induced_free --details /tmp/migration-details`.

- Canonical: `GTBase.common.induced_free`.
- Baseline: `9e030727db115917ae077ac07a8fc6aa68661f73`.
- Scope: 10 helpers, 10 statements, 33 frozen objects, 58 recorded references.
- Source checks: 266/266 pass; consistent.

| Statement / corpus row | Compatibility theorem |
|---|---|
| `Chromatic.conjectures.X43.diamond_free_claw_free_cubic_strong_six_edge_colourable_statement` / arxiv:2511.02892#03 | `Chromatic.migration.induced_free.x43_statement_compat` |
| `Extremal.conjectures.X56.c8_complement_c8_erdos_hajnal_statement` / arxiv:2102.04994#00 | `Extremal.migration.induced_free.x56_statement_compat` |
| `Extremal.conjectures.X57.sparse_strong_eh_iff_forest_statement` / arxiv:1810.00811#00 | `Extremal.migration.induced_free.x57_statement_compat` |
| `Extremal.conjectures.X58.epsilon_bounded_h_free_anticomplete_pair_statement` / arxiv:1810.00058#00 | `Extremal.migration.induced_free.x58_statement_compat` |
| `Extremal.conjectures.X61.infinite_family_without_finite_induced_saturation_statement` / arxiv:2506.08810#00 | `Extremal.migration.induced_free.x61_statement_compat` |
| `Extremal.conjectures.X118.conlon_fox_sudakov_dense_pair_statement` / studies:std_conlon_fox_sudakov_conjecture_dense_pair | `Extremal.migration.induced_free.x118_statement_compat` |
| `Extremal.conjectures.X120.conlon_fox_sudakov_sparse_pair_statement` / studies:std_conlon_fox_sudakov_sparse_pair_conjecture | `Extremal.migration.induced_free.x120_statement_compat` |
| `GTMisc.conjectures.X41.sparse_linear_pure_pair_statement` / studies:std_conlon_fox_sudakov_sparse_linear_conjecture | `GTMisc.migration.induced_free.x41_statement_compat` |
| `GTMisc.conjectures.X102.bounded_tree_independence_forbidden_family_statement` / studies:std_bounded_tree_independence_number_conjecture_dall | `GTMisc.migration.induced_free.x102_statement_compat` |
| `Minor.conjectures.X42.even_hole_k4_diamond_free_bounded_treewidth_statement` / arxiv:2001.01607#00 | `Minor.migration.induced_free.x42_statement_compat` |

Source checks compare frozen text, registry and statement coverage, bridge endpoints, and unchanged statement metadata. They do not prove theorem types.
`python3 meta/migration_report.py induced_free --check --kernel` checks exact closed statement equivalences and all named theorem assumptions in already-built modules.
Helper types, Section context, notation/constructor resolution and compiled dependency closure still require independent review and family-specific Section and kernel dependency evidence.

Excluded distinct variants: `Extremal.conjectures.X207.x207_H_free`, `GTMisc.conjectures.X94.x94_H_free`.

Prior snapshot limitations (explanations and replacement certificates in the inputs): `graph-theory-misc/theories/migration/simple_edges.v#X102Legacy.statement`, `minor-theory/theories/migration/consecutive_in_cycle.v#X42Legacy.even_hole_k4_diamond_free_bounded_treewidth_statement`, `extremal-graph-theory/theories/migration/delete_edge.v#X61Legacy.induced_saturated`.
