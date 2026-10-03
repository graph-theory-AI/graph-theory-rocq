# Migration report: set-pair

Inputs: `meta/migration_reports/set_pairs.spec.json` and `meta/library_primitives/set-pair.json`.
Regenerate: `python3 meta/migration_report.py set_pairs --write`.
Full evidence: `python3 meta/migration_report.py set_pairs --details /tmp/migration-details`.

- Canonical: `GTBase.set_pairs.anticomplete`.
- Baseline: `229f2959f7726f1c0b1b3c72da4537245cb9919c`.
- Scope: 10 helpers, 9 statements, 41 frozen objects, 77 recorded references.
- Source checks: 313/313 pass; consistent.

| Statement / corpus row | Compatibility theorem |
|---|---|
| `Chromatic.conjectures.X3.erdos_anticomplete_pairs_statement` / erdos:1111 | `Chromatic.migration.set_pairs.erdos_anticomplete_pairs_statement_compat` |
| `Chromatic.conjectures.X213.el_zahar_erdos_statement` / bm:bm-046 | `Chromatic.migration.set_pairs.el_zahar_erdos_statement_compat` |
| `Extremal.conjectures.X57.sparse_strong_eh_iff_forest_statement` / arxiv:1810.00811#00 | `Extremal.migration.set_pairs.sparse_strong_eh_iff_forest_statement_compat` |
| `Extremal.conjectures.X58.epsilon_bounded_h_free_anticomplete_pair_statement` / arxiv:1810.00058#00 | `Extremal.migration.set_pairs.epsilon_bounded_h_free_anticomplete_pair_statement_compat` |
| `Extremal.conjectures.X223.triangle_free_eps_bounded_anticomplete_pair_statement` / arxiv:1810.00058#01 | `Extremal.migration.set_pairs.triangle_free_eps_bounded_anticomplete_pair_statement_compat` |
| `Extremal.conjectures.D2ram.complete_bipartite_subgraphs_of_perfect_graphs_statement` / opg:complete_bipartite_subgraphs_of_perfect_graphs | `Extremal.migration.set_pairs.complete_bipartite_subgraphs_of_perfect_graphs_statement_compat` |
| `GTMisc.conjectures.X41.sparse_linear_pure_pair_statement` / studies:std_conlon_fox_sudakov_sparse_linear_conjecture | `GTMisc.migration.set_pairs.sparse_linear_pure_pair_statement_compat` |
| `GTMisc.conjectures.X144.fox_pure_pair_perfect_graphs_statement` / studies:std_fox_s_pure_pair_conjecture_for_perfect_graphs | `GTMisc.migration.set_pairs.fox_pure_pair_perfect_graphs_statement_compat` |
| `Minor.conjectures.X11.induced_menger_anticomplete_paths_statement` / arxiv:2512.17232#00 | `Minor.migration.set_pairs.induced_menger_anticomplete_paths_statement_compat` |

Source checks compare frozen text, registry and statement coverage, bridge endpoints, and unchanged statement metadata. They do not prove theorem types.
`python3 meta/migration_report.py set_pairs --check --kernel` checks exact closed statement equivalences and all named theorem assumptions in already-built modules.
Helper types, Section context, notation/constructor resolution and compiled dependency closure still require independent review and family-specific Section and kernel dependency evidence.

Excluded distinct variants: `GTMisc.conjectures.X94.x94_complete_pair`, `GTMisc.conjectures.X94.x94_anticomplete_pair`, `Minor.conjectures.X67.x67_no_cross_edges`, `GTBase.common.complete_bipartite`.

Prior snapshot limitations (explanations and replacement certificates in the inputs): `extremal-graph-theory/theories/migration/induced_free.v#X57Legacy.sparse_strong_eh_property`, `extremal-graph-theory/theories/migration/induced_free.v#X58Legacy.statement`, `graph-theory-misc/theories/migration/induced_free.v#X41Legacy.statement`, `minor-theory/theories/migration/path_vertices.v#X11Legacy.pairwise_anticomplete_paths`, `minor-theory/theories/migration/set_path.v#X11Legacy.has_k_anticomplete_xy_paths`, `minor-theory/theories/migration/set_path.v#X11Original.has_k_anticomplete_xy_paths`, `minor-theory/theories/migration/set_path.v#X11Original.induced_menger_anticomplete_paths_statement`, `extremal-graph-theory/theories/migration/perfect_graphs.v#Legacy.complete_bipartite_subgraphs_of_perfect_graphs_statement`, `graph-theory-misc/theories/migration/perfect_graphs.v#Legacy.fox_pure_pair_perfect_graphs_statement`.
