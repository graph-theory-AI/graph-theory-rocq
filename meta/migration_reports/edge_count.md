# Migration report: edge-count

Inputs: `meta/migration_reports/edge_count.spec.json` and `meta/library_primitives/edge-count.json`.
Regenerate: `python3 meta/migration_report.py edge_count --write`.
Full evidence: `python3 meta/migration_report.py edge_count --details /tmp/migration-details`.

- Canonical: `GTBase.common.edge_count`.
- Baseline: `ae0e6059bcb9ff7cbee3c425e719ad9c7d772656`.
- Scope: 7 helpers, 35 statements, 90 frozen objects, 230 recorded references.
- Source checks: 770/770 pass; consistent.

| Statement / corpus row | Compatibility theorem |
|---|---|
| `Cycle.conjectures.X5.cycle_with_external_three_neighbours_statement` / erdos:916 | `Cycle.migration.edge_count.cycle_with_external_three_neighbours_statement_compat` |
| `Extremal.conjectures.D2ram.chromatic_number_of_common_graphs_statement` / opg:chromatic_number_of_common_graphs | `Extremal.migration.edge_count.chromatic_number_of_common_graphs_statement_compat` |
| `Extremal.conjectures.D2tur.turan_number_of_a_finite_family_statement` / opg:turan_number_of_a_finite_family | `Extremal.migration.edge_count.turan_number_of_a_finite_family_statement_compat` |
| `Extremal.conjectures.D2tur.sidorenkos_statement` / opg:sidorenkos_conjecture | `Extremal.migration.edge_count.sidorenkos_statement_compat` |
| `Extremal.conjectures.X4.turan_degree_sum_clique_statement` / erdos:904 | `Extremal.migration.edge_count.turan_degree_sum_clique_statement_compat` |
| `Extremal.conjectures.X4.book_triangle_edge_statement` / erdos:905 | `Extremal.migration.edge_count.book_triangle_edge_statement_compat` |
| `Extremal.conjectures.X4.c5_edge_count_above_turan_statement` / erdos:608 | `Extremal.migration.edge_count.c5_edge_count_above_turan_statement_compat` |
| `Extremal.conjectures.X4.triangle_supersaturation_statement` / erdos:1010 | `Extremal.migration.edge_count.triangle_supersaturation_statement_compat` |
| `Extremal.conjectures.X76.ck_free_max_cut_polynomial_surplus_statement` / studies:std_alon_et_al_c_k_free_max_cut_conjecture | `Extremal.migration.edge_count.ck_free_max_cut_polynomial_surplus_statement_compat` |
| `Extremal.conjectures.X78.h_free_max_cut_three_fourths_surplus_statement` / studies:std_alon_krivelevich_sudakov_max_cut_exponent_conjec | `Extremal.migration.edge_count.h_free_max_cut_three_fourths_surplus_statement_compat` |
| `Extremal.conjectures.X88.pentagonal_turan_stability_dominates_clique_count_statement` / studies:std_balogh_clemen_lavrov_lidick_pfender_conjecture | `Extremal.migration.edge_count.pentagonal_turan_stability_dominates_clique_count_statement_compat` |
| `Extremal.conjectures.X96.bollobas_erdos_large_c4_free_subgraph_statement` / studies:std_bollob_s_erd_s_problem_on_large_c_free_subgraphs | `Extremal.migration.edge_count.bollobas_erdos_large_c4_free_subgraph_statement_compat` |
| `Extremal.conjectures.XE1.erdos_128_statement` / erdos:128 | `Extremal.migration.edge_count.erdos_128_statement_compat` |
| `Extremal.conjectures.XE1.erdos_545_statement` / erdos:545 | `Extremal.migration.edge_count.erdos_545_statement_compat` |
| `Extremal.conjectures.XE1.erdos_548_statement` / erdos:548 | `Extremal.migration.edge_count.erdos_548_statement_compat` |
| `Extremal.conjectures.XE1.erdos_561_statement` / erdos:561 | `Extremal.migration.edge_count.erdos_561_statement_compat` |
| `Extremal.conjectures.XE1.erdos_566_statement` / erdos:566 | `Extremal.migration.edge_count.erdos_566_statement_compat` |
| `Extremal.conjectures.XE1.erdos_567_statement` / erdos:567 | `Extremal.migration.edge_count.erdos_567_statement_compat` |
| `Extremal.conjectures.XE1.erdos_568_statement` / erdos:568 | `Extremal.migration.edge_count.erdos_568_statement_compat` |
| `Extremal.conjectures.XE1.erdos_766_statement` / erdos:766 | `Extremal.migration.edge_count.erdos_766_statement_compat` |
| `Extremal.conjectures.XE2.erdos_1009_statement` / erdos:1009 | `Extremal.migration.edge_count.erdos_1009_statement_compat` |
| `Extremal.conjectures.XE2.erdos_1018_statement` / erdos:1018 | `Extremal.migration.edge_count.erdos_1018_statement_compat` |
| `Extremal.conjectures.XE2.erdos_1019_statement` / erdos:1019 | `Extremal.migration.edge_count.erdos_1019_statement_compat` |
| `Extremal.conjectures.XE2.erdos_1080_statement` / erdos:1080 | `Extremal.migration.edge_count.erdos_1080_statement_compat` |
| `Extremal.conjectures.XE2.erdos_22_statement` / erdos:22 | `Extremal.migration.edge_count.erdos_22_statement_compat` |
| `Extremal.conjectures.XE2.erdos_559_statement` / erdos:559 | `Extremal.migration.edge_count.erdos_559_statement_compat` |
| `Extremal.conjectures.XE2.erdos_570_statement` / erdos:570 | `Extremal.migration.edge_count.erdos_570_statement_compat` |
| `Extremal.conjectures.XE2.erdos_613_statement` / erdos:613 | `Extremal.migration.edge_count.erdos_613_statement_compat` |
| `Extremal.conjectures.XE2.erdos_742_statement` / erdos:742 | `Extremal.migration.edge_count.erdos_742_statement_compat` |
| `Extremal.conjectures.XE2.erdos_767_statement` / erdos:767 | `Extremal.migration.edge_count.erdos_767_statement_compat` |
| `Extremal.conjectures.XE2.erdos_801_statement` / erdos:801 | `Extremal.migration.edge_count.erdos_801_statement_compat` |
| `Extremal.conjectures.XE2.erdos_803_statement` / erdos:803 | `Extremal.migration.edge_count.erdos_803_statement_compat` |
| `Extremal.conjectures.XE2.erdos_814_statement` / erdos:814 | `Extremal.migration.edge_count.erdos_814_statement_compat` |
| `Extremal.conjectures.XE2.erdos_816_statement` / erdos:816 | `Extremal.migration.edge_count.erdos_816_statement_compat` |
| `Extremal.conjectures.XE2.erdos_915_statement` / erdos:915 | `Extremal.migration.edge_count.erdos_915_statement_compat` |

Source checks compare frozen text, registry and statement coverage, bridge endpoints, and unchanged statement metadata. They do not prove theorem types.
`python3 meta/migration_report.py edge_count --check --kernel` checks exact closed statement equivalences and all named theorem assumptions in already-built modules.
Helper types, Section context, notation/constructor resolution and compiled dependency closure still require independent review and family-specific Section and kernel dependency evidence.

Excluded distinct variants: `Extremal.conjectures.D2tur.oedges`.

Prior snapshot limitations (explanations and replacement certificates in the inputs): `extremal-graph-theory/theories/migration/bipartition.v#XE2Legacy.erdos_1080_statement`, `extremal-graph-theory/theories/migration/bipartition.v#XE2Original.erdos_1080_statement`, `extremal-graph-theory/theories/migration/complement.v#XE1Legacy.erdos_545_statement`, `extremal-graph-theory/theories/migration/complement.v#XE1Legacy.erdos_566_statement`, `extremal-graph-theory/theories/migration/complement.v#XE1Legacy.erdos_567_statement`, `extremal-graph-theory/theories/migration/complement.v#XE1Legacy.erdos_568_statement`, `extremal-graph-theory/theories/migration/complement.v#XE2Legacy.erdos_570_statement`, `extremal-graph-theory/theories/migration/complement.v#XE1Original.erdos_545_statement`, `extremal-graph-theory/theories/migration/complement.v#XE1Original.erdos_566_statement`, `extremal-graph-theory/theories/migration/complement.v#XE1Original.erdos_567_statement`, `extremal-graph-theory/theories/migration/complement.v#XE1Original.erdos_568_statement`, `extremal-graph-theory/theories/migration/complement.v#XE2Original.erdos_570_statement`, `extremal-graph-theory/theories/migration/consecutive_in_cycle.v#X4Legacy.c5_edge_count_above_turan_statement`, `extremal-graph-theory/theories/migration/consecutive_in_cycle.v#XE1Legacy.erdos_567_statement`, `extremal-graph-theory/theories/migration/consecutive_in_cycle.v#XE2Legacy.incident_chord_extremal`, `extremal-graph-theory/theories/migration/delete_edges.v#XE2Legacy.erdos_613_statement`, `extremal-graph-theory/theories/migration/delete_edges.v#XE2Legacy.erdos_742_statement`, `extremal-graph-theory/theories/migration/internal_vertices.v#XE2Legacy.statement`, `extremal-graph-theory/theories/migration/subgraph_of.v#XE1Legacy.turan_number_for_graph`, `extremal-graph-theory/theories/migration/subgraph_of.v#XE1Legacy.min_turan_over_size_edges`, `extremal-graph-theory/theories/migration/subgraph_of.v#XE1Legacy.erdos_545_statement`, `extremal-graph-theory/theories/migration/subgraph_of.v#XE1Legacy.erdos_548_statement`, `extremal-graph-theory/theories/migration/subgraph_of.v#XE1Legacy.erdos_566_statement`, `extremal-graph-theory/theories/migration/subgraph_of.v#XE1Legacy.erdos_567_statement`, `extremal-graph-theory/theories/migration/subgraph_of.v#XE1Legacy.erdos_568_statement`, `extremal-graph-theory/theories/migration/subgraph_of.v#XE2Legacy.erdos_1018_statement`, `extremal-graph-theory/theories/migration/subgraph_of.v#XE2Legacy.erdos_1019_statement`, `extremal-graph-theory/theories/migration/subgraph_of.v#XE2Legacy.erdos_1080_statement`, `extremal-graph-theory/theories/migration/subgraph_of.v#XE2Legacy.erdos_22_statement`, `extremal-graph-theory/theories/migration/subgraph_of.v#XE2Legacy.erdos_570_statement`, `extremal-graph-theory/theories/migration/subgraph_of.v#XE2Legacy.erdos_803_statement`, `extremal-graph-theory/theories/migration/subgraph_of.v#X78Legacy.h_free_max_cut_three_fourths_surplus_statement`, `extremal-graph-theory/theories/migration/subgraph_of.v#X96Legacy.bollobas_erdos_large_c4_free_subgraph_statement`, `extremal-graph-theory/theories/migration/subgraph_of.v#XE1Original.erdos_567_statement`.
