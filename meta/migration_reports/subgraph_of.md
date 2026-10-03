# Migration report: subgraph-of

Inputs: `meta/migration_reports/subgraph_of.spec.json` and `meta/library_primitives/subgraph-of.json`.
Regenerate: `python3 meta/migration_report.py subgraph_of --write`.
Full evidence: `python3 meta/migration_report.py subgraph_of --details /tmp/migration-details`.

- Canonical: `GTBase.common.has_subgraph`.
- Baseline: `49ddc033ec6be3372ba6813f044fd26922fad16d`.
- Scope: 7 helpers, 35 statements, 54 frozen objects, 259 recorded references.
- Source checks: 562/562 pass; consistent.

| Statement / corpus row | Compatibility theorem |
|---|---|
| `Chromatic.conjectures.X31.chromatic_girth_average_degree_subgraph_statement` / arxiv:1808.01605#01 | `Chromatic.migration.subgraph_of.chromatic_girth_average_degree_subgraph_statement_compat` |
| `Chromatic.conjectures.XE1.erdos_108_statement` / erdos:108 | `Chromatic.migration.subgraph_of.erdos_108_statement_compat` |
| `Chromatic.conjectures.XE1.erdos_628_statement` / erdos:628 | `Chromatic.migration.subgraph_of.erdos_628_statement_compat` |
| `Chromatic.conjectures.XE2.erdos_1091_statement` / erdos:1091 | `Chromatic.migration.subgraph_of.erdos_1091_statement_compat` |
| `Chromatic.conjectures.XE2.erdos_58_statement` / erdos:58 | `Chromatic.migration.subgraph_of.erdos_58_statement_compat` |
| `Chromatic.conjectures.XE2.erdos_762_statement` / erdos:762 | `Chromatic.migration.subgraph_of.erdos_762_statement_compat` |
| `Chromatic.conjectures.XE2.erdos_923_statement` / erdos:923 | `Chromatic.migration.subgraph_of.erdos_923_statement_compat` |
| `Extremal.conjectures.XE1.erdos_1035_statement` / erdos:1035 | `Extremal.migration.subgraph_of.erdos_1035_statement_compat` |
| `Extremal.conjectures.XE1.erdos_545_statement` / erdos:545 | `Extremal.migration.subgraph_of.erdos_545_statement_compat` |
| `Extremal.conjectures.XE1.erdos_548_statement` / erdos:548 | `Extremal.migration.subgraph_of.erdos_548_statement_compat` |
| `Extremal.conjectures.XE1.erdos_550_statement` / erdos:550 | `Extremal.migration.subgraph_of.erdos_550_statement_compat` |
| `Extremal.conjectures.XE1.erdos_552_statement` / erdos:552 | `Extremal.migration.subgraph_of.erdos_552_statement_compat` |
| `Extremal.conjectures.XE1.erdos_566_statement` / erdos:566 | `Extremal.migration.subgraph_of.erdos_566_statement_compat` |
| `Extremal.conjectures.XE1.erdos_567_statement` / erdos:567 | `Extremal.migration.subgraph_of.erdos_567_statement_compat` |
| `Extremal.conjectures.XE1.erdos_568_statement` / erdos:568 | `Extremal.migration.subgraph_of.erdos_568_statement_compat` |
| `Extremal.conjectures.XE1.erdos_766_statement` / erdos:766 | `Extremal.migration.subgraph_of.erdos_766_statement_compat` |
| `Extremal.conjectures.XE1.erdos_802_statement` / erdos:802 | `Extremal.migration.subgraph_of.erdos_802_statement_compat` |
| `Extremal.conjectures.XE1.erdos_812_statement` / erdos:812 | `Extremal.migration.subgraph_of.erdos_812_statement_compat` |
| `Extremal.conjectures.XE1.erdos_85_statement` / erdos:85 | `Extremal.migration.subgraph_of.erdos_85_statement_compat` |
| `Extremal.conjectures.XE1.erdos_87_statement` / erdos:87 | `Extremal.migration.subgraph_of.erdos_87_statement_compat` |
| `Extremal.conjectures.XE2.erdos_1018_statement` / erdos:1018 | `Extremal.migration.subgraph_of.erdos_1018_statement_compat` |
| `Extremal.conjectures.XE2.erdos_1019_statement` / erdos:1019 | `Extremal.migration.subgraph_of.erdos_1019_statement_compat` |
| `Extremal.conjectures.XE2.erdos_1080_statement` / erdos:1080 | `Extremal.migration.subgraph_of.erdos_1080_statement_compat` |
| `Extremal.conjectures.XE2.erdos_22_statement` / erdos:22 | `Extremal.migration.subgraph_of.erdos_22_statement_compat` |
| `Extremal.conjectures.XE2.erdos_547_statement` / erdos:547 | `Extremal.migration.subgraph_of.erdos_547_statement_compat` |
| `Extremal.conjectures.XE2.erdos_549_statement` / erdos:549 | `Extremal.migration.subgraph_of.erdos_549_statement_compat` |
| `Extremal.conjectures.XE2.erdos_570_statement` / erdos:570 | `Extremal.migration.subgraph_of.erdos_570_statement_compat` |
| `Extremal.conjectures.XE2.erdos_800_statement` / erdos:800 | `Extremal.migration.subgraph_of.erdos_800_statement_compat` |
| `Extremal.conjectures.XE2.erdos_803_statement` / erdos:803 | `Extremal.migration.subgraph_of.erdos_803_statement_compat` |
| `Extremal.conjectures.X59.c4_free_subgraph_polynomial_average_degree_statement` / arxiv:2307.08361#01 | `Extremal.migration.subgraph_of.c4_free_subgraph_polynomial_average_degree_statement_compat` |
| `Extremal.conjectures.X78.h_free_max_cut_three_fourths_surplus_statement` / studies:std_alon_krivelevich_sudakov_max_cut_exponent_conjec | `Extremal.migration.subgraph_of.h_free_max_cut_three_fourths_surplus_statement_compat` |
| `Extremal.conjectures.X96.bollobas_erdos_large_c4_free_subgraph_statement` / studies:std_bollob_s_erd_s_problem_on_large_c_free_subgraphs | `Extremal.migration.subgraph_of.bollobas_erdos_large_c4_free_subgraph_statement_compat` |
| `Extremal.conjectures.X98.polynomial_kuhn_osthus_induced_subdivision_statement` / studies:std_bonamy_et_al_polynomial_k_hn_osthus_conjecture | `Extremal.migration.subgraph_of.polynomial_kuhn_osthus_induced_subdivision_statement_compat` |
| `GTMisc.conjectures.U13.subgraph_of_large_average_degree_and_large_average_d_statement` / opg:subgraph_of_large_average_degree_and_large_average_degree | `GTMisc.migration.subgraph_of.subgraph_of_large_average_degree_and_large_average_d_statement_compat` |
| `GTMisc.conjectures.XE2.erdos_715_statement` / erdos:715 | `GTMisc.migration.subgraph_of.erdos_715_statement_compat` |

Source checks compare frozen text, registry and statement coverage, bridge endpoints, and unchanged statement metadata. They do not prove theorem types.
`python3 meta/migration_report.py subgraph_of --check --kernel` checks exact closed statement equivalences and all named theorem assumptions in already-built modules.
Helper types, Section context, notation/constructor resolution and compiled dependency closure still require independent review and family-specific Section and kernel dependency evidence.

Prior snapshot limitations (explanations and replacement certificates in the inputs): `extremal-graph-theory/theories/migration/consecutive_in_path.v#X98Legacy.statement`, `chromatic-theory/theories/migration/consecutive_in_cycle.v#XE2Legacy.erdos_1091_statement`, `extremal-graph-theory/theories/migration/consecutive_in_cycle.v#XE1Legacy.erdos_567_statement`, `extremal-graph-theory/theories/migration/complement.v#XE1Legacy.graph_ramsey`, `chromatic-theory/theories/migration/genuine_cycle.v#XE2Legacy.erdos_58_statement`, `chromatic-theory/theories/migration/genuine_cycle.v#XE2Legacy.erdos_1091_statement`, `extremal-graph-theory/theories/migration/bipartition.v#XE2Legacy.erdos_1080_statement`, `extremal-graph-theory/theories/migration/bipartition.v#XE2Legacy.erdos_549_statement`, `extremal-graph-theory/theories/migration/edge_count.v#X78Legacy.h_free_max_cut_three_fourths_surplus_statement`, `extremal-graph-theory/theories/migration/edge_count.v#X96Legacy.bollobas_erdos_large_c4_free_subgraph_statement`, `extremal-graph-theory/theories/migration/edge_count.v#XE1Legacy.turan_number_for_graph`, `extremal-graph-theory/theories/migration/edge_count.v#XE1Legacy.erdos_545_statement`, `extremal-graph-theory/theories/migration/edge_count.v#XE1Legacy.erdos_548_statement`, `extremal-graph-theory/theories/migration/edge_count.v#XE1Legacy.erdos_566_statement`, `extremal-graph-theory/theories/migration/edge_count.v#XE1Legacy.erdos_567_statement`, `extremal-graph-theory/theories/migration/edge_count.v#XE1Legacy.erdos_568_statement`, `extremal-graph-theory/theories/migration/edge_count.v#XE2Legacy.erdos_1018_statement`, `extremal-graph-theory/theories/migration/edge_count.v#XE2Legacy.erdos_1019_statement`, `extremal-graph-theory/theories/migration/edge_count.v#XE2Legacy.erdos_1080_statement`, `extremal-graph-theory/theories/migration/edge_count.v#XE2Legacy.erdos_22_statement`, `extremal-graph-theory/theories/migration/edge_count.v#XE2Legacy.erdos_570_statement`, `extremal-graph-theory/theories/migration/edge_count.v#XE2Legacy.erdos_803_statement`, `extremal-graph-theory/theories/migration/cut_size.v#X78Legacy.h_free_max_cut_three_fourths_surplus_statement`, `extremal-graph-theory/theories/migration/min_degree_at_least.v#XE1Legacy.erdos_566_statement`, `extremal-graph-theory/theories/migration/min_degree_at_least.v#XE1Legacy.erdos_567_statement`, `extremal-graph-theory/theories/migration/min_degree_at_least.v#XE1Legacy.erdos_568_statement`, `extremal-graph-theory/theories/migration/min_degree_at_least.v#XE1Legacy.c4_forcing_min_degree`, `extremal-graph-theory/theories/migration/min_degree_at_least.v#XE2Legacy.erdos_570_statement`, `extremal-graph-theory/theories/migration/min_degree_at_least.v#XE1Legacy.erdos_545_statement`, `extremal-graph-theory/theories/migration/cycle_lengths.v#X59Legacy.c4_free_subgraph_polynomial_average_degree_statement`, `extremal-graph-theory/theories/migration/cycle_lengths.v#X96Legacy.bollobas_erdos_large_c4_free_subgraph_statement`, `extremal-graph-theory/theories/migration/min_degree.v#XE2Legacy.erdos_803_statement`, `extremal-graph-theory/theories/migration/whole_tree.v#XE1Legacy.erdos_548_statement`, `extremal-graph-theory/theories/migration/whole_tree.v#XE1Legacy.erdos_550_statement`, `extremal-graph-theory/theories/migration/whole_tree.v#XE1Legacy.erdos_568_statement`, `extremal-graph-theory/theories/migration/whole_tree.v#XE2Legacy.erdos_547_statement`, `extremal-graph-theory/theories/migration/whole_tree.v#XE2Legacy.erdos_549_statement`, `extremal-graph-theory/theories/migration/model_support.v#X98Legacy.polynomial_kuhn_osthus_induced_subdivision_statement`, `extremal-graph-theory/theories/migration/induced_subdivisions.v#X98Legacy.polynomial_kuhn_osthus_induced_subdivision_statement`.
