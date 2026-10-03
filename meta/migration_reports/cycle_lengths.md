# Migration report: cycle-lengths

Inputs: `meta/migration_reports/cycle_lengths.spec.json` and `meta/library_primitives/cycle-lengths.json`.
Regenerate: `python3 meta/migration_report.py cycle_lengths --write`.
Full evidence: `python3 meta/migration_report.py cycle_lengths --details /tmp/migration-details`.

- Canonical: `GTBase.walks_paths.has_ucycle_length`.
- Baseline: `4b63976bad086439fa79f74eaccd270cd1291eb9`.
- Scope: 5 helpers, 6 statements, 15 frozen objects, 38 recorded references.
- Source checks: 166/166 pass; consistent.

| Statement / corpus row | Compatibility theorem |
|---|---|
| `Chromatic.conjectures.X28.planar_no_4_to_6_cycles_three_choosable_statement` / arxiv:1508.03437#00 | `Chromatic.migration.cycle_lengths.planar_no_4_to_6_cycles_three_choosable_statement_compat` |
| `Chromatic.conjectures.X159.planar_no_cycles_4_to_8_correspondence_chromatic_three_statement` / arxiv:1508.03437#01 | `Chromatic.migration.cycle_lengths.planar_no_cycles_4_to_8_correspondence_chromatic_three_statement_compat` |
| `Chromatic.conjectures.X204.planar_no_4_5_cycles_fractional_below_eleven_thirds_statement` / arxiv:1802.04179#01 | `Chromatic.migration.cycle_lengths.planar_no_4_5_cycles_fractional_below_eleven_thirds_statement_compat` |
| `Extremal.conjectures.X59.c4_free_subgraph_polynomial_average_degree_statement` / arxiv:2307.08361#01 | `Extremal.migration.cycle_lengths.c4_free_subgraph_polynomial_average_degree_statement_compat` |
| `Extremal.conjectures.X76.ck_free_max_cut_polynomial_surplus_statement` / studies:std_alon_et_al_c_k_free_max_cut_conjecture | `Extremal.migration.cycle_lengths.ck_free_max_cut_polynomial_surplus_statement_compat` |
| `Extremal.conjectures.X96.bollobas_erdos_large_c4_free_subgraph_statement` / studies:std_bollob_s_erd_s_problem_on_large_c_free_subgraphs | `Extremal.migration.cycle_lengths.bollobas_erdos_large_c4_free_subgraph_statement_compat` |

Source checks compare frozen text, registry and statement coverage, bridge endpoints, and unchanged statement metadata. They do not prove theorem types.
`python3 meta/migration_report.py cycle_lengths --check --kernel` checks exact closed statement equivalences and all named theorem assumptions in already-built modules.
Helper types, Section context, notation/constructor resolution and compiled dependency closure still require independent review and family-specific Section and kernel dependency evidence.

Excluded distinct variants: `Extremal.conjectures.X84.x84_has_cycle_length`, `Cycle.conjectures.XE2.xe2_cycle_lengths`, `Cycle.conjectures.XE2.xe2_all_cycle_lengths_in`, `Chromatic.conjectures.XE2.xe2_odd_cycle_lengths_bounded`, `Digraph.conjectures.X19.x19_distinct_cycle_lengths`.

Prior snapshot limitations (explanations and replacement certificates in the inputs): `extremal-graph-theory/theories/migration/subgraph_of.v#X59Legacy.c4_free_subgraph_polynomial_average_degree_statement`, `extremal-graph-theory/theories/migration/subgraph_of.v#X96Legacy.bollobas_erdos_large_c4_free_subgraph_statement`, `extremal-graph-theory/theories/migration/edge_count.v#X76Legacy.ck_free_max_cut_polynomial_surplus_statement`, `extremal-graph-theory/theories/migration/edge_count.v#X76Original.ck_free_max_cut_polynomial_surplus_statement`, `extremal-graph-theory/theories/migration/edge_count.v#X96Legacy.bollobas_erdos_large_c4_free_subgraph_statement`, `extremal-graph-theory/theories/migration/edge_count.v#X96Original.bollobas_erdos_large_c4_free_subgraph_statement`, `extremal-graph-theory/theories/migration/cut_size.v#X76Legacy.ck_free_max_cut_polynomial_surplus_statement`, `extremal-graph-theory/theories/migration/cut_size.v#X76Original.ck_free_max_cut_polynomial_surplus_statement`.
