# Migration report: consecutive-in-cycle

Inputs: `meta/migration_reports/consecutive_in_cycle.spec.json` and `meta/library_primitives/consecutive-in-cycle.json`.
Regenerate: `python3 meta/migration_report.py consecutive_in_cycle --write`.
Full evidence: `python3 meta/migration_report.py consecutive_in_cycle --details /tmp/migration-details`.

- Canonical: `GTBase.walks_paths.seq_cyclic_consecutiveb`.
- Baseline: `49ddc033ec6be3372ba6813f044fd26922fad16d`.
- Scope: 7 helpers, 18 statements, 59 frozen objects, 162 recorded references.
- Source checks: 515/515 pass; consistent.

| Statement / corpus row | Compatibility theorem |
|---|---|
| `Chromatic.conjectures.X3.bounded_clique_consecutive_hole_lengths_statement` / arxiv:1509.06563#00 | `Chromatic.migration.consecutive_in_cycle.bounded_clique_consecutive_hole_lengths_statement_compat` |
| `Chromatic.conjectures.X3.bounded_gaps_sets_are_constricting_statement` / arxiv:1509.06563#01 | `Chromatic.migration.consecutive_in_cycle.bounded_gaps_sets_are_constricting_statement_compat` |
| `Chromatic.conjectures.X3.rainbow_consecutive_vertices_in_hole_statement` / arxiv:1702.01094#00 | `Chromatic.migration.consecutive_in_cycle.rainbow_consecutive_vertices_in_hole_statement_compat` |
| `Chromatic.conjectures.X3.clique_or_consecutive_holes_statement` / arxiv:1705.04609#00 | `Chromatic.migration.consecutive_in_cycle.clique_or_consecutive_holes_statement_compat` |
| `Chromatic.conjectures.X160.density_zero_constricting_set_statement` / arxiv:1509.06563#02 | `Chromatic.migration.consecutive_in_cycle.density_zero_constricting_set_statement_compat` |
| `Chromatic.conjectures.XE2.erdos_1091_statement` / erdos:1091 | `Chromatic.migration.consecutive_in_cycle.erdos_1091_statement_compat` |
| `Chromatic.conjectures.XE2.erdos_842_statement` / erdos:842 | `Chromatic.migration.consecutive_in_cycle.erdos_842_statement_compat` |
| `Cycle.conjectures.X9.min_degree_three_linearly_many_chords_cycle_statement` / arxiv:2502.04726#03 | `Cycle.migration.consecutive_in_cycle.min_degree_three_linearly_many_chords_cycle_statement_compat` |
| `Extremal.conjectures.X4.c5_edge_count_above_turan_statement` / erdos:608 | `Extremal.migration.consecutive_in_cycle.c5_edge_count_above_turan_statement_compat` |
| `Extremal.conjectures.XE1.erdos_567_statement` / erdos:567 | `Extremal.migration.consecutive_in_cycle.erdos_567_statement_compat` |
| `Extremal.conjectures.XE2.erdos_767_statement` / erdos:767 | `Extremal.migration.consecutive_in_cycle.erdos_767_statement_compat` |
| `Extremal.conjectures.D2str.geodesic_cycles_and_tuttes_theorem_statement` / opg:geodesic_cycles_and_tuttes_theorem | `Extremal.migration.consecutive_in_cycle.geodesic_cycles_and_tuttes_theorem_statement_compat` |
| `GTMisc.conjectures.X91.avoidable_path_or_pk_free_statement` / studies:std_beisegel_chudnovsky_gurvich_milani_servatius_con | `GTMisc.migration.consecutive_in_cycle.avoidable_path_or_pk_free_statement_compat` |
| `Minor.conjectures.X27.bounded_degree_even_hole_free_bounded_treewidth_statement` / arxiv:2008.05504#00 | `Minor.migration.consecutive_in_cycle.bounded_degree_even_hole_free_bounded_treewidth_statement_compat` |
| `Minor.conjectures.X42.even_hole_k4_diamond_free_bounded_treewidth_statement` / arxiv:2001.01607#00 | `Minor.migration.consecutive_in_cycle.even_hole_k4_diamond_free_bounded_treewidth_statement_compat` |
| `Minor.conjectures.X220.theta_prism_even_wheel_free_bounded_treewidth_statement` / arxiv:2203.06775#00 | `Minor.migration.consecutive_in_cycle.theta_prism_even_wheel_free_bounded_treewidth_statement_compat` |
| `Minor.conjectures.X220.even_hole_kt_free_logarithmic_treewidth_statement` / arxiv:2305.16258#01 | `Minor.migration.consecutive_in_cycle.even_hole_kt_free_logarithmic_treewidth_statement_compat` |
| `Minor.conjectures.X220.even_hole_diamond_free_bounded_tree_alpha_statement` / arxiv:2305.16258#00 | `Minor.migration.consecutive_in_cycle.even_hole_diamond_free_bounded_tree_alpha_statement_compat` |

Source checks compare frozen text, registry and statement coverage, bridge endpoints, and unchanged statement metadata. They do not prove theorem types.
`python3 meta/migration_report.py consecutive_in_cycle --check --kernel` checks exact closed statement equivalences and all named theorem assumptions in already-built modules.
Helper types, Section context, notation/constructor resolution and compiled dependency closure still require independent review and family-specific Section and kernel dependency evidence.

Excluded distinct variants: `Packing.conjectures.XE1.xe1_induced_cycle`, `Cycle.conjectures.XE1.xe1_cycle_edges`, `Cycle.conjectures.U6.cyc_pairs`.

Prior snapshot limitations (explanations and replacement certificates in the inputs): `minor-theory/theories/migration/induced_free.v#X42Legacy.statement`, `graph-theory-misc/theories/migration/consecutive_in_path.v#X91Legacy.avoidable_path`, `chromatic-theory/theories/migration/proper_colouring.v#X3Legacy.rainbow_consecutive_vertices_in_hole_statement`, `chromatic-theory/theories/migration/subgraph_of.v#XE2Legacy.erdos_1091_statement`, `extremal-graph-theory/theories/migration/subgraph_of.v#XE1Legacy.erdos_567_statement`, `extremal-graph-theory/theories/migration/complement.v#XE1Legacy.erdos_567_statement`.
