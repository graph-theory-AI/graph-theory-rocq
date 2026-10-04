# Migration report: induced-cycle

Inputs: `meta/migration_reports/induced_cycles.spec.json` and `meta/library_primitives/induced-cycle.json`.
Regenerate: `python3 meta/migration_report.py induced_cycles --write`.
Full evidence: `python3 meta/migration_report.py induced_cycles --details /tmp/migration-details`.

- Canonical: `GTBase.induced_cycles.chordless_cycle`.
- Baseline: `7d8cc47829b045a122d6f6421ddc2d928dd9675a`.
- Scope: 7 helpers, 14 statements, 44 frozen objects, 160 recorded references.
- Source checks: 438/438 pass; consistent.

| Statement / corpus row | Compatibility theorem |
|---|---|
| `Chromatic.conjectures.X3.bounded_clique_consecutive_hole_lengths_statement` / arxiv:1509.06563#00 | `Chromatic.migration.induced_cycles.bounded_clique_consecutive_hole_lengths_statement_compat` |
| `Chromatic.conjectures.X3.bounded_gaps_sets_are_constricting_statement` / arxiv:1509.06563#01 | `Chromatic.migration.induced_cycles.bounded_gaps_sets_are_constricting_statement_compat` |
| `Chromatic.conjectures.X3.rainbow_consecutive_vertices_in_hole_statement` / arxiv:1702.01094#00 | `Chromatic.migration.induced_cycles.rainbow_consecutive_vertices_in_hole_statement_compat` |
| `Chromatic.conjectures.X3.clique_or_consecutive_holes_statement` / arxiv:1705.04609#00 | `Chromatic.migration.induced_cycles.clique_or_consecutive_holes_statement_compat` |
| `Chromatic.conjectures.X160.density_zero_constricting_set_statement` / arxiv:1509.06563#02 | `Chromatic.migration.induced_cycles.density_zero_constricting_set_statement_compat` |
| `Extremal.conjectures.D2str.geodesic_cycles_and_tuttes_theorem_statement` / opg:geodesic_cycles_and_tuttes_theorem | `Extremal.migration.induced_cycles.geodesic_cycles_and_tuttes_theorem_statement_compat` |
| `GTMisc.conjectures.X91.avoidable_path_or_pk_free_statement` / studies:std_beisegel_chudnovsky_gurvich_milani_servatius_con | `GTMisc.migration.induced_cycles.avoidable_path_or_pk_free_statement_compat` |
| `Minor.conjectures.X27.bounded_degree_even_hole_free_bounded_treewidth_statement` / arxiv:2008.05504#00 | `Minor.migration.induced_cycles.bounded_degree_even_hole_free_bounded_treewidth_statement_compat` |
| `Minor.conjectures.X42.even_hole_k4_diamond_free_bounded_treewidth_statement` / arxiv:2001.01607#00 | `Minor.migration.induced_cycles.even_hole_k4_diamond_free_bounded_treewidth_statement_compat` |
| `Minor.conjectures.X220.theta_prism_even_wheel_free_bounded_treewidth_statement` / arxiv:2203.06775#00 | `Minor.migration.induced_cycles.theta_prism_even_wheel_free_bounded_treewidth_statement_compat` |
| `Minor.conjectures.X220.even_hole_kt_free_logarithmic_treewidth_statement` / arxiv:2305.16258#01 | `Minor.migration.induced_cycles.even_hole_kt_free_logarithmic_treewidth_statement_compat` |
| `Minor.conjectures.X220.even_hole_diamond_free_bounded_tree_alpha_statement` / arxiv:2305.16258#00 | `Minor.migration.induced_cycles.even_hole_diamond_free_bounded_tree_alpha_statement_compat` |
| `Packing.conjectures.XE1.erdos_81_statement` / erdos:81 | `Packing.migration.induced_cycles.erdos_81_statement_compat` |
| `GTMisc.conjectures.U13.two_colouring_a_graph_without_a_monochromatic_maximu_statement` / opg:2_colouring_a_graph_without_a_monochromatic_maximum_clique | `GTMisc.migration.induced_cycles.two_colouring_a_graph_without_a_monochromatic_maximu_statement_compat` |

Source checks compare frozen text, registry and statement coverage, bridge endpoints, and unchanged statement metadata. They do not prove theorem types.
`python3 meta/migration_report.py induced_cycles --check --kernel` checks exact closed statement equivalences and all named theorem assumptions in already-built modules.
Helper types, Section context, notation/constructor resolution and compiled dependency closure still require independent review and family-specific Section and kernel dependency evidence.

Excluded distinct variants: `Extremal.conjectures.X49.x49_has_induced_cycle`, `Extremal.conjectures.X60.x60_has_induced_cycle`, `GTMisc.conjectures.X29.x29_has_induced_cycle`, `Extremal.conjectures.X115.x115_odd_induced_cycle`, `Chromatic.conjectures.X161.x161_has_four_hole`.

Prior snapshot limitations (explanations and replacement certificates in the inputs): `chromatic-theory/theories/migration/proper_colouring.v#X3Legacy.rainbow_consecutive_vertices_in_hole_statement`, `graph-theory-misc/theories/migration/consecutive_in_path.v#X91Legacy.avoidable_path`, `graph-theory-misc/theories/migration/induced_paths.v#X91Legacy.x91_avoidable_path`, `minor-theory/theories/migration/bag_decompositions.v#Legacy.bounded_degree_even_hole_free_bounded_treewidth_statement`, `minor-theory/theories/migration/bag_decompositions.v#Legacy.even_hole_k4_diamond_free_bounded_treewidth_statement`, `minor-theory/theories/migration/induced_free.v#X42Legacy.statement`, `minor-theory/theories/migration/model_support.v#X220Legacy.theta_prism_even_wheel_free_bounded_treewidth_statement`, `graph-theory-misc/theories/migration/monochromatic.v#U13Legacy.two_colouring_a_graph_without_a_monochromatic_maximu_statement`, `packing-theory/theories/migration/chordal.v#Legacy.xe1_chordal`.
