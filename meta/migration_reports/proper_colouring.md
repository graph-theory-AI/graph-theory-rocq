# Migration report: proper-colouring

Inputs: `meta/migration_reports/proper_colouring.spec.json` and `meta/library_primitives/proper-colouring.json`.
Regenerate: `python3 meta/migration_report.py proper_colouring --write`.
Full evidence: `python3 meta/migration_report.py proper_colouring --details /tmp/migration-details`.

- Canonical: `GTBase.colourings.proper_colouring`.
- Baseline: `a6db537386d7092db506526fbcfd2dbe9760ed5e`.
- Scope: 8 helpers, 10 statements, 26 frozen objects, 65 recorded references.
- Source checks: 236/236 pass; consistent.

| Statement / corpus row | Compatibility theorem |
|---|---|
| `Chromatic.conjectures.X3.rainbow_consecutive_vertices_in_hole_statement` / arxiv:1702.01094#00 | `Chromatic.migration.proper_colouring.rainbow_consecutive_vertices_in_hole_statement_compat` |
| `Chromatic.conjectures.X63.cubic_two_homogeneous_four_colour_statement` / arxiv:2511.02892#04 | `Chromatic.migration.proper_colouring.cubic_two_homogeneous_four_colour_statement_compat` |
| `Chromatic.conjectures.X64.finite_bridgeless_cubic_two_homogeneous_exceptions_statement` / arxiv:2511.02892#05 | `Chromatic.migration.proper_colouring.finite_bridgeless_cubic_two_homogeneous_exceptions_statement_compat` |
| `Chromatic.conjectures.X68.triangle_free_planar_distant_precolouring_extension_statement` / arxiv:0911.0885#00 | `Chromatic.migration.proper_colouring.triangle_free_planar_distant_precolouring_extension_statement_compat` |
| `Chromatic.conjectures.X83.aravind_rainbow_induced_chromatic_path_statement` / studies:std_aravind_s_rainbow_induced_path_conjecture | `Chromatic.migration.proper_colouring.aravind_rainbow_induced_chromatic_path_statement_compat` |
| `Chromatic.conjectures.X109.cereceda_degenerate_recolouring_quadratic_diameter_statement` / studies:std_cereceda_s_conjecture | `Chromatic.migration.proper_colouring.cereceda_degenerate_recolouring_quadratic_diameter_statement_compat` |
| `Chromatic.conjectures.X162.wsk_triangular_lattice_q5_kempe_class_statement` / arxiv:1510.06964#00 | `Chromatic.migration.proper_colouring.wsk_triangular_lattice_q5_kempe_class_statement_compat` |
| `Chromatic.conjectures.X187.planar_triangle_free_request_graph_fraction_statement` / arxiv:1702.00588#00 | `Chromatic.migration.proper_colouring.planar_triangle_free_request_graph_fraction_statement_compat` |
| `Spectral.conjectures.D5.does_the_symmetric_chromatic_function_distinguish_tr_statement` / opg:does_the_symmetric_chromatic_function_distinguish_trees | `Spectral.migration.proper_colouring.does_the_symmetric_chromatic_function_distinguish_tr_statement_compat` |
| `Infinite.conjectures.D4doa.counting_3_colorings_of_the_hex_lattice_statement` / opg:counting_3_colorings_of_the_hex_lattice | `Infinite.migration.proper_colouring.counting_3_colorings_of_the_hex_lattice_statement_compat` |

Source checks compare frozen text, registry and statement coverage, bridge endpoints, and unchanged statement metadata. They do not prove theorem types.
`python3 meta/migration_report.py proper_colouring --check --kernel` checks exact closed statement equivalences and all named theorem assumptions in already-built modules.
Helper types, Section context, notation/constructor resolution and compiled dependency closure still require independent review and family-specific Section and kernel dependency evidence.

Prior snapshot limitations (explanations and replacement certificates in the inputs): `chromatic-theory/theories/migration/simple_edges.v#X64Legacy.statement`, `chromatic-theory/theories/migration/delete_edge.v#X64Legacy.finite_bridgeless_cubic_two_homogeneous_exceptions_statement`, `chromatic-theory/theories/migration/delete_edge.v#X64Original.finite_bridgeless_cubic_two_homogeneous_exceptions_statement`, `chromatic-theory/theories/migration/consecutive_in_path.v#X83Legacy.statement`.
