# Migration report: induced-path

Inputs: `meta/migration_reports/induced_paths.spec.json` and `meta/library_primitives/induced-path.json`.
Regenerate: `python3 meta/migration_report.py induced_paths --write`.
Full evidence: `python3 meta/migration_report.py induced_paths --details /tmp/migration-details`.

- Canonical: `GTBase.induced_paths.induced_path_between`.
- Baseline: `00e59d190216a0cf26724bb6334d3aceee0f3b68`.
- Scope: 8 helpers, 8 statements, 31 frozen objects, 140 recorded references.
- Source checks: 289/289 pass; consistent.

| Statement / corpus row | Compatibility theorem |
|---|---|
| `Chromatic.conjectures.X3.stable_cover_unique_induced_path_statement` / arxiv:1702.01094#01 | `Chromatic.migration.induced_paths.stable_cover_unique_induced_path_statement_compat` |
| `Chromatic.conjectures.X83.aravind_rainbow_induced_chromatic_path_statement` / studies:std_aravind_s_rainbow_induced_path_conjecture | `Chromatic.migration.induced_paths.aravind_rainbow_induced_chromatic_path_statement_compat` |
| `GTMisc.conjectures.X91.avoidable_path_or_pk_free_statement` / studies:std_beisegel_chudnovsky_gurvich_milani_servatius_con | `GTMisc.migration.induced_paths.avoidable_path_or_pk_free_statement_compat` |
| `Extremal.conjectures.X98.polynomial_kuhn_osthus_induced_subdivision_statement` / studies:std_bonamy_et_al_polynomial_k_hn_osthus_conjecture | `Extremal.migration.induced_paths.polynomial_kuhn_osthus_induced_subdivision_statement_compat` |
| `GTMisc.conjectures.X114.subcubic_induced_subdivision_np_complete_statement` / studies:std_chudnovsky_seymour_trotignon_question_on_subcubi | `GTMisc.migration.induced_paths.subcubic_induced_subdivision_np_complete_statement_compat` |
| `Minor.conjectures.X67.theta_triangle_free_bounded_degree_treewidth_statement` / arxiv:2001.01607#01 | `Minor.migration.induced_paths.theta_triangle_free_bounded_degree_treewidth_statement_compat` |
| `Packing.conjectures.U9.lovasz_path_removal_statement` / opg:lovasz_path_removal_conjecture | `Packing.migration.induced_paths.lovasz_path_removal_statement_compat` |
| `GTMisc.conjectures.X208.Pt_free_maximum_independent_set_polytime_statement` / arxiv:1803.05396#01 | `GTMisc.migration.induced_paths.Pt_free_maximum_independent_set_polytime_statement_compat` |

Source checks compare frozen text, registry and statement coverage, bridge endpoints, and unchanged statement metadata. They do not prove theorem types.
`python3 meta/migration_report.py induced_paths --check --kernel` checks exact closed statement equivalences and all named theorem assumptions in already-built modules.
Helper types, Section context, notation/constructor resolution and compiled dependency closure still require independent review and family-specific Section and kernel dependency evidence.

Excluded distinct variants: `Chromatic.conjectures.X177.x177_induced_path_between`, `Chromatic.conjectures.X218.x218_induced_run`, `Chromatic.conjectures.X218.x218_path_induced_copy`, `GTMisc.conjectures.X91.x91_induced_cycle`.

Prior snapshot limitations (explanations and replacement certificates in the inputs): `chromatic-theory/theories/migration/path_vertices.v#X3Legacy.statement`, `extremal-graph-theory/theories/migration/consecutive_in_path.v#X98Legacy.statement`, `extremal-graph-theory/theories/migration/induced_subdivisions.v#Legacy.x98_induced_subdivision_model`, `extremal-graph-theory/theories/migration/model_support.v#X98Legacy.x98_induced_subdivision_model`, `extremal-graph-theory/theories/migration/subgraph_of.v#X98Legacy.polynomial_kuhn_osthus_induced_subdivision_statement`, `graph-theory-misc/theories/migration/consecutive_in_cycle.v#X91Legacy.avoidable_path`, `graph-theory-misc/theories/migration/consecutive_in_cycle.v#X91Legacy.avoidable_path_or_pk_free_statement`, `graph-theory-misc/theories/migration/consecutive_in_path.v#X114Legacy.hisc_problem`, `graph-theory-misc/theories/migration/induced_subdivisions.v#Legacy.x114_induced_subdivision_model`, `graph-theory-misc/theories/migration/model_support.v#X114Legacy.x114_induced_subdivision_model`, `graph-theory-misc/theories/migration/subcubic.v#X114Legacy.subcubic_induced_subdivision_np_complete_statement`, `minor-theory/theories/migration/bag_decompositions.v#Legacy.theta_triangle_free_bounded_degree_treewidth_statement`, `minor-theory/theories/migration/path_vertices.v#X67Legacy.theta`, `graph-theory-misc/theories/migration/stable_sets.v#X208Legacy.Pt_free_maximum_independent_set_polytime_statement`, `chromatic-theory/theories/migration/stable_sets.v#X3Legacy.stable_cover_unique_induced_path_statement`.
