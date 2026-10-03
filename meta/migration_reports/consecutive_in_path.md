# Migration report: consecutive-in-path

Inputs: `meta/migration_reports/consecutive_in_path.spec.json` and `meta/library_primitives/consecutive-in-path.json`.
Regenerate: `python3 meta/migration_report.py consecutive_in_path --write`.
Full evidence: `python3 meta/migration_report.py consecutive_in_path --details /tmp/migration-details`.

- Canonical: `GTBase.walks_paths.seq_consecutive`.
- Baseline: `ceadac8a097e951709afd63b65546f1a2513e0a5`.
- Scope: 5 helpers, 6 statements, 33 frozen objects, 71 recorded references.
- Source checks: 246/246 pass; consistent.

| Statement / corpus row | Compatibility theorem |
|---|---|
| `Chromatic.conjectures.X3.stable_cover_unique_induced_path_statement` / arxiv:1702.01094#01 | `Chromatic.migration.consecutive_in_path.stable_cover_unique_induced_path_statement_compat` |
| `Chromatic.conjectures.X83.aravind_rainbow_induced_chromatic_path_statement` / studies:std_aravind_s_rainbow_induced_path_conjecture | `Chromatic.migration.consecutive_in_path.aravind_rainbow_induced_chromatic_path_statement_compat` |
| `Extremal.conjectures.X98.polynomial_kuhn_osthus_induced_subdivision_statement` / studies:std_bonamy_et_al_polynomial_k_hn_osthus_conjecture | `Extremal.migration.consecutive_in_path.polynomial_kuhn_osthus_induced_subdivision_statement_compat` |
| `GTMisc.conjectures.X114.subcubic_induced_subdivision_np_complete_statement` / studies:std_chudnovsky_seymour_trotignon_question_on_subcubi | `GTMisc.migration.consecutive_in_path.subcubic_induced_subdivision_np_complete_statement_compat` |
| `GTMisc.conjectures.X91.avoidable_path_or_pk_free_statement` / studies:std_beisegel_chudnovsky_gurvich_milani_servatius_con | `GTMisc.migration.consecutive_in_path.avoidable_path_or_pk_free_statement_compat` |
| `Minor.conjectures.X67.theta_triangle_free_bounded_degree_treewidth_statement` / arxiv:2001.01607#01 | `Minor.migration.consecutive_in_path.theta_triangle_free_bounded_degree_treewidth_statement_compat` |

Source checks compare frozen text, registry and statement coverage, bridge endpoints, and unchanged statement metadata. They do not prove theorem types.
`python3 meta/migration_report.py consecutive_in_path --check --kernel` checks exact closed statement equivalences and all named theorem assumptions in already-built modules.
Helper types, Section context, notation/constructor resolution and compiled dependency closure still require independent review and family-specific Section and kernel dependency evidence.

Prior snapshot limitations (explanations and replacement certificates in the inputs): `chromatic-theory/theories/migration/path_vertices.v#X3Legacy.statement`, `minor-theory/theories/migration/path_vertices.v#X67Legacy.theta`, `graph-theory-misc/theories/migration/consecutive_in_cycle.v#X91Legacy.avoidable_path`, `graph-theory-misc/theories/migration/consecutive_in_cycle.v#X91Legacy.avoidable_path_or_pk_free_statement`, `extremal-graph-theory/theories/migration/subgraph_of.v#X98Legacy.polynomial_kuhn_osthus_induced_subdivision_statement`.
