# Migration report: subcubic

Inputs: `meta/migration_reports/subcubic.spec.json` and `meta/library_primitives/subcubic.json`.
Regenerate: `python3 meta/migration_report.py subcubic --write`.
Full evidence: `python3 meta/migration_report.py subcubic --details /tmp/migration-details`.

- Canonical: `GTBase.base.subcubic`.
- Baseline: `ba8b7be309af5926081ba760ba0d5ab8e94215f7`.
- Scope: 2 helpers, 3 statements, 24 frozen objects, 46 recorded references.
- Source checks: 164/164 pass; consistent.

| Statement / corpus row | Compatibility theorem |
|---|---|
| `GTMisc.conjectures.X14.subcubic_matching_lower_bound_statement` / studies:std_biedl_demaine_duncan_fleischer_kobourov_subcubic | `GTMisc.migration.subcubic.subcubic_matching_lower_bound_statement_compat` |
| `GTMisc.conjectures.X114.subcubic_induced_subdivision_np_complete_statement` / studies:std_chudnovsky_seymour_trotignon_question_on_subcubi | `GTMisc.migration.subcubic.subcubic_induced_subdivision_np_complete_statement_compat` |
| `GTMisc.conjectures.X102.bounded_tree_independence_forbidden_family_statement` / studies:std_bounded_tree_independence_number_conjecture_dall | `GTMisc.migration.subcubic.bounded_tree_independence_forbidden_family_statement_compat` |

Source checks compare frozen text, registry and statement coverage, bridge endpoints, and unchanged statement metadata. They do not prove theorem types.
`python3 meta/migration_report.py subcubic --check --kernel` checks exact closed statement equivalences and all named theorem assumptions in already-built modules.
Helper types, Section context, notation/constructor resolution and compiled dependency closure still require independent review and family-specific Section and kernel dependency evidence.

Excluded distinct variants: `GTBase.base.mcubic`, `GTBase.base.loopless_cubic`, `GTBase.base.regular`.

Prior snapshot limitations (explanations and replacement certificates in the inputs): `graph-theory-misc/theories/migration/matching.v#X14Legacy.subcubic_matching_lower_bound_statement`, `graph-theory-misc/theories/migration/consecutive_in_path.v#X114Legacy.statement`, `graph-theory-misc/theories/migration/simple_edges.v#X102Legacy.line_graph_of_subdivided_multiclaw`, `graph-theory-misc/theories/migration/simple_edges.v#X102Legacy.statement`, `graph-theory-misc/theories/migration/induced_free.v#X102Legacy.statement`, `graph-theory-misc/theories/migration/induced_free.v#X102Original.statement`, `graph-theory-misc/theories/migration/bag_decompositions.v#Legacy.bounded_tree_independence_forbidden_family_statement`, `graph-theory-misc/theories/migration/bag_decompositions.v#X102Original.bounded_tree_independence_forbidden_family_statement`, `graph-theory-misc/theories/migration/model_support.v#X114Legacy.subcubic_induced_subdivision_np_complete_statement`, `graph-theory-misc/theories/migration/induced_subdivisions.v#X114Legacy.subcubic_induced_subdivision_np_complete_statement`, `graph-theory-misc/theories/migration/induced_paths.v#X114Legacy.subcubic_induced_subdivision_np_complete_statement`.
