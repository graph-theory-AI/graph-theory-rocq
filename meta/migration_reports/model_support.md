# Migration report: model-support

Inputs: `meta/migration_reports/model_support.spec.json` and `meta/library_primitives/model-support.json`.
Regenerate: `python3 meta/migration_report.py model_support --write`.
Full evidence: `python3 meta/migration_report.py model_support --details /tmp/migration-details`.

- Canonical: `GTBase.model_support.model_support`.
- Baseline: `bb0bf3cd7c1d14e014704ebd5e24b03e4c475cb8`.
- Scope: 3 helpers, 4 statements, 24 frozen objects, 136 recorded references.
- Source checks: 194/194 pass; consistent.

| Statement / corpus row | Compatibility theorem |
|---|---|
| `Extremal.conjectures.X98.polynomial_kuhn_osthus_induced_subdivision_statement` / studies:std_bonamy_et_al_polynomial_k_hn_osthus_conjecture | `Extremal.migration.model_support.polynomial_kuhn_osthus_induced_subdivision_statement_compat` |
| `GTMisc.conjectures.X114.subcubic_induced_subdivision_np_complete_statement` / studies:std_chudnovsky_seymour_trotignon_question_on_subcubi | `GTMisc.migration.model_support.subcubic_induced_subdivision_np_complete_statement_compat` |
| `Minor.conjectures.X220.four_family_free_logarithmic_treewidth_statement` / arxiv:2109.01310#00 | `Minor.migration.model_support.four_family_free_logarithmic_treewidth_statement_compat` |
| `Minor.conjectures.X220.theta_prism_even_wheel_free_bounded_treewidth_statement` / arxiv:2203.06775#00 | `Minor.migration.model_support.theta_prism_even_wheel_free_bounded_treewidth_statement_compat` |

Source checks compare frozen text, registry and statement coverage, bridge endpoints, and unchanged statement metadata. They do not prove theorem types.
`python3 meta/migration_report.py model_support --check --kernel` checks exact closed statement equivalences and all named theorem assumptions in already-built modules.
Helper types, Section context, notation/constructor resolution and compiled dependency closure still require independent review and family-specific Section and kernel dependency evidence.

Prior snapshot limitations (explanations and replacement certificates in the inputs): `extremal-graph-theory/theories/migration/consecutive_in_path.v#X98Legacy.induced_subdivision_model`, `graph-theory-misc/theories/migration/consecutive_in_path.v#X114Legacy.induced_subdivision_model`, `extremal-graph-theory/theories/migration/subgraph_of.v#X98Legacy.polynomial_kuhn_osthus_induced_subdivision_statement`, `graph-theory-misc/theories/migration/subcubic.v#X114Legacy.subcubic_induced_subdivision_np_complete_statement`, `minor-theory/theories/migration/consecutive_in_cycle.v#X220Legacy.theta_prism_even_wheel_free_bounded_treewidth_statement`, `extremal-graph-theory/theories/migration/induced_subdivisions.v#Legacy.x98_induced_subdivision_model`, `graph-theory-misc/theories/migration/induced_subdivisions.v#Legacy.x114_induced_subdivision_model`, `minor-theory/theories/migration/induced_cycles.v#X220Legacy.theta_prism_even_wheel_free_bounded_treewidth_statement`, `minor-theory/theories/migration/simple_line_graphs.v#X220Legacy.four_family_free_logarithmic_treewidth_statement`.
