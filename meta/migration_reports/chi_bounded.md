# Migration report: chi-bounded

Inputs: `meta/migration_reports/chi_bounded.spec.json` and `meta/library_primitives/chi-bounded.json`.
Regenerate: `python3 meta/migration_report.py chi_bounded --write`.
Full evidence: `python3 meta/migration_report.py chi_bounded --details /tmp/migration-details`.

- Canonical: `GTBase.chi_bounding.chi_bounded_via`.
- Baseline: `0659592d2a379b1f2564601e8b61689e05eac416`.
- Scope: 5 helpers, 10 statements, 16 frozen objects, 118 recorded references.
- Source checks: 250/250 pass; consistent.

| Statement / corpus row | Compatibility theorem |
|---|---|
| `Chromatic.conjectures.U8.graphs_with_a_forbidden_induced_tree_are_chi_bounded_statement` / opg:graphs_with_a_forbidden_induced_tree_are_chi_bounded | `Chromatic.migration.chi_bounded_classes.graphs_with_a_forbidden_induced_tree_are_chi_bounded_statement_compat` |
| `Chromatic.conjectures.U8.vertex_minor_closed_classes_are_chi_bounded_statement` / opg:vertex_minor_closed_classes_are_chi_bounded | `Chromatic.migration.chi_bounded_classes.vertex_minor_closed_classes_are_chi_bounded_statement_compat` |
| `Chromatic.conjectures.X3.hereditary_chi_bounded_not_polynomial_statement` / arxiv:1910.00697#00 | `Chromatic.migration.chi_bounded_classes.hereditary_chi_bounded_not_polynomial_statement_compat` |
| `Chromatic.conjectures.X3.gyarfas_complementation_chi_bounded_statement` / studies:std_gy_rf_s_complementation_conjecture | `Chromatic.migration.chi_bounded_classes.gyarfas_complementation_chi_bounded_statement_compat` |
| `Chromatic.conjectures.X3.gyarfas_alpha_omega_chi_bounded_statement` / studies:std_gy_rf_s_conjecture_6_8_h_h_h_1_classes_are_bound | `Chromatic.migration.chi_bounded_classes.gyarfas_alpha_omega_chi_bounded_statement_compat` |
| `Chromatic.conjectures.X112.chi_bounded_closure_substitution_gluing_statement` / studies:std_chudnovsky_penev_scott_trotignon_conjecture_boun | `Chromatic.migration.chi_bounded_classes.chi_bounded_closure_substitution_gluing_statement_compat` |
| `Chromatic.conjectures.X170.oriented_P4_forb_chi_bounded_statement` / arxiv:1605.07411#02 | `Chromatic.migration.chi_bounded_classes.oriented_P4_forb_chi_bounded_statement_compat` |
| `Digraph.conjectures.chi_bounded.conj2_1605_statement` / arxiv:1605.07411#00 | `Digraph.migration.chi_bounded_classes.conj2_1605_statement_compat` |
| `Digraph.conjectures.chi_bounded.conj4_1605_statement` / arxiv:1605.07411#01 | `Digraph.migration.chi_bounded_classes.conj4_1605_statement_compat` |
| `Digraph.conjectures.chi_bounded.conj5_1605_statement` / no corpus row | `Digraph.migration.chi_bounded_classes.conj5_1605_statement_compat` |

Source checks compare frozen text, registry and statement coverage, bridge endpoints, and unchanged statement metadata. They do not prove theorem types.
`python3 meta/migration_report.py chi_bounded --check --kernel` checks exact closed statement equivalences and all named theorem assumptions in already-built modules.
Helper types, Section context, notation/constructor resolution and compiled dependency closure still require independent review and family-specific Section and kernel dependency evidence.

Excluded distinct variants: `Chromatic.conjectures.X3.x3_polynomially_chi_bounded`, `Chromatic.conjectures.X124.x124_poly_chi_bounded`, `Chromatic.foundations.chi_bounding.poly_chi_bounded`, `Chromatic.conjectures.X3.x3_bounded_chromatic`, `Digraph.conjectures.dichromatic.dichromatic_bounded`, `Digraph.conjectures.X52.x52_mader_chi_bound`.

Prior snapshot limitations (explanations and replacement certificates in the inputs): `chromatic-theory/theories/migration/complement.v#X3Legacy.gyarfas_complementation_chi_bounded_statement`, `digraph-theory/theories/migration/path_vertices.v#X52Legacy.mader_chi_bound`, `chromatic-theory/theories/migration/graph_classes.v#Legacy.hereditary_chi_bounded_not_polynomial_statement`, `chromatic-theory/theories/migration/ordinal_path.v#X170Legacy.oriented_P4_forb_chi_bounded_statement`.
