# Migration report: poly-list-chi-bounded

Inputs: `meta/migration_reports/poly_list_chi_bounded.spec.json` and `meta/library_primitives/poly-list-chi-bounded.json`.
Regenerate: `python3 meta/migration_report.py poly_list_chi_bounded --write`.
Full evidence: `python3 meta/migration_report.py poly_list_chi_bounded --details /tmp/migration-details`.

- Canonical: `Chromatic.foundations.chi_bounding.poly_list_chi_bounded`.
- Baseline: `0449699300e18f2ddf0773ede1c81976e632a284`.
- Scope: 2 helpers, 4 statements, 10 frozen objects, 42 recorded references.
- Source checks: 94/94 pass; consistent.

| Statement / corpus row | Compatibility theorem |
|---|---|
| `Chromatic.conjectures.X3.hereditary_chi_bounded_not_polynomial_statement` / arxiv:1910.00697#00 | `Chromatic.migration.poly_list_chi_bounded.hereditary_chi_bounded_not_polynomial_statement_compat` |
| `Chromatic.conjectures.X65.forest_free_polynomial_chi_bound_statement` / arxiv:2202.05557#00 | `Chromatic.migration.poly_list_chi_bounded.forest_free_polynomial_chi_bound_statement_compat` |
| `Chromatic.conjectures.X66.good_trees_disjoint_union_good_statement` / arxiv:2202.09118#03 | `Chromatic.migration.poly_list_chi_bounded.good_trees_disjoint_union_good_statement_compat` |
| `Chromatic.conjectures.X124.dreier_torunczyk_merge_width_poly_chi_bounded_statement` / studies:std_dreier_toru_czyk_conjecture_merge_width_polynomi | `Chromatic.migration.poly_list_chi_bounded.dreier_torunczyk_merge_width_poly_chi_bounded_statement_compat` |

Source checks compare frozen text, registry and statement coverage, bridge endpoints, and unchanged statement metadata. They do not prove theorem types.
`python3 meta/migration_report.py poly_list_chi_bounded --check --kernel` checks exact closed statement equivalences and all named theorem assumptions in already-built modules.
Helper types, Section context, notation/constructor resolution and compiled dependency closure still require independent review and family-specific Section and kernel dependency evidence.

Excluded distinct variants: `Chromatic.foundations.chi_bounding.poly_chi_bounded`.

Prior snapshot limitations (explanations and replacement certificates in the inputs): `chromatic-theory/theories/migration/chi_bounded_classes.v#X3Legacy.hereditary_chi_bounded_not_polynomial_statement`, `chromatic-theory/theories/migration/disjoint_union.v#X66Legacy.good_trees_disjoint_union_good_statement`, `chromatic-theory/theories/migration/graph_classes.v#Legacy.hereditary_chi_bounded_not_polynomial_statement`, `chromatic-theory/theories/migration/graph_classes.v#X3Original.hereditary_chi_bounded_not_polynomial_statement`.
