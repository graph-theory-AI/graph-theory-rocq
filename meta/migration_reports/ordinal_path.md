# Migration report: ordinal-path

Inputs: `meta/migration_reports/ordinal_path.spec.json` and `meta/library_primitives/ordinal-path.json`.
Regenerate: `python3 meta/migration_report.py ordinal_path --write`.
Full evidence: `python3 meta/migration_report.py ordinal_path --details /tmp/migration-details`.

- Canonical: `GTBase.path_graphs.ordinal_path`.
- Baseline: `9921abbaa06205062a2b81d77d06cdd641dcdc97`.
- Scope: 7 helpers, 4 statements, 20 frozen objects, 50 recorded references.
- Source checks: 181/181 pass; consistent.

| Statement / corpus row | Compatibility theorem |
|---|---|
| `Packing.conjectures.X18.path_partition_independent_set_balance_statement` / arxiv:1611.03196#00 | `Packing.migration.ordinal_path.path_partition_independent_set_balance_statement_compat` |
| `Packing.conjectures.X226.eta_bounded_path_free_classes_statement` / arxiv:2302.04986#01 | `Packing.migration.ordinal_path.eta_bounded_path_free_classes_statement_compat` |
| `Hom.conjectures.U3.extremal_problem_on_the_number_of_tree_endomorphism_statement` / opg:extremal_problem_on_the_number_of_tree_endomorphism | `Hom.migration.ordinal_path.extremal_problem_on_the_number_of_tree_endomorphism_statement_compat` |
| `Chromatic.conjectures.X170.oriented_P4_forb_chi_bounded_statement` / arxiv:1605.07411#02 | `Chromatic.migration.ordinal_path.oriented_P4_forb_chi_bounded_statement_compat` |

Source checks compare frozen text, registry and statement coverage, bridge endpoints, and unchanged statement metadata. They do not prove theorem types.
`python3 meta/migration_report.py ordinal_path --check --kernel` checks exact closed statement equivalences and all named theorem assumptions in already-built modules.
Helper types, Section context, notation/constructor resolution and compiled dependency closure still require independent review and family-specific Section and kernel dependency evidence.

Excluded distinct variants: `GTBase.base.cyc_rel`, `Minor.conjectures.X198.x198_join_path_rel`, `Digraph.conjectures.two_extremal.symcyc_rel`, `GTMisc.conjectures.U13.induced_cycle`, `Chromatic.applications.gap_repairs.viable_boundary.boundary_rel`, `Chromatic.conjectures.X162.x162_tri_rel`, `Topological.conjectures.D6emb.anti_dir`.

Prior snapshot limitations (explanations and replacement certificates in the inputs): `chromatic-theory/theories/migration/chi_bounded_classes.v#X170StatementsLegacy.oriented_P4_forb_chi_bounded_statement`, `packing-theory/theories/migration/stable_sets.v#X18Legacy.path_partition_independent_set_balance_statement`.
