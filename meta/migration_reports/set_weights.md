# Migration report: set-weight

Inputs: `meta/migration_reports/set_weights.spec.json` and `meta/library_primitives/set-weight.json`.
Regenerate: `python3 meta/migration_report.py set_weights --write`.
Full evidence: `python3 meta/migration_report.py set_weights --details /tmp/migration-details`.

- Canonical: `GraphTheory.core.dom.weight_set`.
- Baseline: `3bdfdae32824d4762ba8105367f7858a706a02e2`.
- Scope: 4 helpers, 4 statements, 14 frozen objects, 37 recorded references.
- Source checks: 130/130 pass; consistent.

| Statement / corpus row | Compatibility theorem |
|---|---|
| `GTMisc.conjectures.X128.dvorak_cheap_balanced_separator_bounded_expansion_statement` / studies:std_dvo_k_conjecture_cheap_balanced_separators_with | `GTMisc.migration.set_weights.dvorak_cheap_balanced_separator_bounded_expansion_statement_compat` |
| `GTMisc.conjectures.U13.a_gold_grabbing_game_statement` / opg:a_gold_grabbing_game | `GTMisc.migration.set_weights.a_gold_grabbing_game_statement_compat` |
| `Minor.conjectures.X190.thin_overlay_without_bounded_degree_statement` / arxiv:1704.00125#00 | `Minor.migration.set_weights.thin_overlay_without_bounded_degree_statement_compat` |
| `Minor.conjectures.X199.strongly_sublinear_separator_constant_M_statement` / arxiv:1710.03117#00 | `Minor.migration.set_weights.strongly_sublinear_separator_constant_M_statement_compat` |

Source checks compare frozen text, registry and statement coverage, bridge endpoints, and unchanged statement metadata. They do not prove theorem types.
`python3 meta/migration_report.py set_weights --check --kernel` checks exact closed statement equivalences and all named theorem assumptions in already-built modules.
Helper types, Section context, notation/constructor resolution and compiled dependency closure still require independent review and family-specific Section and kernel dependency evidence.

Excluded distinct variants: `Chromatic.conjectures.X187.x187_total_request_weight`, `Chromatic.conjectures.X187.x187_satisfied_request_weight`, `Extremal.conjectures.D2tur.tree_weight`, `Digraph.conjectures.X216.x216_cycle_weight`, `Extremal.conjectures.D2chr.match_weight`, `Extremal.conjectures.D2chr.coloring_weight`.

Prior snapshot limitations (explanations and replacement certificates in the inputs): `graph-theory-misc/theories/migration/edge_count.v#X128Legacy.dvorak_cheap_balanced_separator_bounded_expansion_statement`, `graph-theory-misc/theories/migration/ambient_shallow_minors.v#X128Legacy.dvorak_cheap_balanced_separator_bounded_expansion_statement`, `graph-theory-misc/theories/migration/ambient_shallow_minors.v#X128Original.dvorak_cheap_balanced_separator_bounded_expansion_statement`, `graph-theory-misc/theories/migration/ambient_grad.v#X128Legacy.dvorak_cheap_balanced_separator_bounded_expansion_statement`, `graph-theory-misc/theories/migration/poly_eval.v#X128Legacy.dvorak_cheap_balanced_separator_bounded_expansion_statement`.
