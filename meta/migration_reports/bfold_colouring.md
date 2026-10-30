# Migration report: bfold-colouring

Inputs: `meta/migration_reports/bfold_colouring.spec.json` and `meta/library_primitives/bfold-colouring.json`.
Regenerate: `python3 meta/migration_report.py bfold_colouring --write`.
Full evidence: `python3 meta/migration_report.py bfold_colouring --details /tmp/migration-details`.

- Canonical: `GTBase.bfold_colourings.bfold_colouring`.
- Baseline: `3bdfdae32824d4762ba8105367f7858a706a02e2`.
- Scope: 2 helpers, 7 statements, 12 frozen objects, 89 recorded references.
- Source checks: 165/165 pass; consistent.

| Statement / corpus row | Compatibility theorem |
|---|---|
| `Chromatic.conjectures.X130.dvorak_mnich_planar_girth5_fractional_chromatic_statement` / studies:std_dvo_k_mnich_conjecture_fractional_chromatic_numb | `Chromatic.migration.bfold_colouring.dvorak_mnich_planar_girth5_fractional_chromatic_statement_compat` |
| `Chromatic.conjectures.X131.dvorak_mnich_planar_girth5_fractional_chromatic_duplicate_statement` / studies:std_dvo_k_mnich_conjecture_fractional_chromatic_numb_186 | `Chromatic.migration.bfold_colouring.dvorak_mnich_planar_girth5_fractional_chromatic_duplicate_statement_compat` |
| `Chromatic.conjectures.X149.gimbel_kundgen_li_thomassen_four_chromatic_planar_fractional_statement` / studies:std_gimbel_k_ndgen_li_thomassen_conjecture | `Chromatic.migration.bfold_colouring.gimbel_kundgen_li_thomassen_four_chromatic_planar_fractional_statement_compat` |
| `Chromatic.conjectures.X173.planar_triangle_free_fractional_chromatic_bound_statement` / arxiv:1606.06265#00 | `Chromatic.migration.bfold_colouring.planar_triangle_free_fractional_chromatic_bound_statement_compat` |
| `Chromatic.conjectures.X204.planar_no_4_5_cycles_fractional_below_eleven_thirds_statement` / arxiv:1802.04179#01 | `Chromatic.migration.bfold_colouring.planar_no_4_5_cycles_fractional_below_eleven_thirds_statement_compat` |
| `Chromatic.conjectures.X218.kr_free_degenerate_fractional_chromatic_sublinear_statement` / arxiv:2601.15245#04 | `Chromatic.migration.bfold_colouring.kr_free_degenerate_fractional_chromatic_sublinear_statement_compat` |
| `Extremal.conjectures.D2chr.fractional_hadwiger_statement` / opg:fractional_hadwiger | `Extremal.migration.bfold_colouring.fractional_hadwiger_statement_compat` |

Source checks compare frozen text, registry and statement coverage, bridge endpoints, and unchanged statement metadata. They do not prove theorem types.
`python3 meta/migration_report.py bfold_colouring --check --kernel` checks exact closed statement equivalences and all named theorem assumptions in already-built modules.
Helper types, Section context, notation/constructor resolution and compiled dependency closure still require independent review and family-specific Section and kernel dependency evidence.

Excluded distinct variants: `GTMisc.conjectures.U13.weighted_colourable`, `Chromatic.conjectures.XE2.xe2_ab_choosable`, `Chromatic.conjectures.X130.x130_frac_chi_le`.

Prior snapshot limitations (explanations and replacement certificates in the inputs): `chromatic-theory/theories/migration/cycle_lengths.v#X204Legacy.planar_no_4_5_cycles_fractional_below_eleven_thirds_statement`, `extremal-graph-theory/theories/migration/fractional_chromatic.v#Legacy.is_fractional_chromatic`, `extremal-graph-theory/theories/migration/fractional_clique_minor.v#D2chrLegacy.fractional_hadwiger_statement`.
