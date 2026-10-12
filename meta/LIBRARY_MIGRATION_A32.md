# Library Migration A32: List-Form Polynomial Chi-Bound

Batch A family A32 (stage 2 of the polynomial scope), on the A31 CANDIDATE `0449699` (stage 1, natural Horner evaluation),
itself on the reviewed A30 candidate `db16a76`; neither parent is accepted main. Registry
`meta/library_primitives/poly-list-chi-bounded.json`; spec, hashes and per-row certificates
`meta/migration_reports/poly_list_chi_bounded.{spec.json,md}`; fidelity `meta/foundation_fidelity/poly-list-chi-bounded.json`;
full evidence `coordination/evidence/A32-poly-list-chi-bounded/` (scope: `resume-2026-10-06/A31-poly-scope-handoff-by-arthur.md`, §2).

- **Contract.** `Chromatic.foundations.chi_bounding.poly_list_chi_bounded F := exists p : seq nat, forall G, F G ->
  χ([set: G]) <= GTBase.poly_nat.horner_nat p (ω([set: G]))`: one coefficient list, chosen before the graphs, no guard
  (the empty list bounds only χ = 0). It sits beside the normal form `poly_chi_bounded`, which the same module already owns,
  and has a sanity API (non-vacuity, heredity, a list bound is a bound, teeth) and a public client.
- **Sources.** X3's `x3_polynomially_chi_bounded` and X124's `x124_poly_chi_bounded` become transparent aliases. Each is
  related to its freeze at `0449699` by a CONVERSION: A31's evaluator aliases unfold, and `x124_omega G := ω([set: G])`.
- **Rows.** Frozen verbatim:
  - the two classes;
  - `x66_good`;
  - the X3 (negated class), X65, X66 and X124 rows.

  Guards and quantifier order are unchanged.
- **History.** Only 3 earlier frozen objects reach a live list-form class. The scan resolved actual qualified closures for
  161 probed objects. The 3 are C9's X3 row and C10's Legacy and Original X3 rows. They stay byte-exact as stale snapshots.
  The deepest Originals are A31's X3/X124 Originals. Their whole-row iffs compose:
  - C10's Original certificate or A16's clique-number equality;
  - A31's evaluator equality;
  - the conversion.

  C9's spec moves the two migrated distinct variants into a qualified note.
- **`poly_forms`.** The X3 import is dropped. The seven qualified names are kept, stated over the owners' constants, and
  each complete type is convertible to its former X3-stated type (kernel ascriptions). The ω = 0 corner (`chi_eq0_omega0`)
  is kept. X218's and X66's `apply:` lines and `implications_U8` compile unchanged.
- **Proof-only.** In A31's `poly_eval.v`, the two class certificates now pass through the alias by conversion. Their types
  are unchanged.
- **Kept distinct.** The P-normal `poly_chi_bounded`, which `poly_forms` proves equivalent, and the arbitrary-function
  chi-bounded family.
- **Pending (not claimed).** A28/X66: at an actual parent containing A28, its X66 row reaches this family's alias through
  `x66_good`. Its deepest Original composes A28's disjoint union with A31's and this family's frozen class.
- **Reproduction.**
  1. Build the packages.
  2. Run `python3 meta/migration_report.py poly_list_chi_bounded --check --kernel`.
  3. Run the `--kernel` reports of poly_eval, chi_bounded, hereditary_class and clique_number.
  4. Run both `test_migration_report.py` runs.
  5. Run the milestones X3, X65, X66, X124, X218 and U8 (chromatic).
