# Library Migration A31: Natural Horner Evaluation

Batch A family A31 (stage 1 of the polynomial scope; the list-form class owner is stage A32), on the reviewed CANDIDATE
parent A30 `db16a76` (not accepted main). Registry `meta/library_primitives/poly-eval.json`; spec, hashes and per-row
certificates `meta/migration_reports/poly_eval.{spec.json,md}`; fidelity `meta/foundation_fidelity/poly-eval.json`; full
evidence `coordination/evidence/A31-poly-eval/` (scope: `resume-2026-10-06/A31-poly-scope-handoff-by-arthur.md`; discovery:
`resume-2026-10-06/poly-utility-discovery-by-arthur/`).

- **Contract.** `GTBase.poly_nat.horner_nat p x := poly.horner_rec p x`, upstream MathComp at the natural semiring:
  coefficients lowest degree first, the empty list is 0 at every point, no guard. A thin adapter in a narrow-import
  module (ssralg/poly Required, only ssralg canonicals imported), not re-exported by `GTBase.base`, with the nil/cons-complete
  API: nil, cons, foldr shape, `x = 0`, monomial, trailing zero, monotonicity, domination for `1 <= t` (necessary guard).
- **Sources.** The six Fixpoints `x3`/`x124`/`x59`/`x60`/`x128`/`x139_poly_eval`, X220's foldr `x220_poly_eval` and the
  public foldr `Chromatic.foundations.chi_bounding.horner_nat` (repository source) become transparent aliases; each is
  related to its raw freeze by an UNCONDITIONAL pointwise equality (not a conversion).
- **Rows.** Frozen verbatim: the eight evaluators, six chains (X3/X124 list-form classes, `x66_good`, X128/X139/X220
  expansion) and twelve whole rows (X3 negated class, X65, X66, X124, X59, X98, X60, X128, X139, X220 ×3). Guards and
  quantifier order are unchanged; X139's documented defect stays blocked.
- **History.** 37 earlier frozen objects reach a live evaluator by actual qualified closure resolution (706 probed). The
  eight rows with history get deepest Originals: the deepest existing Original (no live migrated-family helper, kernel
  audit) with the raw evaluator substituted; each whole-row iff composes the evaluator equality with the earlier Original's
  certificate. Earlier objects stay byte-exact as documented stale snapshots, with reciprocal notes.
- **Consumers.** Proof-only restatements with unchanged types: `chi_bounding.horner_nat_dom`, `poly_forms.x3_poly_eval_monomial`,
  `implications_X220`'s `x220_poly_eval_mono`, `poly_addE`, `poly_shiftE`. `poly_forms` keeps its X3 import until A32.
- **Kept distinct.** The P-normal `poly_chi_bounded` (A32 relates it), grad and shallow-minor encodings, separator contracts.
- **Pending (not claimed).** A28/X66's deeper Original composes A28's disjoint union with this family's frozen class at an
  actual parent containing both.
- **Reproduction.** Build the packages, then `python3 meta/migration_report.py poly_eval --check --kernel`, the historical
  reports with `--kernel`, both `test_migration_report.py` runs and the milestones X3, X65, X66, X124 (chromatic), X59, X60,
  X98 (extremal), X128, X139 (graph-theory-misc) and X220 (minor).
