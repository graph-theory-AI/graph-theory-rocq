# Library Migration A30: Finite-Set Weights

Batch A family A30, on the accepted parent P' `3bdfdae`. Registry `meta/library_primitives/set-weight.json`; spec,
hashes and per-row certificates `meta/migration_reports/set_weights.{spec.json,md}`; full evidence
`coordination/evidence/A30-set-weights/` (family summary: `coordination/evidence/resume-2026-10-06/A30-set-weights-family-summary-by-arthur.md`).

- **Contract.** Upstream `GraphTheory.core.dom.weight_set w S := \sum_(v in S) w v` (re-exported by `GTBase.base`) is
  canonical: any finite carrier, any natural weights (zero weights included), any set (the empty set weighs 0), no
  positivity premise. No summation primitive is added. `GTBase.set_weights` gives the views: empty set, singleton,
  whole carrier `= fg_total_weight`, constant weights `c * #|S|`, disjoint additivity, complement split,
  monotonicity, zero test, extensionality, and the finite-set coercion bridge `weight_set w S = fg_event_weight w [in S]`.
  `finite_graph.v` and its positive-total-weight ratio guards are unchanged.
- **Sources.** X128's `x128_weight`, X190's `x190_weight`, X199's `x199_weight` and U13's `gold_total` (found by the
  body scan: the same body up to the binder name) are the upstream body at `T := G`; they become transparent aliases.
- **Rows.** Frozen verbatim at P': the four sources; the chains `x128_cheap_bal_sep`,
  `x190_strongly_sublinear_separator_class`, `x199_weighted_balanced_separator` (and `_with_constant_M`) and
  `leaf_game_solution`; four complete rows (X128, X190, X199, U13 gold-grabbing game). The rows keep their guards,
  their quantifier order and their notes; X190 and X199 stay blocked and unrepaired. Fourteen certificates by conversion.
- **History.** The X128 rows of A7 `edge_count`, C16 `ambient_shallow_minors` (Legacy and Original) and C23
  `ambient_grad` stay byte-exact and are documented stale snapshots. The new deepest `X128Original` puts C16's
  complete A7+C16 Original expansion chain under the A30 frozen separator and weight, with its whole-row iff. The
  reciprocal notes for the new X128 copy are in the A7, C16 and C23 specs.
- **Consumers.** grounding_U13's `gold_total_set0` and `leaf_game_E1` add one unfold of the public weight; headers
  unchanged. The rest of the reverse closure recompiles unchanged.
- **Kept distinct.** Separator contracts, polynomial evaluation, X187's request weights, D2tur's edge-pair
  `tree_weight`, X216's rational cycle weight and D2chr's integer matching weights.
- **Reproduction.** Build the packages, then run `python3 meta/migration_report.py set_weights --check --kernel`, the
  historical reports `edge_count`, `ambient_shallow_minors` and `ambient_grad` with `--kernel`, and the milestones
  X128, U13 (graph-theory-misc), X190 and X199 (minor-theory).
