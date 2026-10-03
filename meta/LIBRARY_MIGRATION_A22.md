# Library Migration A22: Closed Vertex Balls and Seed-Set Balls

Batch A family A22, on the fixed A21 pin `1b8126b` (no private union). Registry `meta/library_primitives/ball.json`;
spec, hashes and per-row certificates: `meta/migration_reports/balls.{spec.json,md}`; fidelity
`meta/foundation_fidelity/ball.json`; API contracts are in the Rocq doc comments.

- **Contract.** The vertex canonical is the existing `GTBase.base.ball r x`, byte-exact: radius 0 is `[set x]` and each
  step adds the neighbours of the previous ball. Its Section discharge (over `G` only) and `graph_power` are unchanged;
  `GTBase.base` gains only the evidence lemmas `ball0`, `ballS` and `ball_center`. The new `GTBase.balls` names the
  seed-set ball `set_ball r S := \bigcup_(x in S) ball r x` and proves:
  - radius monotonicity (`ball_succ_sub`, `ball_mono`) and the exact specialization
    `ball_rel_ballE : ball r x = rel_ball (--) r x` of `GTBase.graph_metric.rel_ball`;
  - the seed-set views `in_set_ball`, `set_ball_set0` (no seeds), `set_ball0` (radius 0), `set_ball1` (one seed),
    `set_ballU` (unions), `set_ball_sub` (the seeds belong) and monotonicity in the seeds and in the radius
    (`set_ball_subset`, `set_ball_mono`).

  No connectedness, nonempty-host, positive-radius or small-radius guard is involved. A ball never leaves the centre's
  component, while `graph_dist` is truncated at `#|G|` for unreachable pairs, so no unconditional distance bridge is
  stated.
- **Sources.** The seven local Fixpoints (GTMisc X20, X39, X113, X116, X146; Packing X26, X111) now unfold to
  `ball r x`, and the five seed-set balls (X39, X113, X116, X146, X26) to `set_ball r S`. The certificates are set
  equalities: by induction on the radius for the Fixpoints (distinct fixpoints, not conversions), ball by ball for the
  seed sets.
- **Client.** The public client shows:
  - the zero radius, centre membership, monotonicity and the `rel_ball` specialization;
  - the empty, zero, singleton and union seed-set views;
  - `K_0`, where every seed-set ball is empty at every radius;
  - an edgeless host, where every ball is its centre at every radius;
  - `edgeless 2`, where the truncated `graph_dist` between the two vertices is 2, yet no ball around one ever reaches
    the other.
- **Rows.** Frozen verbatim at `1b8126b`: the twelve sources, the sixteen reaching chains and the eight rows.
  - GTMisc:
    - X20 burning number: positive order, connected carrier, least-square `t`, the same `'I_t` centres and truncated
      `t.-1 - i` radii.
    - X39: `k` before `c` before `d`, `G`, `X`, `Y`; radius `c * d`; separator below `k`.
    - X40: `k >= 1`, `ell > 0`, fixed distance 2, separator at most `k - 1`, over X39's chains.
    - X113: uniform `f`, `g` before `k`, `d`, `G`, with `k, d >= 1`; `k` distant cycles, or at most `f k` vertices
      whose `g d`-ball leaves a forest.
    - X116: `l` depending on both `k` and `d`.
    - X146: uniform `f`, `g`; distinct A-path endpoints and the same hitting bound.
  - Packing:
    - X26: `d` and `Dmax`, then `C > 0`, before `k`, `G`, `X`, `Y`; the degree bound; separator below `C * k`; the
      stronger `d = 0` reading.
    - X111: one `c` before `r`, `G`, `U`; `wagner_planar`; tau's arg-min with default `[set: G]` and nu's maximum, as
      natural-number equalities (an empty `U` still gives 0 and 0).

  Every quantifier order, guard, natural subtraction, status and leg state is unchanged.
- **Complete rows.** 14 whole-row iffs: the eight current rows, and six complete rows at the pre-migration `9e03072`:
  - X39 and X40 (B1+B5+A22): the pairwise chain over B1's frozen path support, the k-path chain over B5's frozen X-Y
    path, and B5's complete frozen separator;
  - X116 (B1+B5+A22), with B5's frozen S-T path;
  - X113 (B1+B10+A22): distant cycles over B10's frozen cycle, and B10's complete forest-after chain;
  - X146 (B1+A22): the pairwise, k-path and hitting chains;
  - Packing X26 (B1+B5+A22), with B5's complete frozen separator.

  B1's, B5's and B10's modules are aliased without Import and their certificates are reused. The older B5 and B10
  `X*Original` rows still reach the live balls, directly or through B1's frozen pairwise chains; they are kept
  unchanged beside the new ones.
- **History.** B1's, B5's and B10's GTMisc and Packing snapshots keep live ball names byte for byte. The spec documents
  them, and also the lexical self-reference of each frozen Fixpoint's recursive call. A22's per-row copies keep B1's,
  B5's and B10's live names, with reciprocal notes in their specs (compact reports regenerated).
- **Proof consumers.**
  - `vocabulary_packing.x26_ballE` keeps its type and its radius-induction proof; both sides now unfold to `ball r x`,
    and only its section comment changes.
  - The import-only `vocabulary_misc` and `GTMisc.migration.simple_edges`, and the five earlier certificate modules,
    compile unchanged.
  - `base.v` and the 21 baseline files of the reverse closure of the seven source files (431 declarations) are
    type-identical to the baseline, and `ball` and `graph_power` print identically.
- **Distinct.** These stay separate:
  - `GTBase.graph_metric.rel_ball`, for an arbitrary relation (`ball_rel_ballE` is its specialization);
  - the ambient `x128_radius_at_most` and `x139_radius_at_most` over the truncated `graph_dist` (C16/C23; X139's
    blocked defect is unchanged);
  - X220's internal `x220_ball_in` (C18);
  - X161's scalar `x161_local_chromatic_radius_two`.
- **Reproduction.** Build the packages. Run `python3 meta/migration_report.py balls --check --kernel` and the
  milestones GTMisc X20/X39/X40/X113/X116/X146 and Packing X26/X111. Kernel probes are in
  `coordination/evidence/A22-balls/`.
