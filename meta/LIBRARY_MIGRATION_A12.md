# Library Migration A12: Exact Minimum Degree

Batch A family A12, on the A11 follow-up `623a89e` (A11 `465e9b4` with its tooling precursor and the private
B10/A7-history union). Registry `meta/library_primitives/minimum-degree.json`; spec, hashes and per-row
certificates: `meta/migration_reports/min_degree.{spec.json,md}`; API contracts are in the Rocq doc comments.

- **Contract.** `GTBase.base.min_degree G d := min_degree_at_least G d /\ exists v : G, #|N(v)| = d`, next to
  A11's lower bound, is a relation, not a numeric minimum. The attaining vertex excludes `K_0` at every `d`.
  X227's copy (bound first) converts to it. Extremal XE2's copy (attaining vertex first) equals it by the
  unconditional conjunct exchange `min_degree_attained_firstE`.
- **API.** Projections, uniqueness, existence given a vertex (MathComp `arg_minnP`) or `0 < #|G|`, `K_0`
  rejection, regularity with a vertex, the greatest-lower-bound equivalence, `Delta` and order bounds, `K_{n+1}`
  at `n`, and degree and minimum transport by isomorphisms. The public client covers `K_1`/`K_2`/`K_3` and wrong
  degrees.
- **Rows.** Extremal XE2 `erdos_803_statement` and GTMisc X227 `hat_guessing_degree_degeneracy_bounds_statement`
  are frozen verbatim at `623a89e` with all quantifiers, guards, the eventual-growth clause and the arithmetic
  untouched. The complete #803 row composes A12's frozen raw minimum with A5's frozen embedding and A7's frozen
  raw rank count; its bridge rewrites the minimum and reuses A7's complete certificate. A5's and A7's three #803
  snapshots stay immutable and are documented reciprocally.
- **Distinct.** Cubic, subcubic, multigraph and directed degree contracts stay separate.
- **Reproduction.** Build the packages. Run `python3 meta/migration_report.py min_degree --check --kernel` and
  the milestones Extremal XE2 and GTMisc X227. Kernel probes and closures are in
  `coordination/evidence/A12-min_degree/`.
