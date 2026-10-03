# Library Migration A13: Multigraph Incidence Regularity and Guarded Cubicity

Batch A family A13, on A12 `58f2862`. Registry `meta/library_primitives/multigraph-regularity.json`; spec, hashes and
per-row certificates: `meta/migration_reports/mregular.{spec.json,md}`; API contracts are in the Rocq doc comments.

- **Contract.** `GTBase.base.mregular G r := forall v : G, #|edges_at v| = r` counts incident edges: a loop once,
  parallel edges separately. `mcubic G := mregular G 3` has no loopless guard, while
  `loopless_cubic G := loopless G /\ mcubic G` adds it. U5's `regular_m` and `cubic` convert to `mregular` and
  `mcubic`. U6's `cubic` (`loopless G /\ forall v, mdeg v = 3`, arc-end degrees, a loop twice) equals
  `loopless_cubic` by an unconditional iff through Cycle's `mdeg_loopless`, under the guard it carries. Base imports
  no Cycle module and does not duplicate the arc-end degree.
- **API.** Vacuity without vertices; uniqueness of the degree and `mDelta` given a vertex; the guarded-to-unguarded
  projection; transport along incidence-preserving vertex/edge bijections (`mregular_bij`; upstream `mgraph.iso`
  needs an `elabelType` edge label, which `unit` lacks). The public client covers three parallel edges, three loops
  at one vertex (incidence cubic, not `loopless_cubic`), the empty multigraph and a wrong degree.
- **Rows.** Eleven whole declarations are frozen verbatim at `58f2862`, with the chains `U5.is_universal_sts` and
  `U10.cubic_bridgeless`:
  - U5: three-edge-colouring (its conclusion keeps the unguarded cubic `H`) and universal STS;
  - U6: four rows;
  - U10: three rows;
  - implications_U6: the two external reductions (non-corpus).
  All guards are unchanged. No earlier frozen copy touches these names.
- **Proof consumers.** Seven proof-only adaptations in `grounding_U6`, `grounding_U10`, `implications_U6` and
  `implications_U10` use `mdeg_loopless`/`subdeg_loopless`. Every theorem type is unchanged.
- **Reproduction.** Build the packages. Run `python3 meta/migration_report.py mregular --check --kernel` and the
  milestones Chromatic U5 and Cycle U6/U10. Kernel probes are in `coordination/evidence/A13-mregular/`.
