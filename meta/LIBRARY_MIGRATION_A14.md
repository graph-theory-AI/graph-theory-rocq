# Library Migration A14: Simple-Graph Subcubic Bound

Batch A family A14, on the private union `ba8b7be` (A13 `004cf63` plus reviewed C13 `cdb9e10`, with C11; not for
integration). Registry `meta/library_primitives/subcubic.json`; spec, hashes and per-row certificates:
`meta/migration_reports/subcubic.{spec.json,md}`; API contracts are in the Rocq doc comments.

- **Contract.** `GTBase.base.subcubic G := forall v : G, #|N(v)| <= 3` is the pointwise upper bound on simple-graph
  degrees. `subcubicP` proves it equal to `Delta G <= 3` for every graph, the empty graph included (subcubic
  vacuously, with `Delta` 0). X14's `x14_subcubic` converts to it. X114's `x114_subcubic` (`Delta H <= 3`) equals
  it by `subcubicP`, an unconditional iff rather than a conversion. A13's multigraph incidence contracts
  `mcubic`/`loopless_cubic` (exactly three incident edges) and exact regularity stay distinct.
- **API.** The finite-maximum bridge `subcubicP`, `subcubic_K0`, `regular_subcubic` (`regular G d` with `d <= 3`),
  `subcubic_Kn` (`K_{n+1}` for `n <= 3`), `not_subcubic_K5` and `subcubic_diso`. The public client covers the
  bridge, `K_0`, `K_4`, `K_5`, `K_2` (subcubic, not 3-regular), cubic graphs and isomorphisms.
- **Rows.** Frozen verbatim at `ba8b7be`:
  - the two sources;
  - X102's chains `x102_subdivided_multiclaw` and `x102_line_graph_of_subdivided_multiclaw`;
  - the whole rows X14 `subcubic_matching_lower_bound_statement`, X114
    `subcubic_induced_subdivision_np_complete_statement` and X102
    `bounded_tree_independence_forbidden_family_statement`.

  X102's biconditional, its forest/connected-set/branch-vertex multiclaw, and its complete-bipartite and line-graph
  members are unchanged. The complete rows (texts at `9e03072`, identical to the baseline) compose:
  - X14: C1's frozen pre-M1 matching;
  - X114: B3's frozen induced-subdivision problem;
  - X102: C13's complete tree-alpha class, with M1's frozen raw line graph.

  Each complete bridge reuses the earlier certificate.
- **History.** Eight earlier frozen copies still name the live helpers and stay byte-for-byte; each is documented
  in the spec with its replacement certificate:
  - C1's X14 row and B3's X114 row;
  - M1's X102 line-graph chain and row;
  - A1's and C13's per-row and complete X102 rows.

  A14's own per-row copies are documented reciprocally in C1's, B3's, A1's and C13's specs. A11, A12 and A13 drop
  the two migrated names from their unchanged distinct variants. Statement doc blocks are unchanged.
- **Proof consumers.** None to adapt: no grounding, implication or proof file names these helpers. The reverse
  dependency closure of X14/X114/X102 at the baseline, computed from the generated build dependencies, is X14,
  X114, X102, X62, `vocabulary_misc` and nine earlier GTMisc certificates (183 declarations). Every one of those
  declarations keeps its kernel type.
- **Inline bounds.** Hamilton X5, Extremal D2chr and Chromatic U5 state `Delta G <= 3` inline in statement text, so
  they have no helper to migrate and stay unchanged.
- **Reproduction.** Build the packages. Run `python3 meta/migration_report.py subcubic --check --kernel` and the
  milestones GTMisc X14, X114 and X102. Kernel probes and closures are in `coordination/evidence/A14-subcubic/`.
