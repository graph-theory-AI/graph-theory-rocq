# Library Migration A21: Complete and Anticomplete Vertex-Set Pairs

Batch A family A21, on the fixed A20 pin `229f295` (no private union). Registry `meta/library_primitives/set-pair.json`;
spec, hashes and per-row certificates: `meta/migration_reports/set_pairs.{spec.json,md}`; fidelity
`meta/foundation_fidelity/set-pair.json`; API contracts are in the Rocq doc comments.

- **Contract.** Three contracts on two supplied vertex sets of one simple graph stay apart:
  - raw anticompleteness: upstream `~~ neighbor A B`, with the bounded view `neighborNP` (X41/X144
    `*_anticomplete_between`, no disjointness);
  - `GTBase.set_pairs.anticomplete A B := [disjoint A & B] && ~~ neighbor A B`, with the `-> False` view `anticompleteP`
    (X3, X57, X58, X223) and the `~~` view `anticomplete_nonadjP` (X11);
  - `GTBase.set_pairs.complete_between A B` (every cross pair adjacent), with `complete_betweenP` (X41/X144
    `*_complete_between`). On an sgraph cross completeness forces disjointness (`complete_between_disjoint`), so D2ram's
    explicit `[disjoint A & B] /\ ...` is the same contract (`disjoint_complete_betweenP`).

  No nonempty, order or unequal-vertex guard is involved. Swaps, restrictions and the complement duality for disjoint
  parts (`complete_between_compl`) complete the API. One-set stability and the whole-graph `complete_bipartite` are
  separate contracts.
- **Client.** The public client shows:
  - empty parts and `K_0`;
  - the shared `K_1` singleton: raw anticomplete with itself, neither disjoint-anticomplete nor complete;
  - singleton parts of `K_2` (complete) and of an edgeless graph (anticomplete);
  - swaps and restrictions;
  - a complete pair with a nonclique part in `K_1,2`;
  - the complement duality and why it needs disjoint parts.
- **Rows.** Frozen verbatim at `229f295`: the ten sources, the five row-reaching chains and the nine rows.
  - Chromatic: X3 #1111 (positive t, c; d before every graph; ordered chromatic bounds); X213 El-Zahar-Erdos (one f
    before r, k, G; exactly-r clique OR both parts of chromatic number exactly k).
  - Extremal: X57's sparse strong Erdos-Hajnal property and iff with forests; X58 (Delta bound, asymmetric bounds, its
    partial defect); X223 (triangle-free, closed-neighbourhood bound); D2ram (complete in G OR in `compl G` on the same
    parts, no nonempty condition).
  - GTMisc: X41 and X144 pure pairs (own disjointness, both nonempty, complete OR anticomplete) and rows, with X41's
    documented sublinear side.
  - Minor: X11's pairwise and k-path chains and the induced Menger row (k = 0, truncated predecessor, X/Y overlap,
    singleton paths, the complete right disjunct).

  Every quantifier order, guard, bound, status and leg state is unchanged.
- **Complete rows.** 13 whole-row iffs in all: the nine current rows, and four complete rows at the pre-migration
  `9e03072`:
  - X57 (with its property chain), X58 and X41, over A1's frozen induced-freeness;
  - X11 (B1+B5+A21): the pairwise chain over B1's frozen path support, the k-path chain over B5's frozen X-Y path, and
    B5's complete frozen right alternative.

  The bridges reuse A1's, B1's and B5's certificates. B5's older `X11Original` reaches the live pair only through B1's
  frozen pairwise chain; it is kept unchanged beside the new one.
- **History.** A1's X57/X58/X41 snapshots and B1's/B5's X11 chains keep live set-pair names byte for byte; the spec
  documents them. A21's per-row copies keep A1's, B1's and B5's live names, with reciprocal notes in their specs. The two
  obsolete A8 `x223_anticomplete` exclusions are removed; X76/X78 stay.
- **Proof consumers.** These route through the views, with types unchanged: `grounding_X213.x213_anticomplete_set0`,
  `grounding_D2ram.complete_bipartite_sub0` and `complete_bipartite_sub_sym`, and `grounding_X223.anticomplete_set0`. The
  verified gc:e076 implication X58 to X223 is unchanged (gc:e077 stays a candidate), as are the A1/B1/B5 certificate
  modules. The 62-file reverse closure (637 old headers) is type-identical to the baseline.
- **Distinct.** These stay separate:
  - X94's two-carrier `x94_complete_pair` and `x94_anticomplete_pair`;
  - X67's sequence-interior `x67_no_cross_edges`;
  - the whole-graph `GTBase.common.complete_bipartite`.
- **Before merge.** C12 is outside A20 ancestry. Its D2ram and X144 complete rows (C12's raw perfection plus the frozen
  pair chains) are a mandatory, separately reviewed follow-up on the combined parent; this pin's acceptance is not
  combined-parent acceptance.
- **Reproduction.** Build the packages. Run `python3 meta/migration_report.py set_pairs --check --kernel` and the
  milestones Chromatic X3/X213, Extremal D2ram/X57/X58/X223, GTMisc X41/X144 and Minor X11. Kernel probes are in
  `coordination/evidence/A21-set-pairs/`.
