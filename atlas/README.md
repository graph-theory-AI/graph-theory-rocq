# atlas — cross-package implication edges

`atlas/` is the one package that imports every area package of this monorepo
(`chromatic-theory`, `cycle-theory`, …, `topological-graph-theory`) and
`digraph-theory`. It hosts the machine-checked theorems
`<from-core>_implies_<to-core>` (or `_equiv_`) for the corpus relations whose
two endpoints live in packages that cannot import each other (for instance
`extremal-graph-theory` ↔ `minor-theory`, which have relations in both
directions). Area packages keep the invariant "import only `GTBase` (plus the
two sanctioned topological exceptions)"; the atlas depends on all of them and
nothing depends on the atlas, so the package graph stays acyclic.

Files:
- `theories/conjectures/implications_A1.v` — the cross edges between area
  packages. Verified: e121, e025, e223, e048, e117, e208, e237, e243;
  conditional on one registered external theorem (Dujmović–Morin–Wood 2017,
  planar graphs have layered treewidth ≤ 3): e126; BLOCKED with the exact
  missing layer in the note: e003, e042 (source row `fractional_hadwiger` is
  vacuous as encoded, see `fractional.is_fractional_hadwiger_unsat`, and LP
  attainment is missing), e087 (emap faces ↔ mgraph circuits bridge); recorded
  blocked/kept candidates e015, e054, e147, e244.
- `theories/foundations/` — cross-package helper lemmas that no area package
  can host because they need two area packages (or an area package this wave
  does not own):
  - `fractional.v` — χ_f ≤ χ and n ≤ had_f for a K_n minor on the D2chr LP
    vocabulary; the vacuity lemma `is_fractional_hadwiger_unsat`;
  - `degeneracy.v` — greedy colouring along a degeneracy order; a graph with
    χ > d has a nonempty set of inner minimum degree ≥ d (chromatic material);
  - `tree_decompositions.v` — X47/X48 ↔ X212 bridge (cut-form vs deletion-form
    edge connectivity, minimum degree, list decompositions);
  - `cops_bridge.v` — the graph cops-and-robbers game is decided at a finite
    horizon (so the cop number exists constructively) and equals the
    hypergraph game on the 2-uniform hypergraph E(G);
  - `complete_minors.v` — K_{n+1,n+1} has a K_{n+2} minor (minor material);
  - `queue_layouts.v` — queue layouts: injective key order vs sorted
    enumeration order.
- `theories/conjectures/implications_A2.v` — the cross edges with a
  `digraph-theory` endpoint (e010, e170, e099). `digraph-theory`'s prelude
  imports `mathcomp-classical` (`boolp`); **never use a `boolp` /
  `classical_sets` lemma here**: every theorem must print
  `Closed under the global context`.

Build and gate:
```sh
make atlas          # after make all and make digraph-theory (foundations first)
make gate           # runs make atlas, build_edge_graph.py --check, check_edges.py --assumptions
```
The atlas is not part of `make all` (like `digraph-theory`); it owns no
corpus rows, so `check_milestone.py` does not apply to it. Its edges are
verified by `meta/build_edge_graph.py --check` (annotation/theorem
consistency, corpus cite, status tripwires) and `meta/check_edges.py
--assumptions` (exact type and `Print Assumptions` of every verified or
conditional theorem). The per-edge state and reviewers live in
`meta/edge_waves.json` (waves `A1`, `A2`).
