# graph-theory-base (`rocq-graph-theory-base`, compatibility name `coq-graph-theory-base`, namespace `GTBase`)

The single owner of **cross-area primitives** for the graph-theory-rocq federation (plan §A
ownership table). Every area package depends ONLY on this (never on a sibling).

**Status: G3-core LANDED (2026-06-26).** `theories/base.v`:
- **re-exports** the core coq-graph-theory undirected vocabulary in one place — `sgraph`, `--`,
  `N(x)`, `χ`/`chi_mem`, `ω`/`omega_mem`, `α`, `clique`/`cliques`, `connected`, `'K_n`/`complete`,
  `≃`/`diso`, `ucycle`/`ucycleb` (plus mathcomp `all_boot`);
- **owns** the cross-area primitives:
  - from U1: `Delta` (Δ), `common_nbr`, `regular`, `girth_geq`, `ceil_div`;
  - U3 surface (+ `cartesian_product` promoted from U2): graph homomorphism `is_hom` /
    `homs_to`, graph `is_core`, `cartesian_product` (□), `tensor_product` (×, the Hedetniemi product);
  - power family (promoted from U1 ∩ U3): `graph_power` (Gᵐ), `subdivision` (G^{1/n}), `frac_power` (G^{m/n});
  - list-colouring (promoted from U4): `list_colourable` / `list_colourable_on` (over an arbitrary
    `finType` palette), `choosable` (k-choosability), `is_choice_number` (relational choice number);
  - edge/total colouring (promoted from U4, the `mgraph` layer): the `mgraph` notation (`graph unit unit`),
    `line_graph` / `total_graph` (undirected sgraphs), `chromatic_index` (χ'), `total_chromatic_number`
    (χ''), `edge_colourable` / `total_colourable`. **`mgraph` is `Import`ed, not `Export`ed** — a
    pure-sgraph milestone stays clean; an mgraph-aware milestone does `From GraphTheory Require Import
    mgraph.` **before** the base import (coq-graph-theory's `mgraph` has a clashing *directed* `line_graph`).
    `mDelta` (multigraph max degree, parallel edges counted) is here too (promoted from U4 ∩ U5).
  - connectivity & structure (promoted across U2/U3/U6/U9): `k_connected` (Whitney form),
    `triangle_free` (vertex-triple form), `uwalk` (undirected multigraph walk — fixes the
    source→target bias of coq-graph-theory's `walk`; cycle-theory/U6 connectivity reuses it);
  - degeneracy / sparsity (promoted U7/U13): `k_degenerate` / `k_degenerate_on`, `average_degree_geq`
    (avg degree ≥ a/b via Σdeg = 2|E|), `has_girth` (exact girth);
  - **combinatorial planarity** (G2-lite): `wagner_planar G := ~ minor G 'K_5 /\ ~ minor G (KB 3 3)`
    — Wagner's theorem characterization of planarity, axiom-free (no coq-fourcolor). For statements
    whose hypothesis is just "G is planar"; NOT a face/embedding/genus notion.

Import with `From GTBase Require Import base.` (area packages add `-Q ../base/theories GTBase`
to their `_CoqProject`). Compiles axiom-free on switch `digraph` (Rocq 9.1.1 + coq-graph-theory);
`chromatic-theory/U1` consumes it.
Installed as the opam package `rocq-graph-theory-base`, which installs the public modules only; see
"Public library packages (opam)" in the root README.

**Heavyweight planar layer (real embeddings/faces/genus) still deferred** to a future `coq-fourcolor`
spike — needed only by surface/triangulation/crossing-number rows; the combinatorial `wagner_planar`
above covers every "G is planar" hypothesis.
