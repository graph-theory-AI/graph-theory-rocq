(* Packing.conjectures.X15 -- v2 fair matching representation rows *)
From mathcomp Require Import all_boot.
From GraphTheory Require Import sgraph minor treewidth connectivity excluded.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


(*From GTBase Require Export base.*)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Coercion svertex : sgraph >-> finType.

(** ** Local X15 vocabulary ************************************************)

Definition x15_edge_set (G : sgraph) : {set {set G}} :=
  [set e : {set G} |
      [exists x : G, [exists y : G, (sedge x y) && (e == [set x; y])]]].

Definition x15_matching (G : sgraph) (M : {set {set G}}) : Prop :=
  M \subset x15_edge_set G /\
  forall v : G, #|[set e in M | v \in e]| <= 1.

Definition x15_edge_partition
    (G : sgraph) (m : nat) (E : 'I_m -> {set {set G}}) : Prop :=
  (forall e : {set G},
      (e \in x15_edge_set G) = [exists i : 'I_m, e \in E i]) /\
  forall i j : 'I_m, i != j -> [disjoint E i & E j].

Definition x15_edge_family
    (G : sgraph) (m : nat) (E : 'I_m -> {set {set G}}) : Prop :=
  forall i : 'I_m, E i \subset x15_edge_set G.


Definition N {G : sgraph} (x : G) : {set G} := [set y : G | sedge x y].
(** Maximum degree Δ(G).  Empty graph ↦ 0; users carry a non-triviality guard. *)
Definition Delta (G : sgraph) : nat := \max_(x : G) #|N(x)|.
(** Bipartite: a 2-colouring with no monochromatic edge. *)
Definition bipartite (G : sgraph) : Prop := 
  exists f : G -> bool, forall x y : G, sedge x y -> f x != f y.
(** ⌈a/b⌉, with the mathcomp convention ⌈a/0⌉ = 0.  Graph-free arithmetic helper. *)
Definition ceil_div (a b : nat) : nat := (a + b - 1) %/ b.


(** ** X15 statements ******************************************************)

(** Corpus row: arxiv:1611.03196#02
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/1611.03196__02/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/1611.03196__02.json
    English statement: (Aharoni, Alon, Berger, Chudnovsky, Kotlar, Loebl, Ziv 2016,
      "Conjecture 1.14")
      For every m, every simple graph H and every family E_0, ..., E_{m-1} of sets of
      edges of H that partitions the edge set of H, there is a matching M of H such
      that for every i, the number of edges of M inside E_i is at least the floor of
      |E_i| divided by Delta(H) + 2.
    Definitions: [x15_edge_set G] — the two-element vertex sets {x, y} joined by
      [sedge] (this file); [x15_matching M] — M is a set of edges of G in which every
      vertex lies in at most one member (this file); [x15_edge_partition E] — an edge
      belongs to the edge set of G exactly when it belongs to some part, and distinct
      parts are disjoint (this file); [Delta] — maximum degree, defined locally in this
      file rather than taken from GTBase base.
    Notes: REFUTED (branch fair-matching-edge-part of this repository, file
      theories/applications/fair_matching_edge_partition_disproved.v): the graph 5 K_4
      (five disjoint copies of K_4, on 'I_20) with six classes of five edges each is a
      counterexample, so the conjecture is false. The body is identical to the X15.v
      definition of the same name; this file is a self-contained scratch variant of
      conjectures/X15.v, is not listed in packing-theory/_CoqProject, and redefines
      [N], [Delta], [bipartite] and [ceil_div] locally instead of importing GTBase
      base. The parts are indexed by 'I_m, so m = 0 forces the graph to be edgeless;
      the bound uses MathComp floor division. *)
Definition fair_matching_edge_partition_statement : Prop :=
  forall (m : nat) (H : sgraph) (E : 'I_m -> {set {set H}}),
    x15_edge_partition E ->
    exists M : {set {set H}},
      x15_matching M /\
      forall i : 'I_m,
        (#|E i| %/ (Delta H + 2) <= #|M :&: E i|)%N.

(** Corpus row: arxiv:1611.03196#03
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/1611.03196__03/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/1611.03196__03.json
    English statement: (Aharoni, Alon, Berger, Chudnovsky, Kotlar, Loebl, Ziv 2016,
      "Conjecture 1.15")
      For every m there is a constant c, bounded by 32 * (m+1)^3, such that for every
      bipartite simple graph G of positive maximum degree and every family
      E_0, ..., E_{m-1} of sets of edges of G (not required to be a partition), there
      is a matching S of G with floor(|E(G)| / Delta(G)) <= |S| + c and, for every i,
      the number of edges of S inside E_i at most the ceiling of |E_i| divided by
      Delta(G).
    Definitions: [x15_edge_set G] — the two-element vertex sets {x, y} joined by
      [sedge] (this file); [x15_matching S] — a set of edges in which every vertex lies
      at most once (this file); [x15_edge_family E] — every part is a set of edges of G
      (this file); [bipartite], [Delta], [ceil_div a b] = (a+b-1) %/ b — all defined
      locally in this file rather than taken from GTBase base.
    Notes: DISCREPANCY — unlike the X15.v definition of the same name, this body also
      asserts the explicit bound c <= 32 * (m+1)^3, so it is strictly stronger than
      corpus row arxiv:1611.03196#03, which only asks that some c(m) exist; it is in
      fact X15.v's orphan variant
      [bipartite_matching_underrepresentation_llm_statement] carrying the corpus name.
      This file is a self-contained scratch variant of conjectures/X15.v and is not
      listed in packing-theory/_CoqProject. Both forms are PROVED in this development:
      theories/foundations/fair_matching.v proves the X15.v llm variant with the same
      bound 32*(m+1)^3, and Conjecture 1.15 itself with c(m) = 12m + 14. The size bound
      |S| >= |E(G)|/Delta(G) - c is rendered over naturals as
      floor(|E(G)|/Delta(G)) <= |S| + c, avoiding truncated subtraction; the guard
      0 < Delta(G) excludes the edgeless graph, where division by Delta(G) = 0 is
      degenerate. *)
Definition bipartite_matching_underrepresentation_statement : Prop :=
  forall m : nat, exists c : nat,
    c <= 32 * (m + 1)^3 /\
    forall (G : sgraph) (E : 'I_m -> {set {set G}}),
      bipartite G ->
      0 < Delta G ->
      x15_edge_family E ->
      exists S : {set {set G}},
        x15_matching S /\
        (#|x15_edge_set G| %/ Delta G <= #|S| + c)%N /\
        forall i : 'I_m,
          #|S :&: E i| <= ceil_div #|E i| (Delta G).


Print Graph.                            (* all coercion paths *)
Print Coercion Paths sgraph Sortclass.  (* should show digraph_of ; rel_car ; Finite.sort *)
About svertex.                          (* confirms: not a coercion *)
