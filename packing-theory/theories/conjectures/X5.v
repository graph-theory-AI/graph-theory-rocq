(** * Packing.conjectures.X5 -- v2 milestone X5, clean packing rows *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local packing vocabulary ********************************************)

Definition x5_is_triangle (G : sgraph) (T : {set G}) : Prop :=
  clique T /\ #|T| = 3.

Definition x5_tri_edges (G : sgraph) (T : {set G}) : {set {set G}} :=
  [set e : {set G} | (e \subset T) && (#|e| == 2)].

Definition x5_edge_set (G : sgraph) : {set {set G}} :=
  [set e : {set G} |
      [exists x : G, [exists y : G, (x -- y) && (e == [set x; y])]]].

Definition x5_edge_disjoint_triangles (G : sgraph) (ts : seq {set G}) : Prop :=
  uniq ts /\
  (forall T : {set G}, T \in ts -> x5_is_triangle T) /\
  forall T U : {set G}, T \in ts -> U \in ts -> T != U ->
    [disjoint x5_tri_edges T & x5_tri_edges U].

Definition x5_triangle_edge_transversal
    (G : sgraph) (F : {set {set G}}) : Prop :=
  F \subset x5_edge_set G /\
  forall T : {set G}, x5_is_triangle T ->
    exists e : {set G}, e \in F /\ e \in x5_tri_edges T.

Definition x5_pairwise_disjoint_sets
    (G : sgraph) (m : nat) (A : 'I_m -> {set G}) : Prop :=
  forall i j : 'I_m, i != j -> [disjoint A i & A j].

(** ** X5 statements *******************************************************)

(** Corpus row: erdos:167
    Site: none
    Review: none
    English statement: (Erdos problem #167)
      For every simple graph G and every k: if every list of pairwise edge-disjoint
      triangles of G has at most k members, then there is a set F of at most 2k edges
      of G meeting every triangle of G.
    Definitions: [x5_is_triangle T] — T is a clique with exactly three vertices (this
      file); [x5_tri_edges T] — the two-element subsets of T (this file);
      [x5_edge_set G] — the two-element vertex sets {x, y} with x -- y (this file);
      [x5_edge_disjoint_triangles ts] — a repetition-free list of triangles whose edge
      sets are pairwise disjoint (this file); [x5_triangle_edge_transversal F] — F is a
      set of edges of G and every triangle has one of its edges in F (this file);
      [clique] — coq-graph-theory sgraph.v.
    Notes: this row is the Erdos-numbered twin of opg:triangle_packing_vs_triangle_edge_transversal (U9.v, [triangle_packing_vs_triangle_edge_transversal_statement]);
      the encodings differ only in the packing being a repetition-free list here and a
      set there, and in F being required to consist of genuine edges here. *)
Definition triangle_packing_transversal_statement : Prop :=
  forall (G : sgraph) (k : nat),
    (forall ts : seq {set G}, x5_edge_disjoint_triangles ts -> size ts <= k) ->
    exists F : {set {set G}},
      x5_triangle_edge_transversal F /\ #|F| <= 2 * k.

(** Corpus row: erdos:914
    Site: none
    Review: none
    English statement: (Erdos problem #914)
      For all r >= 2 and m >= 1 and every simple graph G with exactly r * m vertices in
      which every vertex has at least m * (r-1) neighbours, there are m pairwise
      disjoint vertex sets A_0, ..., A_{m-1}, each of exactly r vertices and each a
      clique — that is, G contains m vertex-disjoint copies of K_r.
    Definitions: [x5_pairwise_disjoint_sets A] — the A i are pairwise disjoint (this
      file); [clique] — coq-graph-theory sgraph.v.
    Notes: the corpus row is marked solved. "m vertex-disjoint copies of K_r" is
      rendered as m pairwise disjoint r-element cliques, which on r * m vertices is
      equivalent to a K_r-factor. *)
Definition clique_factor_min_degree_statement : Prop :=
  forall (r m : nat) (G : sgraph),
    2 <= r -> 1 <= m ->
    #|G| = r * m ->
    (forall v : G, m * (r - 1) <= #|N(v)|) ->
    exists A : 'I_m -> {set G},
      x5_pairwise_disjoint_sets A /\
      forall i : 'I_m, #|A i| = r /\ clique (A i).
