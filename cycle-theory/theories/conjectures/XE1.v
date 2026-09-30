(** * Cycle.conjectures.XE1 -- Erdős open clean/bounded rows *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition xe1_edge_set (G : sgraph) : {set {set G}} :=
  [set e : {set G} |
      [exists x : G, [exists y : G, (x -- y) && (e == [set x; y])]]].

Definition xe1_cycle_edges (G : sgraph) (c : seq G) : {set {set G}} :=
  [set e : {set G} |
      [exists p : G * G,
        [&& p.1 \in c, p.2 \in c, p.1 -- p.2,
            e == [set p.1; p.2] &
            (((p.1, p.2) \in zip c (rot 1 c)) ||
             ((p.2, p.1) \in zip c (rot 1 c)))]]].

Definition xe1_cycle (G : sgraph) (c : seq G) : Prop :=
  ucycle (--) c /\ 2 < size c.

Definition xe1_cycle_or_edge_piece (G : sgraph) (P : {set {set G}}) : Prop :=
  (exists c : seq G, xe1_cycle c /\ P = xe1_cycle_edges c) \/
  (exists e : {set G}, e \in xe1_edge_set G /\ P = [set e]).

Definition xe1_pairwise_edge_disjoint
    (G : sgraph) (m : nat) (P : 'I_m -> {set {set G}}) : Prop :=
  forall i j : 'I_m, i != j -> [disjoint P i & P j].

Definition xe1_covers_edges
    (G : sgraph) (m : nat) (P : 'I_m -> {set {set G}}) : Prop :=
  forall e : {set G}, e \in xe1_edge_set G -> exists i : 'I_m, e \in P i.

(** Corpus row: erdos:184
    Site: none
    Review: none
    English statement: (Erdos problem #184)
      There is a natural constant C such that every simple graph G has a family of at most
      C times the number of vertices of G pairwise disjoint sets of edges which together
      contain every edge of G, each member of the family being either the edge set of a
      cycle through more than two vertices or a single edge.
    Definitions: [xe1_edge_set G] - the two-element vertex sets that are edges (XE1.v);
      [xe1_cycle_edges c] - the set of edges joining vertices consecutive along c (XE1.v);
      [xe1_cycle c] - c is a [ucycle] of length more than two (XE1.v);
      [xe1_cycle_or_edge_piece P] - P is the edge set of such a cycle, or a singleton edge
      (XE1.v); [xe1_pairwise_edge_disjoint P] and [xe1_covers_edges P] - the pieces are
      pairwise disjoint and every edge lies in one of them (XE1.v); [ucycle] (MathComp
      path.v).
    Notes: the asymptotic "O(n) many" is encoded by a single constant C quantified
      outermost and the bound m <= C * |V(G)|, uniform over all finite simple graphs, which
      is the intended reading. Pieces are indexed by a finite ordinal type of size m, so
      the family is a list without repetition of indices; disjointness plus covering makes
      it a partition of the edge set. The corpus row has no site or review page. *)
Definition erdos_184_statement : Prop :=
  exists C : nat,
    forall G : sgraph,
      exists m : nat, exists P : 'I_m -> {set {set G}},
        m <= C * #|G| /\
        xe1_pairwise_edge_disjoint P /\
        xe1_covers_edges P /\
        forall i : 'I_m, xe1_cycle_or_edge_piece (P i).

