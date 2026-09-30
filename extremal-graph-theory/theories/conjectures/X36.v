(** * Extremal.conjectures.X36 -- v2 divisible-subgraph row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X36 vocabulary ************************************************)

Definition x36_edge_set (G : sgraph) : {set {set G}} :=
  [set e : {set G} |
      [exists x : G, [exists y : G, (x -- y) && (e == [set x; y])]]].

Definition x36_degree_in_edge_set
    (G : sgraph) (F : {set {set G}}) (v : G) : nat :=
  #|[set e in F | v \in e]|.

Definition x36_nonempty_k_divisible_subgraph (G : sgraph) (k : nat) : Prop :=
  exists F : {set {set G}},
    F != set0 /\
    F \subset x36_edge_set G /\
    forall v : G, x36_degree_in_edge_set F v %% k == 0.

(** Corpus row: studies:std_alon_friedland_kalai_conjecture
    Site: none
    Review: none
    English statement: (Alon, Friedland and Kalai, "Alon-Friedland-Kalai Conjecture")
      For every k > 0, every graph G containing no non-empty k-divisible subgraph (a non-empty
      set of edges in which every vertex has degree divisible by k) has at most (k-1) * |V(G)|
      edges.
    Definitions: [x36_edge_set G] - the edges of G as 2-element vertex sets (X36.v);
      [x36_degree_in_edge_set G F v] - the number of edges of F containing v (X36.v);
      [x36_nonempty_k_divisible_subgraph G k] - a non-empty subset of the edges in which every
      vertex of G has degree divisible by k (X36.v).
    Notes: this row comes from the studies slice of the corpus, which has no site or review page. A
      subgraph is modelled by its edge set, and the divisibility condition is required at every
      vertex of G, which is equivalent to requiring it at the vertices the edge set touches
      (untouched vertices have degree 0, divisible by k). The subtraction k - 1 is safe because
      0 < k is assumed. *)
Definition alon_friedland_kalai_divisible_subgraph_statement : Prop :=
  forall (k : nat) (G : sgraph),
    0 < k ->
    ~ x36_nonempty_k_divisible_subgraph G k ->
    #|x36_edge_set G| <= (k - 1) * #|G|.
