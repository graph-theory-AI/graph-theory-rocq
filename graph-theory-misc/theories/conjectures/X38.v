(** * GTMisc.conjectures.X38 -- v2 minimum-degree irregular-subgraph row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X38 vocabulary ************************************************)

Definition x38_edge_set (G : sgraph) : {set {set G}} :=
  [set e : {set G} |
      [exists x : G, [exists y : G, (x -- y) && (e == [set x; y])]]].

Definition x38_subgraph_degree
    (G : sgraph) (F : {set {set G}}) (v : G) : nat :=
  #|[set e in F | v \in e]|.

Definition x38_degree_class_size
    (G : sgraph) (F : {set {set G}}) (k : nat) : nat :=
  #|[set v : G | x38_subgraph_degree F v == k]|.

Definition x38_min_degree_at_least (G : sgraph) (delta : nat) : Prop :=
  forall v : G, delta <= #|N(v)|.

(** ** X38 statements ******************************************************)

(** Corpus row: arxiv:2108.02685#01
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/2108.02685__01/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/2108.02685__01.json
    English statement: (Alon and Wei 2021, "Irregular Subgraphs", Conjecture 1.2)
      For every delta and every finite simple graph G of minimum degree at least delta there is
      a set F of edges of G such that, for every k, the number m of vertices having exactly k
      incident edges in F satisfies (delta+1) * m <= |V(G)| + 2 * (delta+1), which is the
      fraction-free form of m <= |V(G)|/(delta+1) + 2.
    Definitions: [x38_edge_set G] - the edges of G as two-element vertex sets (this file);
      [x38_subgraph_degree F v] - the number of edges of F containing v (this file);
      [x38_degree_class_size F k] - the number of vertices of F-degree exactly k (this file);
      [x38_min_degree_at_least G delta] - every vertex has degree at least delta (this file).
    Notes: the source quantity m(H) is the maximum over k of m(H,k); requiring the bound for
      every k, as the Rocq body does, is equivalent.  Only the upper bound is stated here, as
      in the source, in contrast with the two-sided bound of the regular case
      (graph-theory-misc/theories/conjectures/X37.v).  A spanning subgraph is modelled by its
      edge set. *)
Definition min_degree_spanning_subgraph_small_degree_multiplicity_statement : Prop :=
  forall (delta : nat) (G : sgraph),
    x38_min_degree_at_least G delta ->
    exists F : {set {set G}},
      F \subset x38_edge_set G /\
      forall k : nat,
        (delta.+1 * @x38_degree_class_size G F k <= #|G| + 2 * delta.+1)%N.
