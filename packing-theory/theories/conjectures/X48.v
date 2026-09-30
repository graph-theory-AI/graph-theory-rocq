(** * Packing.conjectures.X48 -- v2 leaf-parameter tree decomposition row *)

From GTBase Require Export base.
From Packing.conjectures Require Import X47.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X48 vocabulary ************************************************)

Definition x48_leaf_count (T : sgraph) : nat :=
  #|[set v : T | #|N(v)| == 1]|.

(** ** X48 statements ******************************************************)

(** Corpus row: arxiv:1907.11600#00
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/1907.11600__00/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/1907.11600__00.json
    English statement: (Klimosova and Thomasse 2019, "Conjecture 5")
      There is a function f on natural numbers such that for every tree T and every
      simple graph G: if T has at least one edge, G is f(m)-edge-connected where m is
      the number of leaves of T, every vertex of G has at least f(|E(T)|) neighbours,
      and |E(T)| divides |E(G)|, then the edge set of G decomposes into copies of T.
    Definitions: [x48_leaf_count T] — the number of vertices of T with exactly one
      neighbour (this file); [x47_edge_set], [x47_edge_connected],
      [x47_min_degree_at_least], [x47_copy_edge_set],
      [x47_tree_decomposition_by_copies] — X47.v; [is_tree] — coq-graph-theory
      sgraph.v.
    Notes: this row differs from arxiv:1507.08208#00 (X47.v) only in the parameter
      controlling the required edge-connectivity: the number of leaves of T instead of
      its maximum degree. It inherits X47's encodings (cut-size edge-connectivity;
      parts sharing an edge are equal). *)
Definition tree_decomposition_leaf_edge_connected_statement : Prop :=
  exists f : nat -> nat,
    forall T G : sgraph,
      is_tree [set: T] ->
      0 < #|@x47_edge_set T| ->
      @x47_edge_connected G (f (x48_leaf_count T)) ->
      @x47_min_degree_at_least G (f #|@x47_edge_set T|) ->
      #|@x47_edge_set T| %| #|@x47_edge_set G| ->
      @x47_tree_decomposition_by_copies G T.
