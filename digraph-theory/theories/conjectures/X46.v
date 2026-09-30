(** * Digraph.conjectures.X46 -- v2 bipartite Caccetta-Haggkvist row *)

From HB Require Import structures.
From mathcomp Require Import all_boot.
From Digraph Require Import prelude digraph oriented dipath.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X46 vocabulary ************************************************)

Definition x46_bipartition
    (D : diGraphType) (A B : {set D}) (n : nat) : Prop :=
  [disjoint A & B] /\
  A :|: B = [set: D] /\
  #|A| = n /\
  #|B| = n /\
  forall u v : D,
    u --> v ->
    ((u \in A) && (v \in B)) || ((u \in B) && (v \in A)).

(** ** X46 statements ******************************************************)

(** Corpus row: arxiv:1809.08324#00
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/1809.08324__00/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/1809.08324__00.json
    English statement: (Seymour and Spirkl 2018, Short directed cycles in bipartite digraphs, arXiv:1809.08324, Conjecture 1.2)
      For every k >= 1, every n > 0 and every finite digraph D whose vertex set splits into two
      parts A and B of n vertices each with every arc going between the parts, if every vertex
      has out-degree strictly greater than n/(k+1) (written without division as n < (k+1) *
      outdeg v) then D has a directed cycle with at most 2k vertices.
    Definitions: [x46_bipartition A B n] - A and B are disjoint, cover all vertices, have n
      vertices each, and every arc has one end in each (this file); [dicycle] (core/dipath.v);
      [outdeg] (core/oriented.v).
    Notes: Girth at most 2k is stated as the existence of a directed cycle with at most 2k
      vertices. The strict inequality out-degree > n/(k+1) is cleared of division. *)
Definition bipartite_digraph_outdegree_girth_statement : Prop :=
  forall (k n : nat) (D : diGraphType) (A B : {set D}),
    1 <= k ->
    0 < n ->
    x46_bipartition A B n ->
    (forall v : D, n < k.+1 * outdeg v) ->
    exists c : seq D,
      dicycle c /\
      size c <= 2 * k.
