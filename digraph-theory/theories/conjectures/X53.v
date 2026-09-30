(** * Digraph.conjectures.X53 -- v2 asymmetric bipartite girth row *)

From HB Require Import structures.
From mathcomp Require Import all_boot.
From Digraph Require Import prelude digraph oriented dipath.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X53 vocabulary ************************************************)

Definition x53_bipartition (D : diGraphType) (A B : {set D}) : Prop :=
  [disjoint A & B] /\
  A :|: B = [set: D] /\
  forall u v : D,
    u --> v ->
    ((u \in A) && (v \in B)) || ((u \in B) && (v \in A)).

Definition x53_out_to (D : diGraphType) (S : {set D}) (v : D) : nat :=
  #|[set w in S | v --> w]|.

Definition x53_positive_rational (num den : nat) : Prop :=
  0 < num /\ 0 < den.

Definition x53_k_alpha_plus_beta_gt_one
    (k alpha_num alpha_den beta_num beta_den : nat) : Prop :=
  (alpha_den * beta_den
    < k * alpha_num * beta_den + beta_num * alpha_den)%N.

(** ** X53 statements ******************************************************)

(** Corpus row: arxiv:1809.08324#01
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/1809.08324__01/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/1809.08324__01.json
    English statement: (Seymour and Spirkl 2018, Short directed cycles in bipartite digraphs, arXiv:1809.08324, Conjecture 1.5)
      For every k >= 1 and all positive rationals alpha and beta with k * alpha + beta > 1,
      every nonempty finite digraph whose vertex set splits into parts A and B with every arc
      going between the parts, in which every vertex of A has at least beta * #|B|
      out-neighbours in B and every vertex of B has at least alpha * #|A| out-neighbours in A,
      has a directed cycle with at most 2k vertices.
    Definitions: [x53_bipartition A B] - disjoint parts covering all vertices with every arc
      crossing (this file); [x53_out_to S v] - the number of out-neighbours of v inside S (this
      file); [x53_positive_rational num den] and [x53_k_alpha_plus_beta_gt_one] - the rationals
      and the condition k * alpha + beta > 1, cleared of division (this file); [dicycle]
      (core/dipath.v).
    Notes: The reals alpha and beta of the source are encoded as positive rationals given by
      numerator and denominator, and every inequality is cleared of division; restricting to
      rationals is harmless because the hypotheses are open conditions. This is the asymmetric
      strengthening of [bipartite_digraph_outdegree_girth_statement] (conjectures/X46.v). *)
Definition bipartite_digraph_asymmetric_outdegree_girth_statement : Prop :=
  forall (k alpha_num alpha_den beta_num beta_den : nat),
    1 <= k ->
    x53_positive_rational alpha_num alpha_den ->
    x53_positive_rational beta_num beta_den ->
    x53_k_alpha_plus_beta_gt_one k alpha_num alpha_den beta_num beta_den ->
    forall (D : diGraphType) (A B : {set D}),
      0 < #|D| ->
      x53_bipartition A B ->
      (forall v : D, v \in A ->
        beta_num * #|B| <= beta_den * x53_out_to B v) ->
      (forall v : D, v \in B ->
        alpha_num * #|A| <= alpha_den * x53_out_to A v) ->
      exists c : seq D,
        dicycle c /\
        size c <= 2 * k.
