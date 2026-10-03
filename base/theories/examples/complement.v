(** Downstream use of the ordinary graph complement (upstream [compl]), without corpus
    imports. *)
From GTBase Require Import base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section PublicClient.
Variable G : sgraph.

(** Same vertices; distinct vertices swap adjacency; no loops. *)
Example complement_negates_off_the_diagonal (x y : G) :
  x != y -> @edge_rel (compl G) x y = ~~ (x -- y).
Proof. exact: compl_adj_offdiag. Qed.

Example complement_has_no_loops (x : G) : ~~ @edge_rel (compl G) x x.
Proof. exact: compl_noloop. Qed.

Example double_complement_is_isomorphic : compl (compl G) ≃ G.
Proof. exact: compl_compl_diso. Qed.

(** A hand-built complement is the upstream one up to the identity isomorphism. *)
Example hand_built_complement (r : rel G) (rs : symmetric r) (ri : irreflexive r) :
  r =2 @compl_rel G -> SGraph rs ri ≃ compl G.
Proof. exact: compl_eq_diso. Qed.

End PublicClient.

(** Degenerate and concrete cases. *)
Example complement_of_K0_and_K1_are_edgeless :
  (forall x y : ('K_0 : sgraph), ~~ @edge_rel (compl 'K_0) x y) /\
  (forall x y : ('K_1 : sgraph), ~~ @edge_rel (compl 'K_1) x y).
Proof. by split=> x y; apply: compl_Kn_edgeless. Qed.

Example complement_of_K3_is_edgeless (x y : 'K_3) : ~~ @edge_rel (compl 'K_3) x y.
Proof. exact: compl_Kn_edgeless. Qed.

(** Positive: the complement of two isolated vertices has their edge. *)
Example complement_of_two_isolated_vertices :
  @edge_rel (compl (del_edge_set 'K_2 [set [set: 'K_2]])) ord0 ord_max.
Proof.
rewrite compl_adjE del_edge_set1 /=.
by rewrite eqEcard subsetT cards2 cardsT card_ord.
Qed.

Print Assumptions double_complement_is_isomorphic.
Print Assumptions complement_of_two_isolated_vertices.
