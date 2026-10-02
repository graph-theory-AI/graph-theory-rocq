(** Downstream use of single-edge deletion [del_edge_set G [set e]], without
    corpus imports. *)
From GTBase Require Import common.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section PublicClient.
Variable G : sgraph.

Example a_real_edge_is_removed (x y : G) :
  ~~ @edge_rel (del_edge_set G [set [set x; y]]) x y.
Proof. exact: del_edge_set1_edge. Qed.

Example other_pairs_keep_their_adjacency (e : {set G}) (x y : G) :
  [set x; y] != e -> @edge_rel (del_edge_set G [set e]) x y = x -- y.
Proof. exact: del_edge_set1_other. Qed.

Example deleting_a_non_pair_changes_nothing (e : {set G}) :
  #|e| != 2 -> @edge_rel (del_edge_set G [set e]) =2 @edge_rel G.
Proof. exact: del_edge_set1_invalid. Qed.

Example empty_and_singleton_pairs_are_no_ops (x : G) :
  @edge_rel (del_edge_set G [set set0]) =2 @edge_rel G /\
  @edge_rel (del_edge_set G [set [set x]]) =2 @edge_rel G.
Proof. by split; apply: del_edge_set1_invalid; rewrite ?cards0 ?cards1. Qed.

Example deleting_twice_is_deleting_once (e : {set G}) :
  @edge_rel (del_edge_set (del_edge_set G [set e]) [set e]) =2
  @edge_rel (del_edge_set G [set e]).
Proof. exact: del_edge_set1_twice. Qed.

(** Induced-freeness depends on the host only up to isomorphism. *)
Example host_isomorphism_preserves_freeness (G' H : sgraph) :
  G ≃ G' -> induced_free G H -> induced_free G' H.
Proof. exact: induced_free_host_diso. Qed.

End PublicClient.

Example triangle_loses_exactly_the_deleted_edge :
  ~~ @edge_rel (del_edge_set 'K_3 [set [set ord0; ord_max]]) ord0 ord_max /\
  @edge_rel (del_edge_set 'K_3 [set [set ord0; ord_max]]) ord0 (@Ordinal 3 1 isT).
Proof. exact: del_edge_set_K3. Qed.

Example a_three_vertex_pair_deletes_nothing :
  @edge_rel (del_edge_set 'K_3 [set [set: 'K_3]]) =2 @edge_rel 'K_3.
Proof. by apply: del_edge_set1_invalid; rewrite cardsT card_ord. Qed.
