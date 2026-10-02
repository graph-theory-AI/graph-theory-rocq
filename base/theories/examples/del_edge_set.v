(** Downstream use of the public edge-set deletion API, without corpus imports. *)
From GTBase Require Import common.
From GraphTheory Require Import coloring.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section PublicClient.
Variable G : sgraph.

Example deleting_nothing_keeps_adjacency :
  @edge_rel (del_edge_set G set0) =2 @edge_rel G.
Proof. exact: del_edge_set0. Qed.

Example deleting_every_edge_leaves_none (x y : G) :
  ~~ @edge_rel (del_edge_set G E(G)) x y.
Proof. exact: del_edge_setT. Qed.

Example deleting_non_edges_changes_nothing (F : {set {set G}}) :
  [disjoint F & E(G)] -> @edge_rel (del_edge_set G F) =2 @edge_rel G.
Proof. exact: del_edge_set_nonedges. Qed.

Example remaining_edges_are_the_set_difference (F : {set {set G}}) :
  E(del_edge_set G F) = E(G) :\: F.
Proof. exact: edges_del_edge_set. Qed.

Example vertices_are_kept (F : {set {set G}}) : #|del_edge_set G F| = #|G|.
Proof. exact: card_del_edge_set. Qed.

(** A graph built directly on the deletion relation has the chromatic number of
    [del_edge_set G F]: same-carrier isomorphism, then [chi_diso]. *)
Example chi_of_a_direct_deletion (F : {set {set G}})
    (r_sym : symmetric (del_es_rel F)) (r_irrefl : irreflexive (del_es_rel F)) :
  χ([set: SGraph r_sym r_irrefl]) = χ([set: del_edge_set G F]).
Proof. by apply/chi_diso/del_edge_set_eq_diso. Qed.

End PublicClient.

Example triangle_minus_one_edge :
  let T := del_edge_set 'K_3 [set [set ord0; ord_max]] in
  ~~ @edge_rel T ord0 ord_max /\ @edge_rel T ord0 (@Ordinal 3 1 isT).
Proof. exact: del_edge_set_K3. Qed.
