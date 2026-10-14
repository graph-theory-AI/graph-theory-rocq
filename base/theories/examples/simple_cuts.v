(** Public-only examples for cuts and the cut connectivity bound. *)
From GTBase Require Import base common simple_cuts.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Example empty_cut (G : sgraph) : cut_edges (set0 : {set G}) = set0.
Proof. exact: cut_edges0. Qed.

Example full_cut (G : sgraph) : cut_edges [set: G] = set0.
Proof. exact: cut_edgesT. Qed.

Example zero_bound (G : sgraph) : cut_connected G 0.
Proof. exact: cut_connected0. Qed.

Example empty_graph_bound k : cut_connected 'K_0 k.
Proof. by apply: cut_connected_small; rewrite card_ord. Qed.

Example singleton_bound k : cut_connected 'K_1 k.
Proof. by apply: cut_connected_small; rewrite card_ord. Qed.

Example singleton_not_deletion_connected : ~ k_edge_connected 'K_1 1.
Proof. exact: not_k_edge_connected_K1. Qed.

Example complete_two_bound : cut_connected 'K_2 1.
Proof. exact: k_edge_connected_cut k_edge_connected_K2. Qed.

Example complete_two_cut : #|cut_edges (G := 'K_2) [set ord0]| = 1.
Proof.
by rewrite card_cut_edges cut_size_edges_between edges_between_Kn cards1 cardsC1 card_ord setICr cards0.
Qed.

Example complete_two_not_two : ~ cut_connected 'K_2 2.
Proof.
move=> H.
have S0 : [set (ord0 : 'I_2)] != set0 by rewrite -cards_eq0 cards1.
have ST : [set (ord0 : 'I_2)] != [set: 'I_2].
  apply/eqP => eq.
  have := congr1 (fun S : {set 'I_2} => #|S|) eq.
  by rewrite cards1 cardsT card_ord.
by have := H _ S0 ST; rewrite complete_two_cut.
Qed.

Example complement_same_cut :
  cut_edges (G := 'K_2) (~: [set ord0]) = cut_edges (G := 'K_2) [set ord0].
Proof. exact: cut_edgesC. Qed.

Print Assumptions empty_cut.
Print Assumptions full_cut.
Print Assumptions zero_bound.
Print Assumptions empty_graph_bound.
Print Assumptions singleton_bound.
Print Assumptions singleton_not_deletion_connected.
Print Assumptions complete_two_bound.
Print Assumptions complete_two_cut.
Print Assumptions complete_two_not_two.
Print Assumptions complement_same_cut.
