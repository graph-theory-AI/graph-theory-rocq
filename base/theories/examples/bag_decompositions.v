(** Public-only C13 client: supplied bags, empty/unused/cyclic indices and upstream transport. *)
From mathcomp Require Import all_boot.
From GraphTheory Require Import preliminaries digraph sgraph treewidth.
From GTBase Require Import bag_decompositions.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma empty_index (bag : 'K_0 -> {set 'K_0}) : bag_decomposition bag.
Proof. exact: bag_decomposition_K0. Qed.
Lemma one_vertex_one_bag : bag_decomposition (fun _ : 'K_1 => [set: 'K_1]).
Proof. exact: bag_decomposition_K1_one_bag. Qed.
Lemma one_edge_one_bag : bag_decomposition (fun _ : 'K_1 => [set: 'K_2]).
Proof. exact: bag_decomposition_K2_one_bag. Qed.
Lemma missing_vertex : ~ bag_decomposition (fun _ : 'K_1 => (set0 : {set 'K_1})).
Proof. exact: not_bag_decomposition_K1_empty_bag. Qed.
Lemma missing_edge : ~ bag_decomposition (fun t : 'K_2 => [set t]).
Proof. exact: not_bag_decomposition_K2_singleton_bags. Qed.
Lemma disconnected_fibre : ~ bag_decomposition (fun _ : two_isolated => [set: 'K_1]).
Proof. exact: not_bag_decomposition_two_isolated. Qed.
Lemma cyclic_index_allowed : bag_decomposition (fun _ : 'K_3 => [set: 'K_1]).
Proof. exact: bag_decomposition_K3_index. Qed.
Lemma cyclic_tree_guard_rejected : ~ tree_bag_decomposition (fun _ : 'K_3 => [set: 'K_1]).
Proof. exact: not_tree_bag_decomposition_K3_index. Qed.
Lemma unused_bag : bag_decomposition (fun t : 'K_2 => if t == ord0 then [set: 'K_1] else set0).
Proof. exact: bag_decomposition_unused_empty_bag. Qed.
Lemma supplied_forest_transport (G : sgraph) (T : forest) (bag : T -> {set G}) :
  bag_decomposition bag <-> sdecomp T G bag.
Proof. exact: bag_decomposition_sdecompP. Qed.
Lemma explicit_forest_guard (G T : sgraph) (tf : is_forest [set: T]) (bag : T -> {set G}) :
  bag_decomposition bag <-> sdecomp (Forest tf) G bag.
Proof. exact: bag_decomposition_forest_sdecompP. Qed.
Lemma empty_tree_guard (bag : 'K_0 -> {set 'K_0}) : tree_bag_decomposition bag.
Proof. exact: tree_bag_decomposition_K0. Qed.
Lemma covered_graph_needs_index (G T : sgraph) (bag : T -> {set G}) :
  bag_decomposition bag -> 0 < #|G| -> 0 < #|T|.
Proof. exact: bag_decomposition_nonempty_index. Qed.
