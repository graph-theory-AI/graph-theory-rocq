(** Public-only edge-family client, with no conjecture imports. *)
From GTBase Require Import base.
From Packing.foundations Require Import edge_families.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Client.
Variables (G : sgraph) (m n : nat) (E F : 'I_m -> {set {set G}}).

Example all_members_are_edges :
  edge_family E -> forall i e, e \in E i -> e \in E(G).
Proof. exact: edge_family_member. Qed.

Example shrinking_members_preserves_validity :
  edge_family E -> (forall i, F i \subset E i) -> edge_family F.
Proof. exact: edge_family_subfamily. Qed.

Example repeated_indices_preserve_validity (f : 'I_n -> 'I_m) :
  edge_family E -> edge_family (fun j => E (f j)).
Proof. exact: edge_family_reindex. Qed.

End Client.

Example a_graph_with_edges_accepts_zero_indices
    (E : 'I_0 -> {set {set 'K_2}}) : edge_family E.
Proof. exact: edge_family0. Qed.

Example empty_members_are_allowed :
  edge_family (fun _ : 'I_2 => (set0 : {set {set 'K_2}})).
Proof. exact: edge_family_empty. Qed.

Example repeated_nonempty_members_are_allowed :
  edge_family (fun _ : 'I_2 => E('K_2)).
Proof. exact: edge_family_K2_repeated. Qed.

Example those_members_overlap : ~ [disjoint E('K_2) & E('K_2)].
Proof. exact: K2_repeated_members_overlap. Qed.

Example singleton_vertex_edges_are_rejected :
  ~ edge_family (fun _ : 'I_1 => [set [set (ord0 : 'K_2)]]).
Proof. exact: not_edge_family_loop. Qed.

Example empty_vertex_set_edges_are_rejected :
  ~ edge_family (fun _ : 'I_1 => [set (set0 : {set 'K_2})]).
Proof. exact: not_edge_family_empty_edge. Qed.

Print Assumptions repeated_indices_preserve_validity.
Print Assumptions a_graph_with_edges_accepts_zero_indices.
Print Assumptions repeated_nonempty_members_are_allowed.
Print Assumptions those_members_overlap.
Print Assumptions singleton_vertex_edges_are_rejected.
Print Assumptions empty_vertex_set_edges_are_rejected.
