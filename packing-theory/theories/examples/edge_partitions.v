(** Public-only indexed edge-partition client, with no conjecture imports. *)
From GTBase Require Import base.
From Packing.foundations Require Import edge_partitions.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section PublicClient.
Variables (G : sgraph) (m : nat) (E : 'I_m -> {set {set G}}).

Example partition_covers_every_edge :
  edge_partition E -> forall e, e \in E(G) -> exists i, e \in E i.
Proof. exact: edge_partition_cover. Qed.

Example partition_assigns_one_index :
  edge_partition E -> forall e, e \in E(G) -> #|[set i | e \in E i]| = 1.
Proof. by move=> /edge_partition_uniqP[]. Qed.

Example sizes_add_up : edge_partition E -> \sum_i #|E i| = #|E(G)|.
Proof. exact: card_edge_partition. Qed.

End PublicClient.

Example edgeless_graph_accepts_zero_parts (E : 'I_0 -> {set {set 'K_1}}) :
  edge_partition E.
Proof. exact: edge_partition_K1_0. Qed.

Example an_edge_needs_a_part (E : 'I_0 -> {set {set 'K_2}}) :
  ~ edge_partition E.
Proof. exact: not_edge_partition_K2_0. Qed.

Example two_empty_parts_are_allowed : edge_partition K2_with_empty_parts.
Proof. exact: edge_partition_K2_empty_part. Qed.

Example those_two_parts_are_empty :
  K2_with_empty_parts (@Ordinal 3 1 isT) = set0 /\
  K2_with_empty_parts (@Ordinal 3 2 isT) = set0.
Proof. exact: K2_repeated_empty_parts. Qed.

Example a_duplicated_edge_is_rejected :
  ~ edge_partition (fun _ : 'I_2 => E('K_2)).
Proof. exact: not_edge_partition_K2_duplicate. Qed.

Example a_loop_member_is_rejected :
  ~ edge_partition (fun _ : 'I_1 => [set [set (ord0 : 'K_2)]]).
Proof. exact: not_edge_partition_K2_loop. Qed.

Print Assumptions partition_assigns_one_index.
Print Assumptions sizes_add_up.
Print Assumptions two_empty_parts_are_allowed.
Print Assumptions a_duplicated_edge_is_rejected.
Print Assumptions a_loop_member_is_rejected.
