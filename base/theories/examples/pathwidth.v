(** Public-only pathwidth clients: supplied graph indices and successor bounds. *)
From GTBase Require Import base path_trees bag_decompositions pathwidth.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Example empty_width_zero : pathwidth_at_most 'K_0 0.
Proof. exact: pathwidth_at_most_K0. Qed.
Example singleton_width_zero : pathwidth_at_most 'K_1 0.
Proof. exact: pathwidth_at_most_K1. Qed.
Example edge_width_one : pathwidth_at_most 'K_2 1.
Proof. exact: pathwidth_at_most_K2. Qed.
Example edge_not_width_zero : ~ pathwidth_at_most 'K_2 0.
Proof. exact: not_pathwidth_at_most_K2_0. Qed.
Example larger_bound (G : sgraph) (k : nat) :
  pathwidth_at_most G k -> pathwidth_at_most G k.+1.
Proof. exact: pathwidth_at_mostW (leqnSn k). Qed.

(** A genuinely unused index carrying an empty bag remains permitted. *)
Example unused_empty_bag : pathwidth_at_most 'K_1 0.
Proof.
apply: (@pathwidth_at_mostI 'K_1 'K_2
  (fun t => if t == ord0 then [set: 'K_1] else set0) 0).
- exact: path_tree_K2.
- exact: bag_decomposition_unused_empty_bag.
- by move=> t; case: (t == ord0); rewrite ?cardsT ?card_ord ?cards0.
Qed.

Example supplied_witness (G : sgraph) (k : nat) : pathwidth_at_most G k ->
  exists (T : sgraph) (bag : T -> {set G}),
    path_tree T /\ bag_decomposition bag /\ forall t : T, #|bag t| <= k.+1.
Proof. exact: pathwidth_at_most_witness. Qed.
