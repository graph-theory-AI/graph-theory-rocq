(** Downstream use of the public induced-free API, without corpus imports. *)
From GTBase Require Import common.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section PublicClient.
Variable G : sgraph.

Example empty_pattern_is_never_excluded : ~ induced_free G 'K_0.
Proof. apply: not_induced_free_pattern0. by rewrite card_ord. Qed.

Example singleton_exclusion_characterizes_empty :
  induced_free G 'K_1 <-> #|G| = 0.
Proof. exact: induced_free_K1. Qed.

End PublicClient.

Example complete_four_is_claw_free : induced_free 'K_4 'K_1,3.
Proof. exact: induced_free_K4_claw. Qed.

Example triangle_contains_an_induced_edge : ~ induced_free 'K_3 'K_2.
Proof. exact: not_induced_free_K3_K2. Qed.
