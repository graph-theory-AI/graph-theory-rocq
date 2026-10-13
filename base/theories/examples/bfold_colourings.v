(** Public-only clients of [GTBase.bfold_colourings], without conjecture or migration imports.  ['K_2] has a
    (2:1)-colouring (its two vertices get the two singletons) but no (1:1)-colouring, since an edge needs two
    disjoint colour sets.  ['K_1] takes the whole palette ['I_3] as a 3-fold colouring but has no (1:2)-colouring,
    since one vertex already needs [b <= a].  The constant empty map is a 0-fold colouring of every graph, and the
    empty graph ['K_0] is coloured by every map, with no positivity guard anywhere. *)
From GTBase Require Import base bfold_colourings.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Positive *)

Definition k2f (v : 'K_2) : {set 'I_2} := [set (v : 'I_2)].

Example k2_two_one : bfold_colouring 1 k2f.
Proof. by split=> [v|x y xy]; rewrite /k2f; [rewrite cards1 | rewrite disjoints1 in_set1; exact: xy]. Qed.

Example k1_whole_palette : bfold_colouring 3 (fun _ : 'K_1 => [set: 'I_3]).
Proof. by split=> [v|x y]; [rewrite cardsT card_ord | rewrite (ord1 x) (ord1 y) sg_irrefl]. Qed.

Example zero_fold (G : sgraph) (a : nat) : bfold_colouring 0 (fun _ : G => (set0 : {set 'I_a})).
Proof. exact: bfold_colouring0. Qed.

Example k0_every_map (a b : nat) (f : 'K_0 -> {set 'I_a}) : bfold_colouring b f.
Proof. by apply: bfold_colouring_empty; rewrite card_ord. Qed.

(** ** Negative *)

Example k2_no_one_one (f : 'K_2 -> {set 'I_1}) : ~ bfold_colouring 1 f.
Proof. by move=> h; have := @bfold_colouring_edge _ _ _ f ord0 ord_max h isT. Qed.

Example k1_no_one_two (f : 'K_1 -> {set 'I_1}) : ~ bfold_colouring 2 f.
Proof. by move=> h; have := @bfold_colouring_le _ _ _ f ord0 h. Qed.

(** The finite form decides small cases. *)
Example k2_two_one_bool :
  [forall v, #|k2f v| == 1] && [forall x, forall y, (x -- y) ==> [disjoint k2f x & k2f y]].
Proof. exact/bfold_colouringP/k2_two_one. Qed.

Print Assumptions k2_two_one.
Print Assumptions k1_whole_palette.
Print Assumptions zero_fold.
Print Assumptions k0_every_map.
Print Assumptions k2_no_one_one.
Print Assumptions k1_no_one_two.
Print Assumptions k2_two_one_bool.
