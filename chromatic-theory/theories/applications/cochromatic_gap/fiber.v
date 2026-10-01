(** * A finite counting bound for color classes of bounded size. *)
From mathcomp Require Import all_boot.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Lemma fiber_card_bound (T C : finType) (f : T -> C) b :
  (forall c, #|[set x | f x == c]| <= b) -> #|T| <= #|C| * b.
Proof.
move=> hb; rewrite -[X in X <= _](sum1_card (predT : pred T)).
rewrite (partition_big f (predT : pred C)) //=.
rewrite -sum_nat_const; apply: leq_sum=> c _.
rewrite sum1_card -cardsE.
exact: hb.
Qed.
