From HB Require Import structures.
From mathcomp Require Import all_boot.
From Digraph Require Import prelude digraph dipath classic_core.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* A one-vertex digraph with a loop. [stable] counts loops inside S, so its only stable set is
   empty, while its single vertex is a longest directed path (ell = 0) that S must meet. This
   refuted the body without the loopless guard; with the guard it no longer compiles. *)
Definition loop1 : Type := unit.
HB.instance Definition _ := Finite.copy loop1 unit.
HB.instance Definition _ := HasArc.Build loop1 (fun _ _ => true).

Lemma loop1_stable_empty (S : {set loop1}) : stable S -> S = set0.
Proof.
move=> stS; apply/setP => x; rewrite inE; apply/negP => xS.
by move: stS => /forallP /(_ x) /implyP /(_ xS) /forallP /(_ x) /implyP /(_ xS).
Qed.

Lemma refuted : ~ stable_meeting_longest_dipaths_statement.
Proof.
move=> /(_ loop1) [S [/loop1_stable_empty S0 meet]].
have ell0 : ell loop1 = 0%N.
  by apply/eqP; rewrite -leqn0; apply/bigmax_leqP => -[k] /=; rewrite card_unit ltnS leqn0.
have [v] := meet tt [::] (erefl true) (esym ell0).
by rewrite S0 in_set0.
Qed.

Print Assumptions refuted.
