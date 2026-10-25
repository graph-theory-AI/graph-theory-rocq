From HB Require Import structures.
From mathcomp Require Import all_boot.
From Digraph Require Import prelude digraph dipath two_extremal classic_core colouring_variants.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* A one-vertex digraph with a loop. [classic_core.stable] counts loops inside S, so its only
   stable set is empty and its vertex reaches no vertex of S. This refuted the body without the
   [loopless D] guard (added 2026-10-25); with the guard it no longer compiles. *)
Definition loop1 : Type := unit.
HB.instance Definition _ := Finite.copy loop1 unit.
HB.instance Definition _ := HasArc.Build loop1 (fun _ _ => true).

Lemma loop1_stable_empty (S : {set loop1}) : stable S -> S = set0.
Proof.
move=> stS; apply/setP => x; rewrite inE; apply/negP => xS.
by move: stS => /forallP /(_ x) /implyP /(_ xS) /forallP /(_ x) /implyP /(_ xS).
Qed.

Lemma refuted : ~ sands_sauer_woodrow_statement.
Proof.
move=> /(_ 1%N) [f /(_ loop1 (fun _ _ => ord0))] [S [[parts [_ stP SE]] reach]].
have S0 : S = set0.
  rewrite SE; elim: parts stP {SE} => [|P ps IH] /=; first by rewrite big_nil.
  by case/andP => sP sps; rewrite big_cons (loop1_stable_empty sP) set0U IH.
by have [s] := reach tt; rewrite S0 inE.
Qed.

Print Assumptions refuted.
