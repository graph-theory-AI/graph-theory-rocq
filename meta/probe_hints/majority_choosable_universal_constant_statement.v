(** Witness hint (Lancelot's lane, item 4b, 2026-10-25): an axiom-free REFUTATION of
    [Digraph.conjectures.X51.majority_choosable_universal_constant_statement] as encoded before its
    loopless guard (corpus row arxiv:1608.03040#06, Open Problem 7).

    [diGraphType] allows loops, and a loop at v makes v an out-neighbour of itself carrying its own
    colour.  On the one-vertex digraph with a loop, v has out-degree 1 and one same-coloured
    out-neighbour, so the majority bound fails for every colouring, whatever the lists and whatever
    the constant c.  The source's digraphs have no loops (Arthur's F1 of 2026-10-25 found the same
    defect, kernel-checked as r_x51_false).  With the loopless guard this file no longer compiles
    (hint-stale-FIX-OK). *)
From HB Require Import structures.
From mathcomp Require Import all_boot.
From Digraph Require Import prelude digraph oriented.
From Digraph.conjectures Require Import X51.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition loop1 : Type := unit.
HB.instance Definition _ := Finite.copy loop1 unit.
HB.instance Definition _ := HasArc.Build loop1 (fun _ _ => true).

Lemma loop1_same (C : finType) (col : loop1 -> C) :
  x51_same_colour_outneighbours col (tt : loop1) = 1.
Proof.
rewrite /x51_same_colour_outneighbours.
have -> : [set w : loop1 | ((tt : loop1) --> w) && (col w == col tt)] = setT.
  by apply/setP => -[]; rewrite !inE eqxx.
by rewrite cardsT card_unit.
Qed.

Lemma loop1_outdeg : outdeg (tt : loop1) = 1.
Proof.
rewrite /outdeg.
have -> : [set w : loop1 | (tt : loop1) --> w] = setT by apply/setP => -[]; rewrite !inE.
by rewrite cardsT card_unit.
Qed.

Lemma refuted : ~ majority_choosable_universal_constant_statement.
Proof.
move=> [c [_ h]].
have [col [_ /(_ tt)]] := h loop1 'I_c (fun _ => setT) (fun _ => ltac:(by rewrite cardsT card_ord)).
by rewrite loop1_same loop1_outdeg.
Qed.

Print Assumptions refuted.
