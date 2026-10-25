(** Witness hint (Lancelot's lane, 2026-10-25): an axiom-free REFUTATION of
    [Digraph.conjectures.colouring_variants.majority_3col_eulerian_statement] as encoded before its loopless guard
    (corpus row arxiv:1608.03040#04 (Open Problem 3; the looped vertex is balanced, in-degree = out-degree = 1)).

    [diGraphType] allows loops, and a loop at v makes v an out-neighbour of itself carrying its own
    colour.  On the one-vertex digraph with a loop, v has out-degree 1 and one same-coloured
    out-neighbour, so the majority bound fails for every colouring.  The source's digraphs have no
    loops: its own Theorem 1 (every digraph has a majority 4-colouring) fails on this digraph.  With
    the loopless guard this file no longer compiles (hint-stale-FIX-OK). *)
From HB Require Import structures.
From mathcomp Require Import all_boot.
From Digraph Require Import prelude digraph oriented.
From Digraph.conjectures Require Import colouring_variants.
From Digraph.foundations Require degree_balance.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition loop1 : Type := unit.
HB.instance Definition _ := Finite.copy loop1 unit.
HB.instance Definition _ := HasArc.Build loop1 (fun _ _ => true).

Lemma loop1_same (k : nat) (col : loop1 -> 'I_k) :
  #|same_col_outnb col (tt : loop1)| = 1.
Proof.
rewrite /same_col_outnb.
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

Lemma loop1_eulerian : eulerian loop1.
Proof.
apply/forallP => -[]; rewrite /degree_balance.indeg loop1_outdeg.
have -> : [set u : loop1 | u --> (tt : loop1)] = setT by apply/setP => -[]; rewrite !inE.
by rewrite cardsT card_unit.
Qed.

Lemma refuted : ~ majority_3col_eulerian_statement.
Proof.
move=> /(_ loop1 loop1_eulerian) [col /forallP /(_ tt)].
by rewrite loop1_same loop1_outdeg.
Qed.

Print Assumptions refuted.
