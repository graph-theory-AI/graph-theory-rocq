(** Witness hint (Any-lane guard, 2026-10-25): an axiom-free REFUTATION of
    [Digraph.conjectures.X45.majority_three_colouring_beta_statement] as encoded before its
    re-encoding (corpus row arxiv:1608.03040#02, Open Problem 1).

    [diGraphType] allows loops, and a loop at v makes v an out-neighbour of itself carrying its
    own colour.  On the one-vertex digraph with a loop, v has out-degree 1 and one out-neighbour
    of its colour, so 2 * 1 <= 1 fails for every colouring.  The same digraph violates
    "at most beta * outdeg" for every beta < 1, so the source's question needs loopless
    digraphs (the source's digraphs have no loops).  With the [loopless D] guard and the
    existential beta this file no longer compiles (hint-stale-FIX-OK). *)
From HB Require Import structures.
From mathcomp Require Import all_boot.
From Digraph Require Import prelude digraph oriented.
From Digraph.conjectures Require Import X45.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition loop1 : Type := unit.
HB.instance Definition _ := Finite.copy loop1 unit.
HB.instance Definition _ := HasArc.Build loop1 (fun _ _ => true).

Lemma refuted : ~ majority_three_colouring_beta_statement.
Proof.
move=> /(_ loop1) [col /(_ tt)].
rewrite /x45_same_colour_outneighbours /outdeg.
have -> : [set w : loop1 | ((tt : loop1) --> w) && (col w == col tt)] = setT.
  by apply/setP => -[]; rewrite !inE eqxx.
have -> : [set w : loop1 | (tt : loop1) --> w] = setT by apply/setP => -[]; rewrite !inE.
by rewrite cardsT card_unit.
Qed.

Print Assumptions refuted.
