(** Witness hint (Lancelot's lane, item 4b, 2026-10-26): an axiom-free REFUTATION of
    [Digraph.conjectures.P9.antidirected_trees_in_digraphs_statement] as encoded before its
    loopless guard (corpus row opg:antidirected_trees_in_digraphs).

    [nb_arcs] counts loops.  The one-vertex digraph with a loop has one arc, so at k = 2 it meets
    the arc-count hypothesis [(k - 2) * #|D| = 0 < 1 = nb_arcs D]; but the two-vertex antidirected
    tree (the transitive tournament [TT 2], one arc) has no injective image in one vertex.  The
    source's digraphs have no loops.  With the guard [loopless D] this file no longer compiles
    (hint-stale-FIX-OK). *)
From HB Require Import structures.
From mathcomp Require Import all_boot.
From Digraph Require Import prelude digraph oriented tournament dipath strong.
From Digraph Require Import classic_core P9.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition loop1 : Type := unit.
HB.instance Definition _ := Finite.copy loop1 unit.
HB.instance Definition _ := HasArc.Build loop1 (fun _ _ => true).

Lemma loop1_nb_arcs : 0 < nb_arcs loop1.
Proof. by apply/card_gt0P; exists ((tt, tt) : loop1 * loop1); rewrite inE. Qed.

Lemma TT2_antidirected : antidirected_tree (TT 2).
Proof.
rewrite /antidirected_tree /tree_digraph; apply/andP; split; first (apply/andP; split).
- apply/forallP => u; apply/forallP => v.
  have [->|huv] := eqVneq u v; first exact: connect0.
  by apply: connect1; rewrite !arcTTE -neq_ltn val_eqE.
- rewrite card_TT /nb_arcs.
  apply/cards1P; exists (ord0, ord_max).
  apply/setP => -[a b]; rewrite !inE arcTTE /=.
  by case: a b => [[|[|a]] ha] [[|[|b]] hb].
- apply/forallP => -[[|[|m]] hm] //=.
  + by apply/orP; right; apply/eqP; apply: eq_card0 => u; rewrite !inE arcTTE.
  + apply/orP; left; apply/eqP; apply: eq_card0 => w; rewrite !inE arcTTE /=.
    by case: w => [[|[|w]] hw].
Qed.

Lemma refuted : ~ antidirected_trees_in_digraphs_statement.
Proof.
move=> h.
have [phi [inj _]] := h loop1 2 (leqnn 2) loop1_nb_arcs (TT 2) TT2_antidirected (card_TT 2).
have e : phi ord0 = phi ord_max by case: (phi ord0); case: (phi ord_max).
by move: (inj _ _ e).
Qed.

Print Assumptions refuted.
