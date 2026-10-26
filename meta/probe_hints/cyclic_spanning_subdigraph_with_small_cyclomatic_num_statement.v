(** Witness hint (Lancelot's lane, item 4b, 2026-10-26): an axiom-free REFUTATION of
    [Digraph.conjectures.P9.cyclic_spanning_subdigraph_with_small_cyclomatic_num_statement] as
    encoded before its loopless guard (corpus row
    opg:cyclic_spanning_subdigraph_with_small_cyclomatic_number).

    On the one-vertex digraph with a loop, the vertex lies on a directed cycle (the loop), its
    singleton is not stable, so [alpha D = 0], and every cyclic arc selector keeps the loop, so the
    cyclomatic number is at least 1 > 0.  The source's digraphs have no loops.  With the guard
    [loopless D] this file no longer compiles (hint-stale-FIX-OK). *)
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

Lemma loop1_alpha : alpha loop1 = 0.
Proof.
apply/eqP; rewrite -leqn0; apply/bigmax_leqP => S hS; rewrite leqn0 cards_eq0.
apply/eqP/setP => -[]; rewrite inE; apply/negP => hin.
by move: hS => /forall_inP /(_ tt hin) /forall_inP /(_ tt hin).
Qed.

Lemma refuted : ~ cyclic_spanning_subdigraph_with_small_cyclomatic_num_statement.
Proof.
move=> /(_ loop1) h.
have hcyc : forall v : loop1, exists c : seq loop1, dicycle c /\ v \in c.
  by case; exists [:: tt]; split; [by [] | exact: mem_head].
have [f [hsel hle]] := h hcyc.
move: hle; rewrite loop1_alpha leqn0 /cyclomatic.
move: hsel => /andP [_ /forallP /(_ tt) /andP [hf _]].
have hw : 0 < nb_wcc f.
  by apply/card_gt0P; exists [set y | connect (wadj f) tt y]; apply/imsetP; exists tt.
have hs : #|f tt| <= \sum_v #|f v| by rewrite (bigD1 tt) //= leq_addr.
rewrite card_unit subn_eq0 => hle.
have h2 := leq_trans (leq_add hf hw) (leq_add hs (leqnn (nb_wcc f))).
by have := leq_trans h2 hle.
Qed.

Print Assumptions refuted.
