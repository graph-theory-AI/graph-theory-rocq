(** Witness hint (Lancelot's lane, item 4b, 2026-10-26): an axiom-free REFUTATION of
    [Digraph.conjectures.packing.linial_berge_statement] as encoded before its loopless guard
    (corpus row opg:linial_berge_path_partition_duality).

    A looped vertex lies in no acyclic set, so on the one-vertex digraph with a loop every
    k-dicolourable induced set S is empty, while at k = 1 every path partition, which must cover the
    vertex, has 1-norm 1.  So the duality equation [pp_knorm k Q = #|S|] fails.  The source's
    digraphs have no loops.  With the guard [loopless D] this file no longer compiles
    (hint-stale-FIX-OK). *)
From HB Require Import structures.
From mathcomp Require Import all_boot.
From Digraph Require Import prelude digraph oriented dipath strong.
From Digraph Require Import classic_core dichromatic packing.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition loop1 : Type := unit.
HB.instance Definition _ := Finite.copy loop1 unit.
HB.instance Definition _ := HasArc.Build loop1 (fun _ _ => true).

Lemma refuted : ~ linial_berge_statement.
Proof.
move=> /(_ loop1 1) [Q [S [hpp hcol hnorm _]]].
have hS : S = set0.
  apply/setP => x; rewrite inE; apply/negP => hx.
  move: hcol => /existsP [col /forallP hacyc].
  pose y : induced_digraph S := exist _ x hx.
  have hy : y \in [set v | col v == col y] by rewrite inE.
  apply: (negP (@loop_not_acyclicb _ (exist _ y hy) _)); [by [] | exact: hacyc].
move: hnorm; rewrite hS cards0 /pp_knorm => /eqP.
rewrite sum_nat_seq_eq0.
move: hpp => /and3P [_ /forallP /(_ tt) /hasP [p hpQ hp] _].
by move/allP/(_ p hpQ); rewrite /pp_vtx /= minnE.
Qed.

Print Assumptions refuted.
