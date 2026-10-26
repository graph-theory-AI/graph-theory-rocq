(** Witness hint (Lancelot's lane, item 4b, 2026-10-26): an axiom-free REFUTATION of
    [Digraph.conjectures.classic_core.splitting_min_outdegree_statement] as encoded before its
    non-emptiness guard (corpus row opg:splitting_a_digraph_with_minimum_outdegree_constraints).

    The empty digraph meets the out-degree hypothesis vacuously, for every f and d, but it has no
    vertex set that is both non-empty and proper, which the body's conclusion demands.  So the old
    body is false for every f.  The source splits the vertex set of a digraph into two non-empty
    parts, so its digraphs have vertices.  With the guard [0 < #|D|] this file no longer compiles
    (hint-stale-FIX-OK). *)
From HB Require Import structures.
From mathcomp Require Import all_boot.
From Digraph Require Import prelude digraph oriented.
From Digraph Require Import classic_core.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition empty0 : Type := 'I_0.
HB.instance Definition _ := Finite.on empty0.
HB.instance Definition _ := HasArc.Build empty0 (fun _ _ => false).

Lemma refuted : ~ splitting_min_outdegree_statement.
Proof.
move=> [f h].
have hyp : forall v : empty0, (f 0 <= outdeg v)%N by move=> v; case: v => m hm; exfalso; by rewrite ltn0 in hm.
have [V1 [h1 _ _ _]] := h empty0 0 hyp.
by move/negP: h1; apply; apply/eqP/setP => v; exfalso; exact: (elimF idP (ltn0 v) (ltn_ord v)).
Qed.

Print Assumptions refuted.
