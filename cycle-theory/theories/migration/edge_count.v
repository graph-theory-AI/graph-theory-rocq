(** A7 edge counts: the frozen X5 helper and its row. Baseline, hashes and exact substitutions are
    recorded in meta/migration_reports/edge_count.spec.json. *)
From Corelib Require Import Setoid Morphisms.
From GTBase Require Import base.
From Cycle.conjectures Require Import X5.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

#[local] Instance and3_iff_morphism : Proper (iff ==> iff ==> iff ==> iff) and3.
Proof. by move=> a a' ha b b' hb c c' hc; split=> -[x y z]; split; by [apply/ha|apply/hb|apply/hc]. Qed.

#[local] Instance and4_iff_morphism : Proper (iff ==> iff ==> iff ==> iff ==> iff) and4.
Proof.
by move=> a a' ha b b' hb c c' hc d d' hd; split=> -[x y z w]; split;
  by [apply/ha|apply/hb|apply/hc|apply/hd].
Qed.

Module Legacy.

Definition x5_edge_count (G : sgraph) : nat :=
  #|[set p : G * G |
      (p.1 -- p.2) && ((enum_rank p.1) < (enum_rank p.2))%N]|.

End Legacy.

Module X5Legacy.

Definition cycle_with_external_three_neighbours_statement : Prop :=
  forall (n : nat) (G : sgraph),
    2 <= n ->
    #|G| = n ->
    Legacy.x5_edge_count G = 2 * n - 2 ->
    exists (c : seq G) (v : G),
      ucycle (--) c /\
      2 < size c /\
      v \notin c /\
      3 <= #|N(v) :&: x5_vertices_of_seq c|.

End X5Legacy.

Lemma x5_edge_count_compat (G : sgraph) : Legacy.x5_edge_count G = x5_edge_count G.
Proof. exact: GTBase.common.edge_count_rank G. Qed.

Lemma cycle_with_external_three_neighbours_statement_compat :
  X5Legacy.cycle_with_external_three_neighbours_statement <-> cycle_with_external_three_neighbours_statement.
Proof. rewrite /X5Legacy.cycle_with_external_three_neighbours_statement /cycle_with_external_three_neighbours_statement; try setoid_rewrite x5_edge_count_compat; reflexivity. Qed.
