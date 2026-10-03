(** A12 exact minimum degree (extremal): the frozen XE2 attained minimum, row erdos:803 and its complete row.
    Baseline, hashes and exact substitutions are recorded in meta/migration_reports/min_degree.spec.json.
    - [Legacy]: [xe2_min_degree] states the attaining vertex FIRST and the universal bound second; it is
      [GTBase.base.min_degree] up to that conjunct exchange, a proved iff ([min_degree_attained_firstE]), not a
      conversion.  The attaining vertex keeps the empty graph excluded.
    - [XE2Legacy]: the row over this frozen minimum; every other helper stays live there.
    - [XE2Original]: the complete row, composing the frozen minimum with A5's frozen containment and A7's frozen
      raw rank count (aliased, not imported); the bridge rewrites the minimum and reuses A7's certificate. *)
From Corelib Require Import Setoid Morphisms.
From GTBase Require Import base.
From Extremal.conjectures Require Import X4 XE1 XE2.
From Extremal.migration Require subgraph_of edge_count.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Earlier families' certificate modules, aliased without Import: their module names coincide
    with this file's. *)
Module A5 := Extremal.migration.subgraph_of.
Module A7 := Extremal.migration.edge_count.

Module Legacy.

Definition xe2_min_degree (G : sgraph) (d : nat) : Prop :=
  (exists v : G, #|N(v)| = d) /\
  forall v : G, d <= #|N(v)|.

End Legacy.

Module XE2Legacy.

Definition erdos_803_statement : Prop :=
  exists D C : nat,
    forall m : nat, 1 <= m -> exists N : nat,
      forall (n : nat) (G : sgraph),
        N <= n -> #|G| = n -> n * trunc_log 2 n <= x4_edge_count G ->
        exists H : sgraph,
          xe1_subgraph_of H G /\ #|H| = m /\
          (exists d : nat, Legacy.xe2_min_degree H d /\ Delta H <= D * d) /\
          C * x4_edge_count H >= m * trunc_log 2 m.

End XE2Legacy.

Module XE2Original.

Definition erdos_803_statement : Prop :=
  exists D C : nat,
    forall m : nat, 1 <= m -> exists N : nat,
      forall (n : nat) (G : sgraph),
        N <= n -> #|G| = n -> n * trunc_log 2 n <= A7.Legacy.x4_edge_count G ->
        exists H : sgraph,
          A5.Legacy.xe1_subgraph_of H G /\ #|H| = m /\
          (exists d : nat, Legacy.xe2_min_degree H d /\ Delta H <= D * d) /\
          C * A7.Legacy.x4_edge_count H >= m * trunc_log 2 m.

End XE2Original.

(** Not a conversion: the two conjuncts are exchanged. *)
Lemma xe2_min_degree_compat (G : sgraph) (d : nat) :
  Legacy.xe2_min_degree G d <->
  xe2_min_degree G d.
Proof. by rewrite /xe2_min_degree min_degree_attained_firstE. Qed.

Lemma erdos_803_statement_compat :
  XE2Legacy.erdos_803_statement <->
  erdos_803_statement.
Proof.
rewrite /XE2Legacy.erdos_803_statement /erdos_803_statement.
setoid_rewrite xe2_min_degree_compat; reflexivity.
Qed.

Lemma erdos_803_statement_original_compat :
  XE2Original.erdos_803_statement <->
  erdos_803_statement.
Proof.
rewrite /XE2Original.erdos_803_statement; setoid_rewrite xe2_min_degree_compat.
exact: A7.erdos_803_statement_original_compat.
Qed.
