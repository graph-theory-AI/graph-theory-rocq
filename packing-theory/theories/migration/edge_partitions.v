(** * C3: indexed edge partitions, with the existing M1/C1/C2 history

    The source body is [matching.X15Legacy.edge_partition], over the frozen
    pre-M1 [matching.Legacy.x15_edge_set]. C1 already froze all three affected
    statements, including their original matching and perfect-matching chains.
    C2 preserved those bodies and adapted the perfect-matching proof. C3 keeps
    every frozen body and statement theorem unchanged, adapts C1's partition
    bridge, and exposes these per-family entry points without duplicate copies.

    Spec and compact report: meta/migration_reports/edge_partition.spec.json
    and edge_partition.md. The public contract and grounding are in
    Packing.foundations.edge_partitions. No statement guards or statuses change. *)

From GTBase Require Import base.
From Packing.conjectures Require Import X15 X18.
From Packing.migration Require matching.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma x15_edge_partition_compat
    (G : sgraph) (m : nat) (E : 'I_m -> {set {set G}}) :
  Packing.migration.matching.X15Legacy.edge_partition E <-> x15_edge_partition E.
Proof. exact: Packing.migration.matching.x15_edge_partition_compat. Qed.

Lemma fair_matching_edge_partition_statement_compat :
  Packing.migration.matching.X15Legacy.fair_matching_edge_partition_statement <->
  fair_matching_edge_partition_statement.
Proof. exact: Packing.migration.matching.fair_matching_edge_partition_statement_compat. Qed.

Lemma knn_fair_perfect_matching_statement_compat :
  Packing.migration.matching.X18Legacy.knn_fair_perfect_matching_statement <->
  knn_fair_perfect_matching_statement.
Proof. exact: Packing.migration.matching.knn_fair_perfect_matching_statement_compat. Qed.

Lemma brualdi_stein_partial_transversal_statement_compat :
  Packing.migration.matching.X18Legacy.brualdi_stein_partial_transversal_statement <->
  brualdi_stein_partial_transversal_statement.
Proof. exact: Packing.migration.matching.brualdi_stein_partial_transversal_statement_compat. Qed.

Print Assumptions x15_edge_partition_compat.
Print Assumptions fair_matching_edge_partition_statement_compat.
Print Assumptions knn_fair_perfect_matching_statement_compat.
Print Assumptions brualdi_stein_partial_transversal_statement_compat.
