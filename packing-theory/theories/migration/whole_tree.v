(** * Packing.migration.whole_tree — frozen whole-graph tree wrapper and row of Packing XE1
    (library migration B20)

    Family [whole-tree] (meta/library_primitives/whole-tree.json).  [Legacy] freezes, verbatim as it
    stood at the B20 baseline 6de6ce3, Packing XE1's [xe1_tree] ([is_forest [set: T] /\ connected [set: T]]),
    definitionally the upstream [GraphTheory.core.sgraph.is_tree [set: T]] that the live wrapper now
    unfolds to; the certificate is a conversion.  [XE1Legacy] freezes the complete row #743 over the
    frozen tree: 2 <= n, the dependent family [T : 'I_n -> sgraph] of trees of orders val k + 1, and the
    dependent injective embeddings with pairwise disjoint edge images covering every pair of ['K_n]
    (the live packing predicate).  No earlier migration snapshot exists for this row.  Hashes and
    substitutions: meta/migration_reports/whole_tree.md. *)

From GTBase Require Import base.
From Packing.conjectures Require Import XE1.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Legacy.

Definition xe1_tree (T : sgraph) : Prop :=
  is_forest [set: T] /\ connected [set: T].

End Legacy.

Module XE1Legacy.

Definition erdos_743_statement : Prop :=
  forall n : nat, 2 <= n ->
    forall T : forall k : 'I_n, sgraph,
      (forall k : 'I_n, #|T k| = (val k).+1 /\ Legacy.xe1_tree (T k)) ->
      exists emb : forall k : 'I_n, T k -> 'I_n,
        @xe1_edge_disjoint_tree_packing n T emb.

End XE1Legacy.

(** ** Certificates *)

(** The helper: the upstream [is_tree] at the whole carrier, by conversion. *)
Lemma xe1_tree_compat (T : sgraph) : Legacy.xe1_tree T <-> xe1_tree T.
Proof. exact: iff_refl. Qed.

(** erdos:743 (unchanged): the complete row over the frozen tree, by conversion. *)
Lemma erdos_743_statement_compat : XE1Legacy.erdos_743_statement <-> erdos_743_statement.
Proof. exact: iff_refl. Qed.

Print Assumptions xe1_tree_compat.
Print Assumptions erdos_743_statement_compat.
