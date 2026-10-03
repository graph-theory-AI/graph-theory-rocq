(** C14: exact supplied-index pathwidth contract and whole-row transport.
    Immediate snapshots freeze cdb9e10161e6566b9a812b0931488acb6338be9f. Complete Originals reuse
    the unchanged C13 bodies, already closed over B9/C13 and (X126) B6.
    No source witness, bound, guard or quantifier is changed. *)
From GTBase Require Import base pathwidth.
From Chromatic.conjectures Require Import X126.
Require Chromatic.migration.bag_decompositions.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Legacy.
Definition x126_pathwidth_at_most (G : sgraph) (k : nat) : Prop := exists (T : sgraph) (bag : T -> {set G}), x126_path_index_graph T /\ x126_tree_decomposition bag /\ forall t : T, #|bag t| <= k.+1.

Definition dujmovic_thue_choice_number_pathwidth_statement : Prop := exists f : nat -> nat, forall (p : nat) (G : sgraph), Legacy.x126_pathwidth_at_most G p -> x126_thue_choosable G (f p).
End Legacy.

Lemma x126_pathwidth_at_most_compat (G : sgraph) (k : nat) :
  Legacy.x126_pathwidth_at_most G k <-> x126_pathwidth_at_most G k.
Proof. exact: iff_refl. Qed.

Lemma dujmovic_thue_choice_number_pathwidth_statement_compat :
  Legacy.dujmovic_thue_choice_number_pathwidth_statement <-> dujmovic_thue_choice_number_pathwidth_statement.
Proof. exact: iff_refl. Qed.

(** The full original statement is reused verbatim; this bridge includes C14. *)
Lemma dujmovic_thue_choice_number_pathwidth_statement_original_compat :
  Chromatic.migration.bag_decompositions.X126Original.dujmovic_thue_choice_number_pathwidth_statement <-> dujmovic_thue_choice_number_pathwidth_statement.
Proof. exact: Chromatic.migration.bag_decompositions.dujmovic_thue_choice_number_pathwidth_statement_original_compat. Qed.
