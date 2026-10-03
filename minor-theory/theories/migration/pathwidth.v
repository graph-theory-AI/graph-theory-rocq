(** C14: exact supplied-index pathwidth contract and whole-row transport.
    Immediate snapshots freeze cdb9e10161e6566b9a812b0931488acb6338be9f. Complete Originals reuse
    the unchanged C13 bodies, already closed over B9/C13 and (X126) B6.
    No source witness, bound, guard or quantifier is changed. *)
From GTBase Require Import base pathwidth.
From Minor.conjectures Require Import X27 X95.
Require Minor.migration.bag_decompositions.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Legacy.
Definition x95_pathwidth_at_most (G : sgraph) (k : nat) : Prop := exists (T : sgraph) (bag : T -> {set G}), x95_path_index_graph T /\ x27_tree_decomposition bag /\ forall t : T, #|bag t| <= k.+1.

Definition subgraph_indexed_tree_decomposition_pathwidth_bound_statement : Prop := exists f : nat -> nat, forall (p : nat) (G : sgraph), connected [set: G] -> Legacy.x95_pathwidth_at_most G p -> x95_subgraph_indexed_tree_decomposition_width_at_most G (f p).
End Legacy.

Lemma x95_pathwidth_at_most_compat (G : sgraph) (k : nat) :
  Legacy.x95_pathwidth_at_most G k <-> x95_pathwidth_at_most G k.
Proof. exact: iff_refl. Qed.

Lemma subgraph_indexed_tree_decomposition_pathwidth_bound_statement_compat :
  Legacy.subgraph_indexed_tree_decomposition_pathwidth_bound_statement <-> subgraph_indexed_tree_decomposition_pathwidth_bound_statement.
Proof. exact: iff_refl. Qed.

(** The full original statement is reused verbatim; this bridge includes C14. *)
Lemma subgraph_indexed_tree_decomposition_pathwidth_bound_statement_original_compat :
  Minor.migration.bag_decompositions.X95Original.subgraph_indexed_tree_decomposition_pathwidth_bound_statement <-> subgraph_indexed_tree_decomposition_pathwidth_bound_statement.
Proof. exact: Minor.migration.bag_decompositions.subgraph_indexed_tree_decomposition_pathwidth_bound_statement_original_compat. Qed.
