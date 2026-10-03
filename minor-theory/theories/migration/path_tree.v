(** * Minor.migration.path_tree — frozen path index graph of X95 (library migration B9)

    Batch B, family [path-tree] (meta/library_primitives/path-tree.json).  [Legacy]
    freezes X95's [x95_path_index_graph] verbatim as it stood at the B9 baseline
    e377dcb: a tree of maximum degree at most two.  The live helper now unfolds to
    [GTBase.path_trees.path_tree T], whose body is that conjunction, so the
    certificates are kernel-checked conversions.  [X95Legacy] freezes the pathwidth
    predicate (over X27's unchanged tree decompositions) and the row, with its
    connectivity hypothesis and its subgraph-indexed tree decomposition unchanged.
    No earlier migration froze this row.  Hashes and substitutions:
    meta/migration_reports/path_tree.md. *)

From GTBase Require Import base path_trees.
From Minor.conjectures Require Import X27 X95.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Legacy.

Definition x95_path_index_graph (T : sgraph) : Prop :=
  is_tree [set: T] /\ Delta T <= 2.

End Legacy.

Module X95Legacy.

Definition pathwidth_at_most (G : sgraph) (k : nat) : Prop :=
  exists (T : sgraph) (bag : T -> {set G}),
    Legacy.x95_path_index_graph T /\
    x27_tree_decomposition bag /\
    forall t : T, #|bag t| <= k.+1.

Definition subgraph_indexed_tree_decomposition_pathwidth_bound_statement : Prop :=
  exists f : nat -> nat,
    forall (p : nat) (G : sgraph),
      connected [set: G] ->
      pathwidth_at_most G p ->
      x95_subgraph_indexed_tree_decomposition_width_at_most G (f p).

End X95Legacy.

(** ** Certificates *)

Lemma x95_path_index_graph_compat (T : sgraph) :
  Legacy.x95_path_index_graph T <-> x95_path_index_graph T.
Proof. exact: iff_refl. Qed.

Lemma x95_pathwidth_at_most_compat (G : sgraph) (k : nat) :
  X95Legacy.pathwidth_at_most G k <-> x95_pathwidth_at_most G k.
Proof. exact: iff_refl. Qed.

Lemma subgraph_indexed_tree_decomposition_pathwidth_bound_statement_compat :
  X95Legacy.subgraph_indexed_tree_decomposition_pathwidth_bound_statement <->
  subgraph_indexed_tree_decomposition_pathwidth_bound_statement.
Proof. exact: iff_refl. Qed.

Print Assumptions x95_path_index_graph_compat.
Print Assumptions x95_pathwidth_at_most_compat.
Print Assumptions subgraph_indexed_tree_decomposition_pathwidth_bound_statement_compat.
