(** * Chromatic.migration.path_tree — frozen path index graphs of X126 and X189
    (library migration B9)

    Batch B, family [path-tree] (meta/library_primitives/path-tree.json).  [Legacy]
    freezes X126's and X189's [*_path_index_graph] verbatim as they stood at the B9
    baseline e377dcb: the index graph is a tree ([is_tree [set: T]]) of maximum
    degree at most two ([Delta T <= 2]).  The live helpers now unfold to
    [GTBase.path_trees.path_tree T], whose body is that conjunction, so the helper
    certificates are kernel-checked conversions.  [X126Legacy] freezes the
    pathwidth predicate and Dujmovic et al.'s row with B6's live
    [x126_thue_choosable]; [X126Original] composes B6's frozen
    [X126Legacy.thue_choosable] (Chromatic.migration.simple_path, over B6's frozen
    genuine path) with this family's frozen pathwidth, the complete pre-B6, pre-B9
    row.  [X189Legacy] freezes the spaghetti/path decomposition width predicate and
    its row, the documented KNOWN-UNFAITHFUL encoding (blocked leg), kept verbatim
    and not repaired.  Tree-decomposition axioms, bag sizes and the uniform outer
    function are unchanged.  Hashes and substitutions:
    meta/migration_reports/path_tree.md. *)

From GTBase Require Import base path_trees.
From Chromatic.conjectures Require Import X126 X189.
From Chromatic.migration Require simple_path.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Legacy.

Definition x126_path_index_graph (T : sgraph) : Prop :=
  is_tree [set: T] /\ Delta T <= 2.

Definition x189_path_index_graph (T : sgraph) : Prop :=
  is_tree [set: T] /\ Delta T <= 2.

End Legacy.

Module X126Legacy.

Definition pathwidth_at_most (G : sgraph) (k : nat) : Prop :=
  exists (T : sgraph) (bag : T -> {set G}),
    Legacy.x126_path_index_graph T /\
    x126_tree_decomposition bag /\
    forall t : T, #|bag t| <= k.+1.

Definition dujmovic_thue_choice_number_pathwidth_statement : Prop :=
  exists f : nat -> nat,
    forall (p : nat) (G : sgraph),
      pathwidth_at_most G p ->
      x126_thue_choosable G (f p).

End X126Legacy.

Module X126Original.

Definition dujmovic_thue_choice_number_pathwidth_statement : Prop :=
  exists f : nat -> nat,
    forall (p : nat) (G : sgraph),
      X126Legacy.pathwidth_at_most G p ->
      Chromatic.migration.simple_path.X126Legacy.thue_choosable G (f p).

End X126Original.

Module X189Legacy.

Definition spaghetti_path_decompositions_width (G : sgraph) (k : nat) : Prop :=
  exists (T P : sgraph) (tbag : T -> {set G}) (pbag : P -> {set G}),
    x189_spaghetti_tree_decomposition tbag /\
    Legacy.x189_path_index_graph P /\
    x189_tree_decomposition pbag /\
    forall (t : T) (p : P), #|tbag t :&: pbag p| <= k.

Definition spaghetti_tree_path_decomposition_chi_bound_statement : Prop :=
  exists f : nat -> nat,
    forall (k : nat) (G : sgraph),
      1 <= k ->
      spaghetti_path_decompositions_width G k ->
      χ([set: G]) <= f k.

End X189Legacy.

(** ** Certificates *)

Lemma x126_path_index_graph_compat (T : sgraph) :
  Legacy.x126_path_index_graph T <-> x126_path_index_graph T.
Proof. exact: iff_refl. Qed.

Lemma x189_path_index_graph_compat (T : sgraph) :
  Legacy.x189_path_index_graph T <-> x189_path_index_graph T.
Proof. exact: iff_refl. Qed.

Lemma x126_pathwidth_at_most_compat (G : sgraph) (k : nat) :
  X126Legacy.pathwidth_at_most G k <-> x126_pathwidth_at_most G k.
Proof. exact: iff_refl. Qed.

Lemma dujmovic_thue_choice_number_pathwidth_statement_compat :
  X126Legacy.dujmovic_thue_choice_number_pathwidth_statement <->
  dujmovic_thue_choice_number_pathwidth_statement.
Proof. exact: iff_refl. Qed.

(** Before B6 and B9: B6's frozen Thue choosability and this family's frozen pathwidth. *)
Lemma dujmovic_thue_choice_number_pathwidth_statement_original_compat :
  X126Original.dujmovic_thue_choice_number_pathwidth_statement <->
  dujmovic_thue_choice_number_pathwidth_statement.
Proof.
split=> -[f hf]; exists f => p G pw.
- by apply/Chromatic.migration.simple_path.x126_thue_choosable_compat; apply: hf.
- by apply/Chromatic.migration.simple_path.x126_thue_choosable_compat; apply: hf.
Qed.

Lemma x189_spaghetti_path_decompositions_width_compat (G : sgraph) (k : nat) :
  X189Legacy.spaghetti_path_decompositions_width G k <-> x189_spaghetti_path_decompositions_width G k.
Proof. exact: iff_refl. Qed.

Lemma spaghetti_tree_path_decomposition_chi_bound_statement_compat :
  X189Legacy.spaghetti_tree_path_decomposition_chi_bound_statement <->
  spaghetti_tree_path_decomposition_chi_bound_statement.
Proof. exact: iff_refl. Qed.

Print Assumptions x126_path_index_graph_compat.
Print Assumptions x189_path_index_graph_compat.
Print Assumptions x126_pathwidth_at_most_compat.
Print Assumptions dujmovic_thue_choice_number_pathwidth_statement_compat.
Print Assumptions dujmovic_thue_choice_number_pathwidth_statement_original_compat.
Print Assumptions x189_spaghetti_path_decompositions_width_compat.
Print Assumptions spaghetti_tree_path_decomposition_chi_bound_statement_compat.
