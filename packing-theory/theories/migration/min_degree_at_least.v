(** A11 minimum-degree lower bounds (Packing): the frozen X47 bound and the X47/X48 rows
    (X48 reaches X47's bound across files).  The bound converts to [GTBase.base.min_degree_at_least].
    Baseline, hashes and exact substitutions are recorded in meta/migration_reports/min_degree_at_least.spec.json. *)
From GTBase Require Import base.
From Packing.conjectures Require Import X47 X48.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Legacy.

Definition x47_min_degree_at_least (G : sgraph) (d : nat) : Prop :=
  forall v : G, d <= #|N(v)|.

End Legacy.

Module X47Legacy.

Definition tree_decomposition_delta_edge_connected_statement : Prop :=
  exists f : nat -> nat,
    forall T G : sgraph,
      is_tree [set: T] ->
      0 < #|@x47_edge_set T| ->
      @x47_edge_connected G (f (Delta T)) ->
      @Legacy.x47_min_degree_at_least G (f #|@x47_edge_set T|) ->
      #|@x47_edge_set T| %| #|@x47_edge_set G| ->
      @x47_tree_decomposition_by_copies G T.

End X47Legacy.

Module X48Legacy.

Definition tree_decomposition_leaf_edge_connected_statement : Prop :=
  exists f : nat -> nat,
    forall T G : sgraph,
      is_tree [set: T] ->
      0 < #|@x47_edge_set T| ->
      @x47_edge_connected G (f (x48_leaf_count T)) ->
      @Legacy.x47_min_degree_at_least G (f #|@x47_edge_set T|) ->
      #|@x47_edge_set T| %| #|@x47_edge_set G| ->
      @x47_tree_decomposition_by_copies G T.

End X48Legacy.

Lemma x47_min_degree_at_least_compat (G : sgraph) (d : nat) :
  Legacy.x47_min_degree_at_least G d <->
  x47_min_degree_at_least G d.
Proof. exact: iff_refl. Qed.

Lemma tree_decomposition_delta_edge_connected_statement_compat :
  X47Legacy.tree_decomposition_delta_edge_connected_statement <->
  tree_decomposition_delta_edge_connected_statement.
Proof. exact: iff_refl. Qed.

Lemma tree_decomposition_leaf_edge_connected_statement_compat :
  X48Legacy.tree_decomposition_leaf_edge_connected_statement <->
  tree_decomposition_leaf_edge_connected_statement.
Proof. exact: iff_refl. Qed.
