(** * Chromatic.migration.bag_decompositions -- frozen bag decompositions (C13, 2026-10-03)

    Family: "tree_decomposition" (meta/library_primitives/tree-decomposition.json);
    chromatic rows of X126 and X189.  Canonical primitive:
    [GTBase.bag_decompositions.bag_decomposition], the raw supplied-index
    three-clause contract; public client base/theories/examples/bag_decompositions.v;
    generated report meta/migration_reports/tree_decomposition.md (from
    tree_decomposition.spec.json); record meta/LIBRARY_MIGRATION_C13.md.

    ** Frozen sources

    [Legacy] freezes verbatim, as they stood at 58d6d60, the migrated helpers
    [x126_tree_decomposition] (Boolean existential witnesses) and
    [x189_tree_decomposition] (Prop witnesses).  The live names are now
    aliases of [bag_decomposition]: X126's certificate is a conversion, X189's
    goes through [bag_decompositionP] (an equivalence, not a conversion).

    ** Frozen chains and rows (A1 convention)

    [X126Legacy] freezes [x126_pathwidth_at_most] (prefix dropped) over the
    frozen helper and the row; [x126_path_index_graph] and
    [x126_thue_choosable] are the live aliases of B9 and B6 and stay live in
    this immediate snapshot.  [X189Legacy] freezes the spaghetti chain
    ([spaghetti_tree_decomposition] with its explicit [exists root : T] and its
    documented defective reachability clause, [spaghetti_path_decompositions_width]
    with the pairwise bag intersections [<= k]) and the row, which stays
    BLOCKED; [x189_path_index_graph] (B9) stays live here.

    ** Complete Originals

    [X126Original] composes B6's frozen Thue choosability
    (Chromatic.migration.simple_path.X126Legacy.thue_choosable), B9's frozen
    path index (Chromatic.migration.path_tree.Legacy.x126_path_index_graph)
    and this family's frozen decomposition: the row before B6, B9 and C13.
    [X189Original] composes B9's frozen path index with this family's frozen
    chain: the row before B9 and C13.  B9's own [path_tree.X126Legacy],
    [path_tree.X126Original] and [path_tree.X189Legacy] still read the live
    decomposition helpers and are kept unchanged as documented partial
    snapshots.  No statement body, status, guard or documented defect changes.

    Axiom-free: no Axiom/Parameter/Admitted; Print Assumptions at the end. *)

From GTBase Require Import base path_trees bag_decompositions.
From Chromatic.conjectures Require Import X126 X189.
From Chromatic.migration Require simple_path path_tree.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Legacy.

(** X126.v lines 53-57 at 58d6d60, verbatim. *)
Definition x126_tree_decomposition
    (G T : sgraph) (bag : T -> {set G}) : Prop :=
  (forall v : G, [exists t : T, v \in bag t]) /\
  (forall x y : G, x -- y -> [exists t : T, (x \in bag t) && (y \in bag t)]) /\
  forall v : G, connected [set t : T | v \in bag t].

(** X189.v lines 12-16 at 58d6d60, verbatim. *)
Definition x189_tree_decomposition
    (G T : sgraph) (bag : T -> {set G}) : Prop :=
  (forall v : G, exists t : T, v \in bag t) /\
  (forall x y : G, x -- y -> exists t : T, x \in bag t /\ y \in bag t) /\
  (forall v : G, connected [set t : T | v \in bag t]).

End Legacy.

(** ** Helper certificates *)

Lemma x126_tree_decomposition_compat (G T : sgraph) (bag : T -> {set G}) :
  Legacy.x126_tree_decomposition bag <-> x126_tree_decomposition bag.
Proof. exact: iff_refl. Qed.

Lemma x189_tree_decomposition_compat (G T : sgraph) (bag : T -> {set G}) :
  Legacy.x189_tree_decomposition bag <-> x189_tree_decomposition bag.
Proof.
rewrite /Legacy.x189_tree_decomposition /x189_tree_decomposition.
exact: iff_sym (bag_decompositionP bag).
Qed.

(** ** X126 *)

Module X126Legacy.

(** X126.v lines 62-66 at 58d6d60 with [x126_pathwidth_at_most] ->
    [pathwidth_at_most] and [x126_tree_decomposition] ->
    [Legacy.x126_tree_decomposition]. *)
Definition pathwidth_at_most (G : sgraph) (k : nat) : Prop :=
  exists (T : sgraph) (bag : T -> {set G}),
    x126_path_index_graph T /\
    Legacy.x126_tree_decomposition bag /\
    forall t : T, #|bag t| <= k.+1.

(** X126.v lines 92-96 at 58d6d60 with [x126_pathwidth_at_most] ->
    [pathwidth_at_most]. *)
Definition dujmovic_thue_choice_number_pathwidth_statement : Prop :=
  exists f : nat -> nat,
    forall (p : nat) (G : sgraph),
      pathwidth_at_most G p ->
      x126_thue_choosable G (f p).

End X126Legacy.

Lemma x126_pathwidth_at_most_compat (G : sgraph) (k : nat) :
  X126Legacy.pathwidth_at_most G k <-> x126_pathwidth_at_most G k.
Proof. exact: iff_refl. Qed.

(** studies:std_dujmovi_et_al_question_thue_choice_number_bounde (open, unchanged). *)
Lemma dujmovic_thue_choice_number_pathwidth_statement_compat :
  X126Legacy.dujmovic_thue_choice_number_pathwidth_statement <->
  dujmovic_thue_choice_number_pathwidth_statement.
Proof. exact: iff_refl. Qed.

(** Before B6, B9 and C13. *)
Module X126Original.

(** [x126_pathwidth_at_most] with B9's frozen path index and this family's
    frozen decomposition. *)
Definition pathwidth_at_most (G : sgraph) (k : nat) : Prop :=
  exists (T : sgraph) (bag : T -> {set G}),
    Chromatic.migration.path_tree.Legacy.x126_path_index_graph T /\
    Legacy.x126_tree_decomposition bag /\
    forall t : T, #|bag t| <= k.+1.

Definition dujmovic_thue_choice_number_pathwidth_statement : Prop :=
  exists f : nat -> nat,
    forall (p : nat) (G : sgraph),
      pathwidth_at_most G p ->
      Chromatic.migration.simple_path.X126Legacy.thue_choosable G (f p).

End X126Original.

Lemma x126_pathwidth_at_most_original_compat (G : sgraph) (k : nat) :
  X126Original.pathwidth_at_most G k <-> x126_pathwidth_at_most G k.
Proof. exact: iff_refl. Qed.

Lemma dujmovic_thue_choice_number_pathwidth_statement_original_compat :
  X126Original.dujmovic_thue_choice_number_pathwidth_statement <->
  dujmovic_thue_choice_number_pathwidth_statement.
Proof.
split=> -[f hf]; exists f => p G pw.
- by apply/Chromatic.migration.simple_path.x126_thue_choosable_compat; apply: hf.
- by apply/Chromatic.migration.simple_path.x126_thue_choosable_compat; apply: hf.
Qed.

(** ** X189 *)

Module X189Legacy.

(** X189.v lines 26-31 at 58d6d60 with [x189_spaghetti_tree_decomposition] ->
    [spaghetti_tree_decomposition] and [x189_tree_decomposition] ->
    [Legacy.x189_tree_decomposition]; the explicit root witness and the
    documented reachability clause are unchanged. *)
Definition spaghetti_tree_decomposition
    (G T : sgraph) (bag : T -> {set G}) : Prop :=
  exists root : T,
    is_tree [set: T] /\
    Legacy.x189_tree_decomposition bag /\
    forall v : G, connected [set t : T | v \in bag t] /\
      (forall t : T, t \in [set u : T | v \in bag u] -> connect (--) root t).

(** X189.v lines 34-39 at 58d6d60 with [x189_spaghetti_path_decompositions_width]
    -> [spaghetti_path_decompositions_width], [x189_spaghetti_tree_decomposition]
    -> [spaghetti_tree_decomposition] and [x189_tree_decomposition] ->
    [Legacy.x189_tree_decomposition]. *)
Definition spaghetti_path_decompositions_width (G : sgraph) (k : nat) : Prop :=
  exists (T P : sgraph) (tbag : T -> {set G}) (pbag : P -> {set G}),
    spaghetti_tree_decomposition tbag /\
    x189_path_index_graph P /\
    Legacy.x189_tree_decomposition pbag /\
    forall (t : T) (p : P), #|tbag t :&: pbag p| <= k.

(** X189.v lines 63-67 at 58d6d60 with [x189_spaghetti_path_decompositions_width]
    -> [spaghetti_path_decompositions_width]. *)
Definition spaghetti_tree_path_decomposition_chi_bound_statement : Prop :=
  exists f : nat -> nat,
    forall (k : nat) (G : sgraph),
      1 <= k ->
      spaghetti_path_decompositions_width G k ->
      χ([set: G]) <= f k.

End X189Legacy.

Lemma x189_spaghetti_tree_decomposition_compat (G T : sgraph) (bag : T -> {set G}) :
  X189Legacy.spaghetti_tree_decomposition bag <-> x189_spaghetti_tree_decomposition bag.
Proof.
rewrite /X189Legacy.spaghetti_tree_decomposition /x189_spaghetti_tree_decomposition.
by split=> -[root [tr [dec fib]]]; exists root; split=> //; split=> //;
  apply/x189_tree_decomposition_compat.
Qed.

Lemma x189_spaghetti_path_decompositions_width_compat (G : sgraph) (k : nat) :
  X189Legacy.spaghetti_path_decompositions_width G k <->
  x189_spaghetti_path_decompositions_width G k.
Proof.
split=> -[T [P [tbag [pbag [sp [pi [dec bnd]]]]]]]; exists T, P, tbag, pbag;
  split; try exact/x189_spaghetti_tree_decomposition_compat; split=> //; split=> //;
  exact/x189_tree_decomposition_compat.
Qed.

(** arxiv:1703.07871#00 (open, statement leg BLOCKED, unchanged). *)
Lemma spaghetti_tree_path_decomposition_chi_bound_statement_compat :
  X189Legacy.spaghetti_tree_path_decomposition_chi_bound_statement <->
  spaghetti_tree_path_decomposition_chi_bound_statement.
Proof.
split=> -[f hf]; exists f => k G k1 w; apply: (hf k G k1).
- exact/x189_spaghetti_path_decompositions_width_compat.
- exact/x189_spaghetti_path_decompositions_width_compat.
Qed.

(** Before B9 and C13. *)
Module X189Original.

Definition spaghetti_path_decompositions_width (G : sgraph) (k : nat) : Prop :=
  exists (T P : sgraph) (tbag : T -> {set G}) (pbag : P -> {set G}),
    X189Legacy.spaghetti_tree_decomposition tbag /\
    Chromatic.migration.path_tree.Legacy.x189_path_index_graph P /\
    Legacy.x189_tree_decomposition pbag /\
    forall (t : T) (p : P), #|tbag t :&: pbag p| <= k.

Definition spaghetti_tree_path_decomposition_chi_bound_statement : Prop :=
  exists f : nat -> nat,
    forall (k : nat) (G : sgraph),
      1 <= k ->
      spaghetti_path_decompositions_width G k ->
      χ([set: G]) <= f k.

End X189Original.

Lemma x189_spaghetti_path_decompositions_width_original_compat (G : sgraph) (k : nat) :
  X189Original.spaghetti_path_decompositions_width G k <->
  x189_spaghetti_path_decompositions_width G k.
Proof.
split=> -[T [P [tbag [pbag [sp [pi [dec bnd]]]]]]]; exists T, P, tbag, pbag;
  split; try exact/x189_spaghetti_tree_decomposition_compat; split; try exact: pi;
  split=> //; exact/x189_tree_decomposition_compat.
Qed.

Lemma spaghetti_tree_path_decomposition_chi_bound_statement_original_compat :
  X189Original.spaghetti_tree_path_decomposition_chi_bound_statement <->
  spaghetti_tree_path_decomposition_chi_bound_statement.
Proof.
split=> -[f hf]; exists f => k G k1 w; apply: (hf k G k1).
- exact/x189_spaghetti_path_decompositions_width_original_compat.
- exact/x189_spaghetti_path_decompositions_width_original_compat.
Qed.

Print Assumptions x126_tree_decomposition_compat.
Print Assumptions x189_tree_decomposition_compat.
Print Assumptions x126_pathwidth_at_most_compat.
Print Assumptions dujmovic_thue_choice_number_pathwidth_statement_compat.
Print Assumptions dujmovic_thue_choice_number_pathwidth_statement_original_compat.
Print Assumptions x189_spaghetti_tree_decomposition_compat.
Print Assumptions x189_spaghetti_path_decompositions_width_compat.
Print Assumptions spaghetti_tree_path_decomposition_chi_bound_statement_compat.
Print Assumptions spaghetti_tree_path_decomposition_chi_bound_statement_original_compat.
