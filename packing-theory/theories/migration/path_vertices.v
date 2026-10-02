(** * Packing.migration.path_vertices — frozen path-vertex chain (library migration B1)

    Batch B family [path-vertices] (meta/library_primitives.json): the local
    helper [x26_path_vertices] now unfolds to [GTBase.walks_paths.seq_vertices].

    [X26Legacy] holds verbatim copies, taken at base commit 9e03072, of every
    definition on the affected dependency chain of row
    [bounded_degree_distant_induced_menger_statement]: the helper and each
    definition that reaches it.  Inside the module the copies shadow the live
    names, so the frozen statement never resolves through the migrated helper;
    definitions that do not reach the helper (balls, X-Y paths) are the live,
    unchanged ones.

    [seq_vertices s] is MathComp's [[set:: s]], which unfolds to the frozen
    comprehension [[set v | v \in s]]; so every live definition is convertible
    to its frozen copy and the certificates below are kernel-checked
    conversions ([x26_path_vertices_compat] goes through [seq_verticesE]).
    Source hashes, the per-row theorem table and the [Print All Dependencies]
    check of the frozen closure: meta/migration_reports/path_vertices.md. *)

From GTBase Require Import base walks_paths.
From Packing.conjectures Require Import X26.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module X26Legacy.

Definition x26_path_vertices (G : sgraph) (p : seq G) : {set G} :=
  [set v | v \in p].

Definition x26_pairwise_distant_paths
    (G : sgraph) (d : nat) (paths : seq (seq G)) : Prop :=
  forall p q : seq G,
    p \in paths -> q \in paths -> p != q ->
    [disjoint x26_set_ball (d.-1) (x26_path_vertices p) & x26_path_vertices q].

Definition x26_has_k_distant_xy_paths
    (G : sgraph) (d k : nat) (X Y : {set G}) : Prop :=
  exists paths : seq (seq G),
    size paths = k /\
    uniq paths /\
    (forall p : seq G, p \in paths -> x26_xy_path X Y p) /\
    x26_pairwise_distant_paths d paths.

Definition x26_separates_xy (G : sgraph) (X Y Z : {set G}) : Prop :=
  forall p : seq G,
    x26_xy_path X Y p ->
    [disjoint x26_path_vertices p & Z] ->
    False.

Definition bounded_degree_distant_induced_menger_statement : Prop :=
  forall d Dmax : nat, exists C : nat,
    0 < C /\
    forall (k : nat) (G : sgraph) (X Y : {set G}),
      Delta G <= Dmax ->
      x26_has_k_distant_xy_paths d k X Y \/
      exists Z : {set G},
        #|Z| < C * k /\
        x26_separates_xy X Y Z.

End X26Legacy.

(** ** Certificates *)

Lemma x26_path_vertices_compat (G : sgraph) (p : seq G) :
  X26Legacy.x26_path_vertices p = x26_path_vertices p.
Proof. by rewrite /x26_path_vertices seq_verticesE. Qed.

Lemma x26_pairwise_distant_paths_compat (G : sgraph) (d : nat) (paths : seq (seq G)) :
  X26Legacy.x26_pairwise_distant_paths d paths <-> x26_pairwise_distant_paths d paths.
Proof. exact: iff_refl. Qed.

Lemma x26_has_k_distant_xy_paths_compat (G : sgraph) (d k : nat) (X Y : {set G}) :
  X26Legacy.x26_has_k_distant_xy_paths d k X Y <-> x26_has_k_distant_xy_paths d k X Y.
Proof. exact: iff_refl. Qed.

Lemma x26_separates_xy_compat (G : sgraph) (X Y Z : {set G}) :
  X26Legacy.x26_separates_xy X Y Z <-> x26_separates_xy X Y Z.
Proof. exact: iff_refl. Qed.

Lemma bounded_degree_distant_induced_menger_statement_compat :
  X26Legacy.bounded_degree_distant_induced_menger_statement <->
  bounded_degree_distant_induced_menger_statement.
Proof. exact: iff_refl. Qed.
