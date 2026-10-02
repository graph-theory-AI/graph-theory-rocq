(** * Packing.migration.path_vertices — frozen path-vertex chain (library migration B1)

    Batch B, family [path-vertices] (meta/library_primitives.json).  [Legacy]
    freezes the conjecture-local helper [x26_path_vertices] verbatim as it stood at
    9e03072, before the migration; the live helper now unfolds to
    [GTBase.walks_paths.seq_vertices].  [X26Legacy] freezes the affected chain of
    row [bounded_degree_distant_induced_menger_statement], the statement included:
    the copies drop the wave prefix of their names and refer to the frozen helper
    as [Legacy.x26_path_vertices], so no frozen body resolves through a live helper
    of this family.  Definitions that do not reach the helper (balls, X-Y paths)
    are the live, unchanged ones.

    [seq_vertices s] is MathComp's [[set:: s]], which unfolds to the frozen
    comprehension [[set v | v \in s]], so every live definition is convertible to
    its frozen copy: the certificates below are kernel-checked conversions, the
    helper certificate going through [seq_verticesE].  Source hashes, the exact
    substitutions and the per-row theorem names are recorded in
    meta/migration_reports/path_vertices.md. *)

From GTBase Require Import base.
From Packing.conjectures Require Import X26.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Legacy.

Definition x26_path_vertices (G : sgraph) (p : seq G) : {set G} :=
  [set v | v \in p].

End Legacy.

Module X26Legacy.

Definition pairwise_distant_paths
    (G : sgraph) (d : nat) (paths : seq (seq G)) : Prop :=
  forall p q : seq G,
    p \in paths -> q \in paths -> p != q ->
    [disjoint x26_set_ball (d.-1) (Legacy.x26_path_vertices p) & Legacy.x26_path_vertices q].

Definition has_k_distant_xy_paths
    (G : sgraph) (d k : nat) (X Y : {set G}) : Prop :=
  exists paths : seq (seq G),
    size paths = k /\
    uniq paths /\
    (forall p : seq G, p \in paths -> x26_xy_path X Y p) /\
    pairwise_distant_paths d paths.

Definition separates_xy (G : sgraph) (X Y Z : {set G}) : Prop :=
  forall p : seq G,
    x26_xy_path X Y p ->
    [disjoint Legacy.x26_path_vertices p & Z] ->
    False.

Definition statement : Prop :=
  forall d Dmax : nat, exists C : nat,
    0 < C /\
    forall (k : nat) (G : sgraph) (X Y : {set G}),
      Delta G <= Dmax ->
      has_k_distant_xy_paths d k X Y \/
      exists Z : {set G},
        #|Z| < C * k /\
        separates_xy X Y Z.

End X26Legacy.

(** ** Certificates *)

Lemma x26_path_vertices_compat (G : sgraph) (p : seq G) :
  Legacy.x26_path_vertices p = x26_path_vertices p.
Proof. by rewrite /x26_path_vertices seq_verticesE. Qed.

Lemma x26_pairwise_distant_paths_compat (G : sgraph) (d : nat) (paths : seq (seq G)) :
  X26Legacy.pairwise_distant_paths d paths <-> x26_pairwise_distant_paths d paths.
Proof. exact: iff_refl. Qed.

Lemma x26_has_k_distant_xy_paths_compat (G : sgraph) (d k : nat) (X Y : {set G}) :
  X26Legacy.has_k_distant_xy_paths d k X Y <-> x26_has_k_distant_xy_paths d k X Y.
Proof. exact: iff_refl. Qed.

Lemma x26_separates_xy_compat (G : sgraph) (X Y Z : {set G}) :
  X26Legacy.separates_xy X Y Z <-> x26_separates_xy X Y Z.
Proof. exact: iff_refl. Qed.

Lemma bounded_degree_distant_induced_menger_statement_compat :
  X26Legacy.statement <-> bounded_degree_distant_induced_menger_statement.
Proof. exact: iff_refl. Qed.
