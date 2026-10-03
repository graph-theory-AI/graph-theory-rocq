(** * Packing.migration.set_path — frozen set-to-set path chain (library migration B5)

    Batch B, family [set-path] (meta/library_primitives/set-path.json).  [Legacy]
    freezes the helper [x26_xy_path] verbatim as it stood at fbf33a0, before the
    migration; the live helper now unfolds to [GTBase.walks_paths.seq_set_path],
    whose body is the same match, so the certificates are kernel-checked
    conversions.  [X26Legacy] freezes this family's chain of row
    [bounded_degree_distant_induced_menger_statement] (k distant paths, the
    separator) with the frozen helper, keeping the live helpers migrated by family
    path-vertices (B1).  B1's snapshot [Packing.migration.path_vertices.X26Legacy]
    calls the live [x26_xy_path]; it is kept unchanged.  [X26Original] freezes the
    row end to end over B1's frozen bodies and this family's frozen path predicate.
    Source hashes, the exact substitutions and the per-row theorem names are
    recorded in meta/migration_reports/set_path.md. *)

From GTBase Require Import base.
From Packing.conjectures Require Import X26.
From Packing.migration Require path_vertices.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Legacy.

Definition x26_xy_path (G : sgraph) (X Y : {set G}) (p : seq G) : Prop :=
  match p with
  | [::] => False
  | x :: q => x \in X /\ last x q \in Y /\ uniq p /\ path (--) x q
  end.

End Legacy.

Module X26Legacy.

Definition has_k_distant_xy_paths
    (G : sgraph) (d k : nat) (X Y : {set G}) : Prop :=
  exists paths : seq (seq G),
    size paths = k /\
    uniq paths /\
    (forall p : seq G, p \in paths -> Legacy.x26_xy_path X Y p) /\
    x26_pairwise_distant_paths d paths.

Definition separates_xy (G : sgraph) (X Y Z : {set G}) : Prop :=
  forall p : seq G,
    Legacy.x26_xy_path X Y p ->
    [disjoint x26_path_vertices p & Z] ->
    False.

Definition bounded_degree_distant_induced_menger_statement : Prop :=
  forall d Dmax : nat, exists C : nat,
    0 < C /\
    forall (k : nat) (G : sgraph) (X Y : {set G}),
      Delta G <= Dmax ->
      has_k_distant_xy_paths d k X Y \/
      exists Z : {set G},
        #|Z| < C * k /\
        separates_xy X Y Z.

End X26Legacy.

Module X26Original.

Definition has_k_distant_xy_paths
    (G : sgraph) (d k : nat) (X Y : {set G}) : Prop :=
  exists paths : seq (seq G),
    size paths = k /\
    uniq paths /\
    (forall p : seq G, p \in paths -> Legacy.x26_xy_path X Y p) /\
    path_vertices.X26Legacy.pairwise_distant_paths d paths.

Definition separates_xy (G : sgraph) (X Y Z : {set G}) : Prop :=
  forall p : seq G,
    Legacy.x26_xy_path X Y p ->
    [disjoint path_vertices.Legacy.x26_path_vertices p & Z] ->
    False.

Definition bounded_degree_distant_induced_menger_statement : Prop :=
  forall d Dmax : nat, exists C : nat,
    0 < C /\
    forall (k : nat) (G : sgraph) (X Y : {set G}),
      Delta G <= Dmax ->
      has_k_distant_xy_paths d k X Y \/
      exists Z : {set G},
        #|Z| < C * k /\
        separates_xy X Y Z.

End X26Original.

(** ** Certificates *)

Lemma x26_xy_path_compat (G : sgraph) (X Y : {set G}) (p : seq G) :
  Legacy.x26_xy_path X Y p = x26_xy_path X Y p.
Proof. by []. Qed.

Lemma x26_has_k_distant_xy_paths_compat (G : sgraph) (d k : nat) (X Y : {set G}) :
  X26Legacy.has_k_distant_xy_paths d k X Y <-> x26_has_k_distant_xy_paths d k X Y.
Proof. exact: iff_refl. Qed.

Lemma x26_separates_xy_compat (G : sgraph) (X Y Z : {set G}) :
  X26Legacy.separates_xy X Y Z <-> x26_separates_xy X Y Z.
Proof. exact: iff_refl. Qed.

Lemma bounded_degree_distant_induced_menger_statement_compat :
  X26Legacy.bounded_degree_distant_induced_menger_statement <->
  bounded_degree_distant_induced_menger_statement.
Proof. exact: iff_refl. Qed.

Lemma x26_has_k_distant_xy_paths_original_compat (G : sgraph) (d k : nat) (X Y : {set G}) :
  X26Original.has_k_distant_xy_paths d k X Y <-> x26_has_k_distant_xy_paths d k X Y.
Proof. exact: iff_refl. Qed.

Lemma x26_separates_xy_original_compat (G : sgraph) (X Y Z : {set G}) :
  X26Original.separates_xy X Y Z <-> x26_separates_xy X Y Z.
Proof. exact: iff_refl. Qed.

Lemma bounded_degree_distant_induced_menger_statement_original_compat :
  X26Original.bounded_degree_distant_induced_menger_statement <->
  bounded_degree_distant_induced_menger_statement.
Proof. exact: iff_refl. Qed.
