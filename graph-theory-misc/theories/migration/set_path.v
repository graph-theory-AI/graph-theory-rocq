(** * GTMisc.migration.set_path — frozen set-to-set path chains (library migration B5)

    Batch B, family [set-path] (meta/library_primitives/set-path.json).  [Legacy]
    freezes the conjecture-local helpers [x39_xy_path] and [x116_ST_path] (the same
    body with the set parameters renamed) verbatim as they stood at fbf33a0, before
    the migration: a nonempty sequence, first entry in the first set, last entry in
    the second, no repetition, consecutive entries adjacent.  The live helpers now
    unfold to [GTBase.walks_paths.seq_set_path], whose body is that same match, so
    every certificate below is a kernel-checked conversion.

    [X39Legacy], [X40Legacy] and [X116Legacy] freeze this family's chains of the
    three rows (k distant paths, the separator, X116's direct use of the path
    predicate in its hitting clause) with the frozen helpers, keeping the live
    vertex-support and pairwise-distance helpers migrated by family path-vertices
    (B1).  B1's snapshots [GTMisc.migration.path_vertices.X39Legacy] and
    [X116Legacy] call the live path predicates; they are kept unchanged.
    [X39Original], [X40Original] and [X116Original] freeze the three rows end to
    end over B1's frozen support/distance bodies and this family's frozen path
    predicates, with [*_original_compat] certificates.  Source hashes, the exact
    substitutions and the per-row theorem names are recorded in
    meta/migration_reports/set_path.md. *)

From GTBase Require Import base.
From GTMisc.conjectures Require Import X39 X40 X116.
From GTMisc.migration Require path_vertices.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Legacy.

Definition x39_xy_path (G : sgraph) (X Y : {set G}) (p : seq G) : Prop :=
  match p with
  | [::] => False
  | x :: q => x \in X /\ last x q \in Y /\ uniq p /\ path (--) x q
  end.

Definition x116_ST_path (G : sgraph) (S T : {set G}) (p : seq G) : Prop :=
  match p with
  | [::] => False
  | x :: q => x \in S /\ last x q \in T /\ uniq p /\ path (--) x q
  end.

End Legacy.

Module X39Legacy.

Definition has_k_distant_xy_paths
    (G : sgraph) (d k : nat) (X Y : {set G}) : Prop :=
  exists paths : seq (seq G),
    size paths = k /\
    uniq paths /\
    (forall p : seq G, p \in paths -> Legacy.x39_xy_path X Y p) /\
    x39_pairwise_distant_paths d paths.

Definition separates_xy
    (G : sgraph) (X Y A : {set G}) : Prop :=
  forall p : seq G,
    Legacy.x39_xy_path X Y p ->
    [disjoint x39_path_vertices p & A] ->
    False.

Definition coarse_menger_ball_separator_statement : Prop :=
  forall k : nat, exists c : nat,
    forall (d : nat) (G : sgraph) (X Y : {set G}),
      has_k_distant_xy_paths d k X Y \/
      exists Z : {set G},
        #|Z| < k /\
        separates_xy X Y (x39_set_ball (c * d) Z).

End X39Legacy.

Module X40Legacy.

Definition coarse_menger_distance_two_separator_statement : Prop :=
  forall k : nat,
    1 <= k ->
    exists ell : nat,
      0 < ell /\
      forall (G : sgraph) (S T : {set G}),
        X39Legacy.has_k_distant_xy_paths 2 k S T \/
        exists X : {set G},
          #|X| <= k - 1 /\
          X39Legacy.separates_xy S T (x39_set_ball ell X).

End X40Legacy.

Module X116Legacy.

Definition has_k_distant_ST_paths
    (G : sgraph) (d k : nat) (S T : {set G}) : Prop :=
  exists paths : seq (seq G),
    size paths = k /\
    uniq paths /\
    (forall p : seq G, p \in paths -> Legacy.x116_ST_path S T p) /\
    x116_pairwise_distant_paths d paths.

Definition coarse_menger_paths_bounded_separator_statement : Prop :=
  forall (k d : nat),
    1 <= k -> 1 <= d ->
    exists l : nat,
      0 < l /\
      forall (G : sgraph) (S T : {set G}),
        has_k_distant_ST_paths d k S T \/
        exists X : {set G},
          #|X| <= k - 1 /\
          forall p : seq G,
            Legacy.x116_ST_path S T p ->
            exists v : G,
              v \in x116_path_vertices p /\ v \in x116_set_ball l X.

End X116Legacy.

Module X39Original.

Definition has_k_distant_xy_paths
    (G : sgraph) (d k : nat) (X Y : {set G}) : Prop :=
  exists paths : seq (seq G),
    size paths = k /\
    uniq paths /\
    (forall p : seq G, p \in paths -> Legacy.x39_xy_path X Y p) /\
    path_vertices.X39Legacy.pairwise_distant_paths d paths.

Definition separates_xy
    (G : sgraph) (X Y A : {set G}) : Prop :=
  forall p : seq G,
    Legacy.x39_xy_path X Y p ->
    [disjoint path_vertices.Legacy.x39_path_vertices p & A] ->
    False.

Definition coarse_menger_ball_separator_statement : Prop :=
  forall k : nat, exists c : nat,
    forall (d : nat) (G : sgraph) (X Y : {set G}),
      has_k_distant_xy_paths d k X Y \/
      exists Z : {set G},
        #|Z| < k /\
        separates_xy X Y (x39_set_ball (c * d) Z).

End X39Original.

Module X40Original.

Definition coarse_menger_distance_two_separator_statement : Prop :=
  forall k : nat,
    1 <= k ->
    exists ell : nat,
      0 < ell /\
      forall (G : sgraph) (S T : {set G}),
        X39Original.has_k_distant_xy_paths 2 k S T \/
        exists X : {set G},
          #|X| <= k - 1 /\
          X39Original.separates_xy S T (x39_set_ball ell X).

End X40Original.

Module X116Original.

Definition has_k_distant_ST_paths
    (G : sgraph) (d k : nat) (S T : {set G}) : Prop :=
  exists paths : seq (seq G),
    size paths = k /\
    uniq paths /\
    (forall p : seq G, p \in paths -> Legacy.x116_ST_path S T p) /\
    path_vertices.X116Legacy.pairwise_distant_paths d paths.

Definition coarse_menger_paths_bounded_separator_statement : Prop :=
  forall (k d : nat),
    1 <= k -> 1 <= d ->
    exists l : nat,
      0 < l /\
      forall (G : sgraph) (S T : {set G}),
        has_k_distant_ST_paths d k S T \/
        exists X : {set G},
          #|X| <= k - 1 /\
          forall p : seq G,
            Legacy.x116_ST_path S T p ->
            exists v : G,
              v \in path_vertices.Legacy.x116_path_vertices p /\ v \in x116_set_ball l X.

End X116Original.

(** ** Certificates *)

Lemma x39_xy_path_compat (G : sgraph) (X Y : {set G}) (p : seq G) :
  Legacy.x39_xy_path X Y p = x39_xy_path X Y p.
Proof. by []. Qed.

Lemma x116_ST_path_compat (G : sgraph) (S T : {set G}) (p : seq G) :
  Legacy.x116_ST_path S T p = x116_ST_path S T p.
Proof. by []. Qed.

Lemma x39_has_k_distant_xy_paths_compat (G : sgraph) (d k : nat) (X Y : {set G}) :
  X39Legacy.has_k_distant_xy_paths d k X Y <-> x39_has_k_distant_xy_paths d k X Y.
Proof. exact: iff_refl. Qed.

Lemma x39_separates_xy_compat (G : sgraph) (X Y A : {set G}) :
  X39Legacy.separates_xy X Y A <-> x39_separates_xy X Y A.
Proof. exact: iff_refl. Qed.

Lemma coarse_menger_ball_separator_statement_compat :
  X39Legacy.coarse_menger_ball_separator_statement <-> coarse_menger_ball_separator_statement.
Proof. exact: iff_refl. Qed.

Lemma coarse_menger_distance_two_separator_statement_compat :
  X40Legacy.coarse_menger_distance_two_separator_statement <->
  coarse_menger_distance_two_separator_statement.
Proof. exact: iff_refl. Qed.

Lemma x116_has_k_distant_ST_paths_compat (G : sgraph) (d k : nat) (S T : {set G}) :
  X116Legacy.has_k_distant_ST_paths d k S T <-> x116_has_k_distant_ST_paths d k S T.
Proof. exact: iff_refl. Qed.

Lemma coarse_menger_paths_bounded_separator_statement_compat :
  X116Legacy.coarse_menger_paths_bounded_separator_statement <->
  coarse_menger_paths_bounded_separator_statement.
Proof. exact: iff_refl. Qed.

Lemma x39_has_k_distant_xy_paths_original_compat (G : sgraph) (d k : nat) (X Y : {set G}) :
  X39Original.has_k_distant_xy_paths d k X Y <-> x39_has_k_distant_xy_paths d k X Y.
Proof. exact: iff_refl. Qed.

Lemma x39_separates_xy_original_compat (G : sgraph) (X Y A : {set G}) :
  X39Original.separates_xy X Y A <-> x39_separates_xy X Y A.
Proof. exact: iff_refl. Qed.

Lemma coarse_menger_ball_separator_statement_original_compat :
  X39Original.coarse_menger_ball_separator_statement <-> coarse_menger_ball_separator_statement.
Proof. exact: iff_refl. Qed.

Lemma coarse_menger_distance_two_separator_statement_original_compat :
  X40Original.coarse_menger_distance_two_separator_statement <->
  coarse_menger_distance_two_separator_statement.
Proof. exact: iff_refl. Qed.

Lemma x116_has_k_distant_ST_paths_original_compat (G : sgraph) (d k : nat) (S T : {set G}) :
  X116Original.has_k_distant_ST_paths d k S T <-> x116_has_k_distant_ST_paths d k S T.
Proof. exact: iff_refl. Qed.

Lemma coarse_menger_paths_bounded_separator_statement_original_compat :
  X116Original.coarse_menger_paths_bounded_separator_statement <->
  coarse_menger_paths_bounded_separator_statement.
Proof. exact: iff_refl. Qed.
