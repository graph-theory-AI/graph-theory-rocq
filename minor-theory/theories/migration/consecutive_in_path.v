(** * Minor.migration.consecutive_in_path — frozen consecutive-entry chain (library migration B3)

    Batch B, family [consecutive-in-path]
    (meta/library_primitives/consecutive-in-path.json).  [Legacy] freezes the
    conjecture-local helper [x67_consecutive_in_path] verbatim as it stood at
    787a996, before the migration; the live helper now unfolds to
    [GTBase.walks_paths.seq_consecutive p u v], whose body is the same
    disjunction, so the certificates below are kernel-checked conversions.

    [X67Legacy] freezes the affected chain of row
    [theta_triangle_free_bounded_degree_treewidth_statement]:
    [induced_path_between], [theta] and the statement, with the wave prefix
    dropped and the frozen helper referred to as [Legacy.x67_consecutive_in_path].
    Definitions that do not reach the helper are the live ones, in particular
    [x67_internal_vertices] and [x67_no_cross_edges], migrated by families
    path-vertices (B1) and internal-vertices (B2).

    B1's snapshot [Minor.migration.path_vertices.X67Legacy.theta] froze the
    path-vertex chain and calls the live [x67_induced_path_between], which now
    reaches [seq_consecutive]; its body, and the statement and certificates of
    families B1 and B2 built on it, are kept unchanged.  [X67Original] freezes
    the pre-migration theta and statement end to end, over the frozen chains of
    B1 and of this family, and the [*_original_compat] certificates relate them
    to the live definitions.  Source hashes, the exact substitutions and the
    per-row theorem names are recorded in
    meta/migration_reports/consecutive_in_path.md. *)

From GTBase Require Import base.
From Minor.conjectures Require Import X27 X67.
From Minor.migration Require path_vertices.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Legacy.

Definition x67_consecutive_in_path (G : sgraph) (p : seq G) (u v : G) : Prop :=
  (u, v) \in zip p (behead p) \/ (v, u) \in zip p (behead p).

End Legacy.

Module X67Legacy.

Definition induced_path_between (G : sgraph) (a b : G) (p : seq G) : Prop :=
  match p with
  | [::] => False
  | x :: q =>
      x = a /\
      last x q = b /\
      3 <= size p /\
      uniq p /\
      path (--) x q /\
      forall u v : G,
        u \in p -> v \in p -> u -- v -> u != v ->
        Legacy.x67_consecutive_in_path p u v
  end.

Definition theta (G : sgraph) : Prop :=
  exists (a b : G) (p1 p2 p3 : seq G),
    a != b /\
    induced_path_between a b p1 /\
    induced_path_between a b p2 /\
    induced_path_between a b p3 /\
    [disjoint x67_internal_vertices a b p1 & x67_internal_vertices a b p2] /\
    [disjoint x67_internal_vertices a b p1 & x67_internal_vertices a b p3] /\
    [disjoint x67_internal_vertices a b p2 & x67_internal_vertices a b p3] /\
    x67_no_cross_edges a b p1 p2 /\
    x67_no_cross_edges a b p1 p3 /\
    x67_no_cross_edges a b p2 p3.

Definition statement : Prop :=
  exists f : nat -> nat,
    forall (t : nat) (G : sgraph),
      4 <= t ->
      Delta G <= t ->
      triangle_free G ->
      ~ theta G ->
      x27_treewidth_at_most G (f t).

End X67Legacy.

(** The X67 theta and statement before the B1, B2 and B3 migrations: the induced
    paths of this family and the internal-vertex chain frozen by family B1. *)
Module X67Original.

Definition theta (G : sgraph) : Prop :=
  exists (a b : G) (p1 p2 p3 : seq G),
    a != b /\
    X67Legacy.induced_path_between a b p1 /\
    X67Legacy.induced_path_between a b p2 /\
    X67Legacy.induced_path_between a b p3 /\
    [disjoint path_vertices.X67Legacy.internal_vertices a b p1
     & path_vertices.X67Legacy.internal_vertices a b p2] /\
    [disjoint path_vertices.X67Legacy.internal_vertices a b p1
     & path_vertices.X67Legacy.internal_vertices a b p3] /\
    [disjoint path_vertices.X67Legacy.internal_vertices a b p2
     & path_vertices.X67Legacy.internal_vertices a b p3] /\
    path_vertices.X67Legacy.no_cross_edges a b p1 p2 /\
    path_vertices.X67Legacy.no_cross_edges a b p1 p3 /\
    path_vertices.X67Legacy.no_cross_edges a b p2 p3.

Definition statement : Prop :=
  exists f : nat -> nat,
    forall (t : nat) (G : sgraph),
      4 <= t ->
      Delta G <= t ->
      triangle_free G ->
      ~ theta G ->
      x27_treewidth_at_most G (f t).

End X67Original.

(** ** Certificates *)

Lemma x67_consecutive_in_path_compat (G : sgraph) (p : seq G) (u v : G) :
  Legacy.x67_consecutive_in_path p u v = x67_consecutive_in_path p u v.
Proof. by []. Qed.

Lemma x67_induced_path_between_compat (G : sgraph) (a b : G) (p : seq G) :
  X67Legacy.induced_path_between a b p <-> x67_induced_path_between a b p.
Proof. exact: iff_refl. Qed.

Lemma x67_theta_compat (G : sgraph) : X67Legacy.theta G <-> x67_theta G.
Proof. exact: iff_refl. Qed.

Lemma theta_triangle_free_bounded_degree_treewidth_statement_compat :
  X67Legacy.statement <-> theta_triangle_free_bounded_degree_treewidth_statement.
Proof. exact: iff_refl. Qed.

Lemma x67_theta_original_compat (G : sgraph) : X67Original.theta G <-> x67_theta G.
Proof. exact: iff_refl. Qed.

Lemma theta_triangle_free_bounded_degree_treewidth_statement_original_compat :
  X67Original.statement <-> theta_triangle_free_bounded_degree_treewidth_statement.
Proof. exact: iff_refl. Qed.
