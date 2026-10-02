(** * Minor.migration.path_vertices — frozen path-vertex chains (library migration B1)

    Batch B family [path-vertices] (meta/library_primitives.json): the local
    helpers [x11_path_vertices] and [x67_path_vertices] now unfold to
    [GTBase.walks_paths.seq_vertices].

    Each [XnnLegacy] module holds verbatim copies, taken at base commit
    9e03072, of every definition on the affected dependency chain of the row
    of its file: the helper and each definition that reaches it.  Inside a
    module the copies shadow the live names, so no frozen statement resolves
    through a migrated helper; definitions that do not reach a helper (X-Y
    paths, anticompleteness, closed neighbourhoods, induced paths between two
    vertices, the X27 treewidth bound) are the live, unchanged ones.

    [seq_vertices s] is MathComp's [[set:: s]], which unfolds to the frozen
    comprehensions [[set v | v \in s]] and [[set x : G | x \in s]]; so every
    live definition is convertible to its frozen copy and the certificates
    below are kernel-checked conversions (the helper certificates go through
    [seq_verticesE]).  Source hashes, the per-row theorem table and the
    [Print All Dependencies] check of the frozen closures:
    meta/migration_reports/path_vertices.md. *)

From GraphTheory Require Import minor.
From GTBase Require Import base walks_paths.
From Minor.conjectures Require Import X27 X11 X67.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module X11Legacy.

Definition x11_path_vertices (G : sgraph) (p : seq G) : {set G} :=
  [set v | v \in p].

Definition x11_pairwise_anticomplete_paths
    (G : sgraph) (paths : seq (seq G)) : Prop :=
  forall p q : seq G,
    p \in paths -> q \in paths -> p != q ->
    @x11_anticomplete_sets G (x11_path_vertices p) (x11_path_vertices q).

Definition x11_has_k_anticomplete_xy_paths
    (G : sgraph) (k : nat) (X Y : {set G}) : Prop :=
  exists paths : seq (seq G),
    size paths = k /\
    uniq paths /\
    (forall p : seq G, p \in paths -> @x11_xy_path G X Y p) /\
    @x11_pairwise_anticomplete_paths G paths.

Definition x11_no_xy_path_after_closed_neighbourhood
    (G : sgraph) (X Y Z : {set G}) : Prop :=
  forall p : seq G,
    @x11_xy_path G X Y p ->
    [disjoint x11_path_vertices p & x11_closed_neighbourhood Z] ->
    False.

Definition induced_menger_anticomplete_paths_statement : Prop :=
  forall (k : nat) (G : sgraph) (X Y : {set G}),
    @x11_has_k_anticomplete_xy_paths G k X Y \/
    exists Z : {set G},
      #|Z| <= k.-1 /\
      @x11_no_xy_path_after_closed_neighbourhood G X Y Z.

End X11Legacy.

Module X67Legacy.

Definition x67_path_vertices (G : sgraph) (p : seq G) : {set G} :=
  [set x : G | x \in p].

Definition x67_internal_vertices (G : sgraph) (a b : G) (p : seq G) : {set G} :=
  x67_path_vertices p :\: [set a; b].

Definition x67_no_cross_edges
    (G : sgraph) (a b : G) (p q : seq G) : Prop :=
  forall u v : G,
    u \in x67_internal_vertices a b p ->
    v \in x67_internal_vertices a b q ->
    ~~ (u -- v).

Definition x67_theta (G : sgraph) : Prop :=
  exists (a b : G) (p1 p2 p3 : seq G),
    a != b /\
    x67_induced_path_between a b p1 /\
    x67_induced_path_between a b p2 /\
    x67_induced_path_between a b p3 /\
    [disjoint x67_internal_vertices a b p1 & x67_internal_vertices a b p2] /\
    [disjoint x67_internal_vertices a b p1 & x67_internal_vertices a b p3] /\
    [disjoint x67_internal_vertices a b p2 & x67_internal_vertices a b p3] /\
    x67_no_cross_edges a b p1 p2 /\
    x67_no_cross_edges a b p1 p3 /\
    x67_no_cross_edges a b p2 p3.

Definition theta_triangle_free_bounded_degree_treewidth_statement : Prop :=
  exists f : nat -> nat,
    forall (t : nat) (G : sgraph),
      4 <= t ->
      Delta G <= t ->
      triangle_free G ->
      ~ x67_theta G ->
      x27_treewidth_at_most G (f t).

End X67Legacy.

(** ** Certificates: X11 *)

Lemma x11_path_vertices_compat (G : sgraph) (p : seq G) :
  X11Legacy.x11_path_vertices p = x11_path_vertices p.
Proof. by rewrite /x11_path_vertices seq_verticesE. Qed.

Lemma x11_pairwise_anticomplete_paths_compat (G : sgraph) (paths : seq (seq G)) :
  X11Legacy.x11_pairwise_anticomplete_paths paths <-> x11_pairwise_anticomplete_paths paths.
Proof. exact: iff_refl. Qed.

Lemma x11_has_k_anticomplete_xy_paths_compat (G : sgraph) (k : nat) (X Y : {set G}) :
  X11Legacy.x11_has_k_anticomplete_xy_paths k X Y <-> x11_has_k_anticomplete_xy_paths k X Y.
Proof. exact: iff_refl. Qed.

Lemma x11_no_xy_path_after_closed_neighbourhood_compat (G : sgraph) (X Y Z : {set G}) :
  X11Legacy.x11_no_xy_path_after_closed_neighbourhood X Y Z <->
  x11_no_xy_path_after_closed_neighbourhood X Y Z.
Proof. exact: iff_refl. Qed.

Lemma induced_menger_anticomplete_paths_statement_compat :
  X11Legacy.induced_menger_anticomplete_paths_statement <->
  induced_menger_anticomplete_paths_statement.
Proof. exact: iff_refl. Qed.

(** ** Certificates: X67 *)

Lemma x67_path_vertices_compat (G : sgraph) (p : seq G) :
  X67Legacy.x67_path_vertices p = x67_path_vertices p.
Proof. by rewrite /x67_path_vertices seq_verticesE. Qed.

Lemma x67_internal_vertices_compat (G : sgraph) (a b : G) (p : seq G) :
  X67Legacy.x67_internal_vertices a b p = x67_internal_vertices a b p.
Proof.
by rewrite /X67Legacy.x67_internal_vertices /x67_internal_vertices x67_path_vertices_compat.
Qed.

Lemma x67_no_cross_edges_compat (G : sgraph) (a b : G) (p q : seq G) :
  X67Legacy.x67_no_cross_edges a b p q <-> x67_no_cross_edges a b p q.
Proof. exact: iff_refl. Qed.

Lemma x67_theta_compat (G : sgraph) : X67Legacy.x67_theta G <-> x67_theta G.
Proof. exact: iff_refl. Qed.

Lemma theta_triangle_free_bounded_degree_treewidth_statement_compat :
  X67Legacy.theta_triangle_free_bounded_degree_treewidth_statement <->
  theta_triangle_free_bounded_degree_treewidth_statement.
Proof. exact: iff_refl. Qed.
