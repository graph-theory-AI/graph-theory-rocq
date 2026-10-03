(** * Minor.migration.path_vertices — frozen path-vertex chains (library migration B1)

    Batch B, family [path-vertices] (meta/library_primitives.json).  [Legacy]
    freezes the conjecture-local helpers [x11_path_vertices] and
    [x67_path_vertices] verbatim as they stood at 9e03072, before the migration;
    the live helpers now unfold to [GTBase.walks_paths.seq_vertices].  [X11Legacy]
    and [X67Legacy] freeze the affected chains of their rows, the statements
    included: the copies drop the wave prefix of their names and refer to the
    frozen helpers as [Legacy.x11_path_vertices] and [Legacy.x67_path_vertices], so
    no frozen body resolves through a live helper of this family.  Definitions
    that do not reach a helper (X-Y paths, anticompleteness, closed neighbourhoods,
    induced paths between two vertices, the X27 treewidth bound) are the live,
    unchanged ones.

    [seq_vertices s] is MathComp's [[set:: s]], which unfolds to the frozen
    comprehensions [[set v | v \in s]] and [[set x : G | x \in s]], so every live
    definition is convertible to its frozen copy: the certificates below are
    kernel-checked conversions, the helper certificates going through
    [seq_verticesE].  Source hashes, the exact substitutions and the per-row
    theorem names are recorded in meta/migration_reports/path_vertices.md. *)

From GraphTheory Require Import minor.
From GTBase Require Import base.
From Minor.conjectures Require Import X27 X11 X67.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Legacy.

Definition x11_path_vertices (G : sgraph) (p : seq G) : {set G} :=
  [set v | v \in p].

Definition x67_path_vertices (G : sgraph) (p : seq G) : {set G} :=
  [set x : G | x \in p].

End Legacy.

Module X11Legacy.

Definition pairwise_anticomplete_paths
    (G : sgraph) (paths : seq (seq G)) : Prop :=
  forall p q : seq G,
    p \in paths -> q \in paths -> p != q ->
    @x11_anticomplete_sets G (Legacy.x11_path_vertices p) (Legacy.x11_path_vertices q).

Definition has_k_anticomplete_xy_paths
    (G : sgraph) (k : nat) (X Y : {set G}) : Prop :=
  exists paths : seq (seq G),
    size paths = k /\
    uniq paths /\
    (forall p : seq G, p \in paths -> @x11_xy_path G X Y p) /\
    @pairwise_anticomplete_paths G paths.

Definition no_xy_path_after_closed_neighbourhood
    (G : sgraph) (X Y Z : {set G}) : Prop :=
  forall p : seq G,
    @x11_xy_path G X Y p ->
    [disjoint Legacy.x11_path_vertices p & x11_closed_neighbourhood Z] ->
    False.

Definition statement : Prop :=
  forall (k : nat) (G : sgraph) (X Y : {set G}),
    @has_k_anticomplete_xy_paths G k X Y \/
    exists Z : {set G},
      #|Z| <= k.-1 /\
      @no_xy_path_after_closed_neighbourhood G X Y Z.

End X11Legacy.

Module X67Legacy.

Definition internal_vertices (G : sgraph) (a b : G) (p : seq G) : {set G} :=
  Legacy.x67_path_vertices p :\: [set a; b].

Definition no_cross_edges
    (G : sgraph) (a b : G) (p q : seq G) : Prop :=
  forall u v : G,
    u \in internal_vertices a b p ->
    v \in internal_vertices a b q ->
    ~~ (u -- v).

Definition theta (G : sgraph) : Prop :=
  exists (a b : G) (p1 p2 p3 : seq G),
    a != b /\
    x67_induced_path_between a b p1 /\
    x67_induced_path_between a b p2 /\
    x67_induced_path_between a b p3 /\
    [disjoint internal_vertices a b p1 & internal_vertices a b p2] /\
    [disjoint internal_vertices a b p1 & internal_vertices a b p3] /\
    [disjoint internal_vertices a b p2 & internal_vertices a b p3] /\
    no_cross_edges a b p1 p2 /\
    no_cross_edges a b p1 p3 /\
    no_cross_edges a b p2 p3.

Definition statement : Prop :=
  exists f : nat -> nat,
    forall (t : nat) (G : sgraph),
      4 <= t ->
      Delta G <= t ->
      triangle_free G ->
      ~ theta G ->
      x27_treewidth_at_most G (f t).

End X67Legacy.

(** ** Certificates: X11 *)

Lemma x11_path_vertices_compat (G : sgraph) (p : seq G) :
  Legacy.x11_path_vertices p = x11_path_vertices p.
Proof. by rewrite /x11_path_vertices seq_verticesE. Qed.

Lemma x11_pairwise_anticomplete_paths_compat (G : sgraph) (paths : seq (seq G)) :
  X11Legacy.pairwise_anticomplete_paths paths <-> x11_pairwise_anticomplete_paths paths.
Proof. exact: iff_refl. Qed.

Lemma x11_has_k_anticomplete_xy_paths_compat (G : sgraph) (k : nat) (X Y : {set G}) :
  X11Legacy.has_k_anticomplete_xy_paths k X Y <-> x11_has_k_anticomplete_xy_paths k X Y.
Proof. exact: iff_refl. Qed.

Lemma x11_no_xy_path_after_closed_neighbourhood_compat (G : sgraph) (X Y Z : {set G}) :
  X11Legacy.no_xy_path_after_closed_neighbourhood X Y Z <->
  x11_no_xy_path_after_closed_neighbourhood X Y Z.
Proof. exact: iff_refl. Qed.

Lemma induced_menger_anticomplete_paths_statement_compat :
  X11Legacy.statement <-> induced_menger_anticomplete_paths_statement.
Proof. exact: iff_refl. Qed.

(** ** Certificates: X67 *)

Lemma x67_path_vertices_compat (G : sgraph) (p : seq G) :
  Legacy.x67_path_vertices p = x67_path_vertices p.
Proof. by rewrite /x67_path_vertices seq_verticesE. Qed.

Lemma x67_internal_vertices_compat (G : sgraph) (a b : G) (p : seq G) :
  X67Legacy.internal_vertices a b p = x67_internal_vertices a b p.
Proof.
by rewrite /X67Legacy.internal_vertices /x67_internal_vertices x67_path_vertices_compat.
Qed.

Lemma x67_no_cross_edges_compat (G : sgraph) (a b : G) (p q : seq G) :
  X67Legacy.no_cross_edges a b p q <-> x67_no_cross_edges a b p q.
Proof. exact: iff_refl. Qed.

Lemma x67_theta_compat (G : sgraph) : X67Legacy.theta G <-> x67_theta G.
Proof. exact: iff_refl. Qed.

Lemma theta_triangle_free_bounded_degree_treewidth_statement_compat :
  X67Legacy.statement <-> theta_triangle_free_bounded_degree_treewidth_statement.
Proof. exact: iff_refl. Qed.
