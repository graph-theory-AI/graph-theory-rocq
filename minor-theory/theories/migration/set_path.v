(** * Minor.migration.set_path — frozen set-to-set path chain (library migration B5)

    Batch B, family [set-path] (meta/library_primitives/set-path.json).  [Legacy]
    freezes the helper [x11_xy_path] verbatim as it stood at fbf33a0, before the
    migration; the live helper now unfolds to [GTBase.walks_paths.seq_set_path],
    whose body is the same match, so the certificates are kernel-checked
    conversions.  [X11Legacy] freezes this family's chain of row
    [induced_menger_anticomplete_paths_statement] (k anticomplete paths, the
    closed-neighbourhood separator, natural predecessor [k.-1]) with the frozen
    helper, keeping the live helpers migrated by family path-vertices (B1).  B1's
    snapshot [Minor.migration.path_vertices.X11Legacy] calls the live
    [x11_xy_path]; it is kept unchanged.  [X11Original] freezes the row end to end
    over B1's frozen bodies and this family's frozen path predicate.  Source hashes,
    the exact substitutions and the per-row theorem names are recorded in
    meta/migration_reports/set_path.md. *)

From GTBase Require Import base.
From Minor.conjectures Require Import X11.
From Minor.migration Require path_vertices.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Legacy.

Definition x11_xy_path (G : sgraph) (X Y : {set G}) (p : seq G) : Prop :=
  match p with
  | [::] => False
  | x :: q =>
      x \in X /\ last x q \in Y /\ uniq p /\ path (--) x q
  end.

End Legacy.

Module X11Legacy.

Definition has_k_anticomplete_xy_paths
    (G : sgraph) (k : nat) (X Y : {set G}) : Prop :=
  exists paths : seq (seq G),
    size paths = k /\
    uniq paths /\
    (forall p : seq G, p \in paths -> @Legacy.x11_xy_path G X Y p) /\
    @x11_pairwise_anticomplete_paths G paths.

Definition no_xy_path_after_closed_neighbourhood
    (G : sgraph) (X Y Z : {set G}) : Prop :=
  forall p : seq G,
    @Legacy.x11_xy_path G X Y p ->
    [disjoint x11_path_vertices p & x11_closed_neighbourhood Z] ->
    False.

Definition induced_menger_anticomplete_paths_statement : Prop :=
  forall (k : nat) (G : sgraph) (X Y : {set G}),
    @has_k_anticomplete_xy_paths G k X Y \/
    exists Z : {set G},
      #|Z| <= k.-1 /\
      @no_xy_path_after_closed_neighbourhood G X Y Z.

End X11Legacy.

Module X11Original.

Definition has_k_anticomplete_xy_paths
    (G : sgraph) (k : nat) (X Y : {set G}) : Prop :=
  exists paths : seq (seq G),
    size paths = k /\
    uniq paths /\
    (forall p : seq G, p \in paths -> @Legacy.x11_xy_path G X Y p) /\
    @path_vertices.X11Legacy.pairwise_anticomplete_paths G paths.

Definition no_xy_path_after_closed_neighbourhood
    (G : sgraph) (X Y Z : {set G}) : Prop :=
  forall p : seq G,
    @Legacy.x11_xy_path G X Y p ->
    [disjoint path_vertices.Legacy.x11_path_vertices p & x11_closed_neighbourhood Z] ->
    False.

Definition induced_menger_anticomplete_paths_statement : Prop :=
  forall (k : nat) (G : sgraph) (X Y : {set G}),
    @has_k_anticomplete_xy_paths G k X Y \/
    exists Z : {set G},
      #|Z| <= k.-1 /\
      @no_xy_path_after_closed_neighbourhood G X Y Z.

End X11Original.

(** ** Certificates *)

Lemma x11_xy_path_compat (G : sgraph) (X Y : {set G}) (p : seq G) :
  @Legacy.x11_xy_path G X Y p = @x11_xy_path G X Y p.
Proof. by []. Qed.

Lemma x11_has_k_anticomplete_xy_paths_compat (G : sgraph) (k : nat) (X Y : {set G}) :
  @X11Legacy.has_k_anticomplete_xy_paths G k X Y <-> @x11_has_k_anticomplete_xy_paths G k X Y.
Proof. exact: iff_refl. Qed.

Lemma x11_no_xy_path_after_closed_neighbourhood_compat (G : sgraph) (X Y Z : {set G}) :
  @X11Legacy.no_xy_path_after_closed_neighbourhood G X Y Z <->
  @x11_no_xy_path_after_closed_neighbourhood G X Y Z.
Proof. exact: iff_refl. Qed.

Lemma induced_menger_anticomplete_paths_statement_compat :
  X11Legacy.induced_menger_anticomplete_paths_statement <->
  induced_menger_anticomplete_paths_statement.
Proof. exact: iff_refl. Qed.

Lemma x11_has_k_anticomplete_xy_paths_original_compat (G : sgraph) (k : nat) (X Y : {set G}) :
  @X11Original.has_k_anticomplete_xy_paths G k X Y <-> @x11_has_k_anticomplete_xy_paths G k X Y.
Proof. exact: iff_refl. Qed.

Lemma x11_no_xy_path_after_closed_neighbourhood_original_compat (G : sgraph) (X Y Z : {set G}) :
  @X11Original.no_xy_path_after_closed_neighbourhood G X Y Z <->
  @x11_no_xy_path_after_closed_neighbourhood G X Y Z.
Proof. exact: iff_refl. Qed.

Lemma induced_menger_anticomplete_paths_statement_original_compat :
  X11Original.induced_menger_anticomplete_paths_statement <->
  induced_menger_anticomplete_paths_statement.
Proof. exact: iff_refl. Qed.
