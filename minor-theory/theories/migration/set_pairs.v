(** A21 set pairs (minor): X11's frozen disjoint anticomplete sets, its pairwise and has-k chains, the induced Menger
    row, and the complete B1+B5+A21 row.  Baseline, hashes and exact substitutions are recorded in
    meta/migration_reports/set_pairs.spec.json.
    - [Legacy]: X11's [[disjoint A & B] /\ (forall cross pairs, ~~ (x -- y))] is equivalent to
      [GTBase.set_pairs.anticomplete A B] by [anticomplete_nonadjP] (an iff, not a conversion).
    - [X11Legacy]: exactly k distinct paths, each a nonempty simple X-Y path, pairwise disjoint and anticomplete, OR a
      set Z with [#|Z| <= k.-1] whose closed neighbourhood every X-Y path meets; X/Y overlap, singleton paths, k = 0 and
      the truncated predecessor are verbatim.  B1's path support and B5's X-Y path stay live in these per-row copies.
    - [X11Original] (texts at the pre-migration 9e03072): the pairwise chain over B1's frozen path support and the
      frozen pair, the has-k chain over B5's frozen X-Y path, and the row with B5's complete frozen right alternative.
      B5's older [X11Original] still reaches the live pair through B1's pairwise chain and is kept unchanged beside this
      one.
      B1's and B5's modules are aliased, not imported; the bridges reuse their certificates. *)
From Corelib Require Import Setoid Morphisms.
From GTBase Require Import base set_pairs.
From Minor.conjectures Require Import X11.
From Minor.migration Require path_vertices set_path.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** B1's and B5's certificate modules, aliased without Import: their module names coincide with this file's. *)
Module B1 := Minor.migration.path_vertices.
Module B5 := Minor.migration.set_path.

Module Legacy.

Definition x11_anticomplete_sets (G : sgraph) (A B : {set G}) : Prop :=
  [disjoint A & B] /\
  forall x y : G, x \in A -> y \in B -> ~~ (x -- y).

End Legacy.

Module X11Legacy.

Definition x11_pairwise_anticomplete_paths
    (G : sgraph) (paths : seq (seq G)) : Prop :=
  forall p q : seq G,
    p \in paths -> q \in paths -> p != q ->
    @Legacy.x11_anticomplete_sets G (x11_path_vertices p) (x11_path_vertices q).

Definition x11_has_k_anticomplete_xy_paths
    (G : sgraph) (k : nat) (X Y : {set G}) : Prop :=
  exists paths : seq (seq G),
    size paths = k /\
    uniq paths /\
    (forall p : seq G, p \in paths -> @x11_xy_path G X Y p) /\
    @X11Legacy.x11_pairwise_anticomplete_paths G paths.

Definition induced_menger_anticomplete_paths_statement : Prop :=
  forall (k : nat) (G : sgraph) (X Y : {set G}),
    @X11Legacy.x11_has_k_anticomplete_xy_paths G k X Y \/
    exists Z : {set G},
      #|Z| <= k.-1 /\
      @x11_no_xy_path_after_closed_neighbourhood G X Y Z.

End X11Legacy.

Module X11Original.

Definition x11_pairwise_anticomplete_paths
    (G : sgraph) (paths : seq (seq G)) : Prop :=
  forall p q : seq G,
    p \in paths -> q \in paths -> p != q ->
    @Legacy.x11_anticomplete_sets G (B1.Legacy.x11_path_vertices p) (B1.Legacy.x11_path_vertices q).

Definition x11_has_k_anticomplete_xy_paths
    (G : sgraph) (k : nat) (X Y : {set G}) : Prop :=
  exists paths : seq (seq G),
    size paths = k /\
    uniq paths /\
    (forall p : seq G, p \in paths -> @B5.Legacy.x11_xy_path G X Y p) /\
    @X11Original.x11_pairwise_anticomplete_paths G paths.

Definition induced_menger_anticomplete_paths_statement : Prop :=
  forall (k : nat) (G : sgraph) (X Y : {set G}),
    @X11Original.x11_has_k_anticomplete_xy_paths G k X Y \/
    exists Z : {set G},
      #|Z| <= k.-1 /\
      @B5.X11Original.no_xy_path_after_closed_neighbourhood G X Y Z.

End X11Original.

(** Not a conversion: the raw conjunction against the Boolean pair, by reflection. *)
Lemma x11_anticomplete_sets_compat (G : sgraph) (A B : {set G}) :
  Legacy.x11_anticomplete_sets A B <-> x11_anticomplete_sets A B.
Proof.
exact: (rwP (anticomplete_nonadjP A B)).
Qed.

Lemma x11_pairwise_anticomplete_paths_compat (G : sgraph) (paths : seq (seq G)) :
  X11Legacy.x11_pairwise_anticomplete_paths paths <-> x11_pairwise_anticomplete_paths paths.
Proof.
rewrite /X11Legacy.x11_pairwise_anticomplete_paths /x11_pairwise_anticomplete_paths.
setoid_rewrite x11_anticomplete_sets_compat.
reflexivity.
Qed.

Lemma x11_has_k_anticomplete_xy_paths_compat (G : sgraph) (k : nat) (X Y : {set G}) :
  X11Legacy.x11_has_k_anticomplete_xy_paths k X Y <-> x11_has_k_anticomplete_xy_paths k X Y.
Proof.
rewrite /X11Legacy.x11_has_k_anticomplete_xy_paths /x11_has_k_anticomplete_xy_paths.
setoid_rewrite x11_pairwise_anticomplete_paths_compat.
reflexivity.
Qed.

Lemma induced_menger_anticomplete_paths_statement_compat :
  X11Legacy.induced_menger_anticomplete_paths_statement <->
  induced_menger_anticomplete_paths_statement.
Proof.
rewrite /X11Legacy.induced_menger_anticomplete_paths_statement /induced_menger_anticomplete_paths_statement.
setoid_rewrite x11_has_k_anticomplete_xy_paths_compat.
reflexivity.
Qed.

(** Complete X11: the frozen pair is rewritten against B1's pairwise chain, then B1's and B5's certificates; B5's
    complete right alternative is reused through its own certificate. *)
Lemma x11_pairwise_anticomplete_paths_original_compat (G : sgraph) (paths : seq (seq G)) :
  X11Original.x11_pairwise_anticomplete_paths paths <-> x11_pairwise_anticomplete_paths paths.
Proof.
rewrite /X11Original.x11_pairwise_anticomplete_paths.
setoid_rewrite x11_anticomplete_sets_compat.
exact: B1.x11_pairwise_anticomplete_paths_compat paths.
Qed.

Lemma x11_has_k_anticomplete_xy_paths_original_compat (G : sgraph) (k : nat) (X Y : {set G}) :
  X11Original.x11_has_k_anticomplete_xy_paths k X Y <-> x11_has_k_anticomplete_xy_paths k X Y.
Proof.
rewrite /X11Original.x11_has_k_anticomplete_xy_paths.
setoid_rewrite x11_pairwise_anticomplete_paths_original_compat.
exact: B5.x11_has_k_anticomplete_xy_paths_compat k X Y.
Qed.

Lemma induced_menger_anticomplete_paths_statement_original_compat :
  X11Original.induced_menger_anticomplete_paths_statement <->
  induced_menger_anticomplete_paths_statement.
Proof.
rewrite /X11Original.induced_menger_anticomplete_paths_statement /induced_menger_anticomplete_paths_statement.
setoid_rewrite x11_has_k_anticomplete_xy_paths_original_compat.
setoid_rewrite B5.x11_no_xy_path_after_closed_neighbourhood_original_compat.
reflexivity.
Qed.
