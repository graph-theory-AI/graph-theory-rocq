(** * GTMisc.migration.path_vertices — frozen path-vertex chains (library migration B1)

    Batch B family [path-vertices] (meta/library_primitives.json): the local
    helpers [x39_path_vertices], [x113_path_vertices], [x116_path_vertices]
    and [x146_path_vertices] now unfold to [GTBase.walks_paths.seq_vertices].

    Each [XnnLegacy] module holds verbatim copies, taken at base commit
    9e03072, of every definition on the affected dependency chain of the rows
    of its file: the helper and each definition that reaches it.  Row X40
    reaches [x39_path_vertices] through the X39 vocabulary, so [X40Legacy]
    imports [X39Legacy].  Inside a module the copies shadow the live names, so
    no frozen statement resolves through a migrated helper; definitions that
    do not reach a helper (balls, X-Y/S-T/A-path predicates) are the live,
    unchanged ones.

    [seq_vertices s] is MathComp's [[set:: s]], which unfolds to the frozen
    comprehension [[set v | v \in s]]; so every live definition is convertible
    to its frozen copy and the certificates below are kernel-checked
    conversions (the helper certificates go through [seq_verticesE]).
    Source hashes, the per-row theorem table and the [Print All Dependencies]
    check of the frozen closures: meta/migration_reports/path_vertices.md. *)

From GTBase Require Import base walks_paths.
From GTMisc.conjectures Require Import X39 X40 X113 X116 X146.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module X39Legacy.

Definition x39_path_vertices (G : sgraph) (p : seq G) : {set G} :=
  [set v | v \in p].

Definition x39_pairwise_distant_paths
    (G : sgraph) (d : nat) (paths : seq (seq G)) : Prop :=
  forall p q : seq G,
    p \in paths -> q \in paths -> p != q ->
    [disjoint x39_path_vertices p & x39_path_vertices q] /\
    [disjoint x39_set_ball (d.-1) (x39_path_vertices p) & x39_path_vertices q].

Definition x39_has_k_distant_xy_paths
    (G : sgraph) (d k : nat) (X Y : {set G}) : Prop :=
  exists paths : seq (seq G),
    size paths = k /\
    uniq paths /\
    (forall p : seq G, p \in paths -> x39_xy_path X Y p) /\
    x39_pairwise_distant_paths d paths.

Definition x39_separates_xy
    (G : sgraph) (X Y A : {set G}) : Prop :=
  forall p : seq G,
    x39_xy_path X Y p ->
    [disjoint x39_path_vertices p & A] ->
    False.

Definition coarse_menger_ball_separator_statement : Prop :=
  forall k : nat, exists c : nat,
    forall (d : nat) (G : sgraph) (X Y : {set G}),
      x39_has_k_distant_xy_paths d k X Y \/
      exists Z : {set G},
        #|Z| < k /\
        x39_separates_xy X Y (x39_set_ball (c * d) Z).

End X39Legacy.

Module X40Legacy.
Import X39Legacy.

Definition coarse_menger_distance_two_separator_statement : Prop :=
  forall k : nat,
    1 <= k ->
    exists ell : nat,
      0 < ell /\
      forall (G : sgraph) (S T : {set G}),
        x39_has_k_distant_xy_paths 2 k S T \/
        exists X : {set G},
          #|X| <= k - 1 /\
          x39_separates_xy S T (x39_set_ball ell X).

End X40Legacy.

Module X113Legacy.

Definition x113_path_vertices (G : sgraph) (p : seq G) : {set G} :=
  [set v | v \in p].

Definition x113_pairwise_distant_cycles
    (G : sgraph) (d : nat) (cs : seq (seq G)) : Prop :=
  forall p q : seq G,
    p \in cs -> q \in cs -> p != q ->
    [disjoint x113_set_ball d (x113_path_vertices p) & x113_path_vertices q].

Definition x113_has_k_distant_cycles
    (G : sgraph) (d k : nat) : Prop :=
  exists cs : seq (seq G),
    size cs = k /\
    uniq cs /\
    (forall c : seq G, c \in cs -> x113_is_cycle c) /\
    x113_pairwise_distant_cycles d cs.

Definition x113_is_forest_after
    (G : sgraph) (A : {set G}) : Prop :=
  forall c : seq G,
    x113_is_cycle c ->
    [disjoint x113_path_vertices c & A] ->
    False.

Definition coarse_erdos_posa_cycles_forest_statement : Prop :=
  exists f g : nat -> nat,
    forall (k d : nat) (G : sgraph),
      1 <= k -> 1 <= d ->
      x113_has_k_distant_cycles G d k \/
      exists X : {set G},
        #|X| <= f k /\
        x113_is_forest_after (x113_set_ball (g d) X).

End X113Legacy.

Module X116Legacy.

Definition x116_path_vertices (G : sgraph) (p : seq G) : {set G} :=
  [set v | v \in p].

Definition x116_pairwise_distant_paths
    (G : sgraph) (d : nat) (paths : seq (seq G)) : Prop :=
  forall p q : seq G,
    p \in paths -> q \in paths -> p != q ->
    [disjoint x116_path_vertices p & x116_path_vertices q] /\
    [disjoint x116_set_ball (d.-1) (x116_path_vertices p) & x116_path_vertices q].

Definition x116_has_k_distant_ST_paths
    (G : sgraph) (d k : nat) (S T : {set G}) : Prop :=
  exists paths : seq (seq G),
    size paths = k /\
    uniq paths /\
    (forall p : seq G, p \in paths -> x116_ST_path S T p) /\
    x116_pairwise_distant_paths d paths.

Definition coarse_menger_paths_bounded_separator_statement : Prop :=
  forall (k d : nat),
    1 <= k -> 1 <= d ->
    exists l : nat,
      0 < l /\
      forall (G : sgraph) (S T : {set G}),
        x116_has_k_distant_ST_paths d k S T \/
        exists X : {set G},
          #|X| <= k - 1 /\
          forall p : seq G,
            x116_ST_path S T p ->
            exists v : G,
              v \in x116_path_vertices p /\ v \in x116_set_ball l X.

End X116Legacy.

Module X146Legacy.

Definition x146_path_vertices (G : sgraph) (p : seq G) : {set G} :=
  [set v | v \in p].

Definition x146_pairwise_distant_A_paths
    (G : sgraph) (d : nat) (paths : seq (seq G)) : Prop :=
  forall p q : seq G,
    p \in paths -> q \in paths -> p != q ->
    [disjoint x146_path_vertices p & x146_path_vertices q] /\
    [disjoint x146_set_ball (d.-1) (x146_path_vertices p) & x146_path_vertices q].

Definition x146_has_k_distant_A_paths
    (G : sgraph) (A : {set G}) (d k : nat) : Prop :=
  exists paths : seq (seq G),
    size paths = k /\
    uniq paths /\
    (forall p : seq G, p \in paths -> x146_A_path A p) /\
    x146_pairwise_distant_A_paths d paths.

Definition x146_every_A_path_hits_ball
    (G : sgraph) (A Z : {set G}) (r : nat) : Prop :=
  forall p : seq G,
    x146_A_path A p ->
    exists v : G,
      v \in x146_path_vertices p /\ v \in x146_set_ball r Z.

Definition geelen_coarse_gallai_A_paths_statement : Prop :=
  exists f g : nat -> nat,
    forall (k d : nat) (G : sgraph) (A : {set G}),
      1 <= k ->
      1 <= d ->
      x146_has_k_distant_A_paths A d k \/
      exists Z : {set G},
        #|Z| <= f k /\
        x146_every_A_path_hits_ball A Z (g d).

End X146Legacy.

(** ** Certificates: X39 *)

Lemma x39_path_vertices_compat (G : sgraph) (p : seq G) :
  X39Legacy.x39_path_vertices p = x39_path_vertices p.
Proof. by rewrite /x39_path_vertices seq_verticesE. Qed.

Lemma x39_pairwise_distant_paths_compat (G : sgraph) (d : nat) (paths : seq (seq G)) :
  X39Legacy.x39_pairwise_distant_paths d paths <-> x39_pairwise_distant_paths d paths.
Proof. exact: iff_refl. Qed.

Lemma x39_has_k_distant_xy_paths_compat (G : sgraph) (d k : nat) (X Y : {set G}) :
  X39Legacy.x39_has_k_distant_xy_paths d k X Y <-> x39_has_k_distant_xy_paths d k X Y.
Proof. exact: iff_refl. Qed.

Lemma x39_separates_xy_compat (G : sgraph) (X Y A : {set G}) :
  X39Legacy.x39_separates_xy X Y A <-> x39_separates_xy X Y A.
Proof. exact: iff_refl. Qed.

Lemma coarse_menger_ball_separator_statement_compat :
  X39Legacy.coarse_menger_ball_separator_statement <->
  coarse_menger_ball_separator_statement.
Proof. exact: iff_refl. Qed.

(** ** Certificates: X40 (through the X39 vocabulary) *)

Lemma coarse_menger_distance_two_separator_statement_compat :
  X40Legacy.coarse_menger_distance_two_separator_statement <->
  coarse_menger_distance_two_separator_statement.
Proof. exact: iff_refl. Qed.

(** ** Certificates: X113 *)

Lemma x113_path_vertices_compat (G : sgraph) (p : seq G) :
  X113Legacy.x113_path_vertices p = x113_path_vertices p.
Proof. by rewrite /x113_path_vertices seq_verticesE. Qed.

Lemma x113_pairwise_distant_cycles_compat (G : sgraph) (d : nat) (cs : seq (seq G)) :
  X113Legacy.x113_pairwise_distant_cycles d cs <-> x113_pairwise_distant_cycles d cs.
Proof. exact: iff_refl. Qed.

Lemma x113_has_k_distant_cycles_compat (G : sgraph) (d k : nat) :
  X113Legacy.x113_has_k_distant_cycles G d k <-> x113_has_k_distant_cycles G d k.
Proof. exact: iff_refl. Qed.

Lemma x113_is_forest_after_compat (G : sgraph) (A : {set G}) :
  X113Legacy.x113_is_forest_after A <-> x113_is_forest_after A.
Proof. exact: iff_refl. Qed.

Lemma coarse_erdos_posa_cycles_forest_statement_compat :
  X113Legacy.coarse_erdos_posa_cycles_forest_statement <->
  coarse_erdos_posa_cycles_forest_statement.
Proof. exact: iff_refl. Qed.

(** ** Certificates: X116 *)

Lemma x116_path_vertices_compat (G : sgraph) (p : seq G) :
  X116Legacy.x116_path_vertices p = x116_path_vertices p.
Proof. by rewrite /x116_path_vertices seq_verticesE. Qed.

Lemma x116_pairwise_distant_paths_compat (G : sgraph) (d : nat) (paths : seq (seq G)) :
  X116Legacy.x116_pairwise_distant_paths d paths <-> x116_pairwise_distant_paths d paths.
Proof. exact: iff_refl. Qed.

Lemma x116_has_k_distant_ST_paths_compat (G : sgraph) (d k : nat) (S T : {set G}) :
  X116Legacy.x116_has_k_distant_ST_paths d k S T <-> x116_has_k_distant_ST_paths d k S T.
Proof. exact: iff_refl. Qed.

Lemma coarse_menger_paths_bounded_separator_statement_compat :
  X116Legacy.coarse_menger_paths_bounded_separator_statement <->
  coarse_menger_paths_bounded_separator_statement.
Proof. exact: iff_refl. Qed.

(** ** Certificates: X146 *)

Lemma x146_path_vertices_compat (G : sgraph) (p : seq G) :
  X146Legacy.x146_path_vertices p = x146_path_vertices p.
Proof. by rewrite /x146_path_vertices seq_verticesE. Qed.

Lemma x146_pairwise_distant_A_paths_compat (G : sgraph) (d : nat) (paths : seq (seq G)) :
  X146Legacy.x146_pairwise_distant_A_paths d paths <-> x146_pairwise_distant_A_paths d paths.
Proof. exact: iff_refl. Qed.

Lemma x146_has_k_distant_A_paths_compat (G : sgraph) (A : {set G}) (d k : nat) :
  X146Legacy.x146_has_k_distant_A_paths A d k <-> x146_has_k_distant_A_paths A d k.
Proof. exact: iff_refl. Qed.

Lemma x146_every_A_path_hits_ball_compat (G : sgraph) (A Z : {set G}) (r : nat) :
  X146Legacy.x146_every_A_path_hits_ball A Z r <-> x146_every_A_path_hits_ball A Z r.
Proof. exact: iff_refl. Qed.

Lemma geelen_coarse_gallai_A_paths_statement_compat :
  X146Legacy.geelen_coarse_gallai_A_paths_statement <->
  geelen_coarse_gallai_A_paths_statement.
Proof. exact: iff_refl. Qed.
