(** * GTMisc.migration.path_vertices — frozen path-vertex chains (library migration B1)

    Batch B, family [path-vertices] (meta/library_primitives.json).  [Legacy]
    freezes the conjecture-local helpers [x39_path_vertices], [x113_path_vertices],
    [x116_path_vertices] and [x146_path_vertices] verbatim as they stood at
    9e03072, before the migration; the live helpers now unfold to
    [GTBase.walks_paths.seq_vertices].  [X39Legacy], [X113Legacy], [X116Legacy] and
    [X146Legacy] freeze the affected chains of their rows, the statements included:
    the copies drop the wave prefix of their names and refer to the frozen helpers
    through [Legacy], so no frozen body resolves through a live helper of this
    family.  Row X40 reaches [x39_path_vertices] through the X39 vocabulary, so
    [X40Legacy.statement] refers to the frozen [X39Legacy] chain.  Definitions that
    do not reach a helper (balls, X-Y, S-T and A-path predicates, genuine cycles)
    are the live, unchanged ones.

    [seq_vertices s] is MathComp's [[set:: s]], which unfolds to the frozen
    comprehension [[set v | v \in s]], so every live definition is convertible to
    its frozen copy: the certificates below are kernel-checked conversions, the
    helper certificates going through [seq_verticesE].  Source hashes, the exact
    substitutions and the per-row theorem names are recorded in
    meta/migration_reports/path_vertices.md. *)

From GTBase Require Import base.
From GTBase Require set_separators.
From GTBase Require distant_paths.
From GTMisc.conjectures Require Import X39 X40 X113 X116 X146.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Legacy.

Definition x39_path_vertices (G : sgraph) (p : seq G) : {set G} :=
  [set v | v \in p].

Definition x113_path_vertices (G : sgraph) (p : seq G) : {set G} :=
  [set v | v \in p].

Definition x116_path_vertices (G : sgraph) (p : seq G) : {set G} :=
  [set v | v \in p].

Definition x146_path_vertices (G : sgraph) (p : seq G) : {set G} :=
  [set v | v \in p].

End Legacy.

Module X39Legacy.

Definition pairwise_distant_paths
    (G : sgraph) (d : nat) (paths : seq (seq G)) : Prop :=
  forall p q : seq G,
    p \in paths -> q \in paths -> p != q ->
    [disjoint Legacy.x39_path_vertices p & Legacy.x39_path_vertices q] /\
    [disjoint x39_set_ball (d.-1) (Legacy.x39_path_vertices p) & Legacy.x39_path_vertices q].

Definition has_k_distant_xy_paths
    (G : sgraph) (d k : nat) (X Y : {set G}) : Prop :=
  exists paths : seq (seq G),
    size paths = k /\
    uniq paths /\
    (forall p : seq G, p \in paths -> x39_xy_path X Y p) /\
    pairwise_distant_paths d paths.

Definition separates_xy
    (G : sgraph) (X Y A : {set G}) : Prop :=
  forall p : seq G,
    x39_xy_path X Y p ->
    [disjoint Legacy.x39_path_vertices p & A] ->
    False.

Definition statement : Prop :=
  forall k : nat, exists c : nat,
    forall (d : nat) (G : sgraph) (X Y : {set G}),
      has_k_distant_xy_paths d k X Y \/
      exists Z : {set G},
        #|Z| < k /\
        separates_xy X Y (x39_set_ball (c * d) Z).

End X39Legacy.

Module X40Legacy.

Definition statement : Prop :=
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

Module X113Legacy.

Definition pairwise_distant_cycles
    (G : sgraph) (d : nat) (cs : seq (seq G)) : Prop :=
  forall p q : seq G,
    p \in cs -> q \in cs -> p != q ->
    [disjoint x113_set_ball d (Legacy.x113_path_vertices p) & Legacy.x113_path_vertices q].

Definition has_k_distant_cycles
    (G : sgraph) (d k : nat) : Prop :=
  exists cs : seq (seq G),
    size cs = k /\
    uniq cs /\
    (forall c : seq G, c \in cs -> x113_is_cycle c) /\
    pairwise_distant_cycles d cs.

Definition is_forest_after
    (G : sgraph) (A : {set G}) : Prop :=
  forall c : seq G,
    x113_is_cycle c ->
    [disjoint Legacy.x113_path_vertices c & A] ->
    False.

Definition statement : Prop :=
  exists f g : nat -> nat,
    forall (k d : nat) (G : sgraph),
      1 <= k -> 1 <= d ->
      has_k_distant_cycles G d k \/
      exists X : {set G},
        #|X| <= f k /\
        is_forest_after (x113_set_ball (g d) X).

End X113Legacy.

Module X116Legacy.

Definition pairwise_distant_paths
    (G : sgraph) (d : nat) (paths : seq (seq G)) : Prop :=
  forall p q : seq G,
    p \in paths -> q \in paths -> p != q ->
    [disjoint Legacy.x116_path_vertices p & Legacy.x116_path_vertices q] /\
    [disjoint x116_set_ball (d.-1) (Legacy.x116_path_vertices p) & Legacy.x116_path_vertices q].

Definition has_k_distant_ST_paths
    (G : sgraph) (d k : nat) (S T : {set G}) : Prop :=
  exists paths : seq (seq G),
    size paths = k /\
    uniq paths /\
    (forall p : seq G, p \in paths -> x116_ST_path S T p) /\
    pairwise_distant_paths d paths.

Definition statement : Prop :=
  forall (k d : nat),
    1 <= k -> 1 <= d ->
    exists l : nat,
      0 < l /\
      forall (G : sgraph) (S T : {set G}),
        has_k_distant_ST_paths d k S T \/
        exists X : {set G},
          #|X| <= k - 1 /\
          forall p : seq G,
            x116_ST_path S T p ->
            exists v : G,
              v \in Legacy.x116_path_vertices p /\ v \in x116_set_ball l X.

End X116Legacy.

Module X146Legacy.

Definition pairwise_distant_A_paths
    (G : sgraph) (d : nat) (paths : seq (seq G)) : Prop :=
  forall p q : seq G,
    p \in paths -> q \in paths -> p != q ->
    [disjoint Legacy.x146_path_vertices p & Legacy.x146_path_vertices q] /\
    [disjoint x146_set_ball (d.-1) (Legacy.x146_path_vertices p) & Legacy.x146_path_vertices q].

Definition has_k_distant_A_paths
    (G : sgraph) (A : {set G}) (d k : nat) : Prop :=
  exists paths : seq (seq G),
    size paths = k /\
    uniq paths /\
    (forall p : seq G, p \in paths -> x146_A_path A p) /\
    pairwise_distant_A_paths d paths.

Definition every_A_path_hits_ball
    (G : sgraph) (A Z : {set G}) (r : nat) : Prop :=
  forall p : seq G,
    x146_A_path A p ->
    exists v : G,
      v \in Legacy.x146_path_vertices p /\ v \in x146_set_ball r Z.

Definition statement : Prop :=
  exists f g : nat -> nat,
    forall (k d : nat) (G : sgraph) (A : {set G}),
      1 <= k ->
      1 <= d ->
      has_k_distant_A_paths A d k \/
      exists Z : {set G},
        #|Z| <= f k /\
        every_A_path_hits_ball A Z (g d).

End X146Legacy.

(** ** Certificates: X39 *)

Lemma x39_path_vertices_compat (G : sgraph) (p : seq G) :
  Legacy.x39_path_vertices p = x39_path_vertices p.
Proof. by rewrite /x39_path_vertices seq_verticesE. Qed.

(** B27 (2026-10-03): the live X39 / X116 / X146 distant-path relations and wrappers are now aliases of
    GTBase.distant_paths, which drops their redundant support-disjointness conjunct, so the certificates below
    that reach them through a frozen copy of that conjunct are proved through [pairwise_distant_seqsP],
    [has_k_distant_set_pathsP] and pointwise row transports instead of by conversion; their statements and
    every frozen body are unchanged. *)

Lemma x39_pairwise_distant_paths_compat (G : sgraph) (d : nat) (paths : seq (seq G)) :
  X39Legacy.pairwise_distant_paths d paths <-> x39_pairwise_distant_paths d paths.
Proof. exact: distant_paths.pairwise_distant_seqsP. Qed.

Lemma x39_has_k_distant_xy_paths_compat (G : sgraph) (d k : nat) (X Y : {set G}) :
  X39Legacy.has_k_distant_xy_paths d k X Y <-> x39_has_k_distant_xy_paths d k X Y.
Proof. exact: distant_paths.has_k_distant_set_pathsP. Qed.

(** B26 (2026-10-03): the live [x39_separates_xy] is now an alias of upstream
    [GraphTheory.core.connectivity.separator] over packaged paths, so the separator and row certificates
    below that reach it are proved through [GTBase.set_separators.seq_separatorP] and a pointwise row
    transport instead of by conversion; their statements and every frozen body are unchanged. *)

Lemma x39_separates_xy_compat (G : sgraph) (X Y A : {set G}) :
  X39Legacy.separates_xy X Y A <-> x39_separates_xy X Y A.
Proof. exact: set_separators.seq_separatorP. Qed.

Lemma coarse_menger_ball_separator_statement_compat :
  X39Legacy.statement <-> coarse_menger_ball_separator_statement.
Proof.
split=> h k; have [c hc] := h k; exists c => d G X Y;
  case: (hc d G X Y) => [l | [Z [Zk sep]]];
  first [by left; apply/x39_has_k_distant_xy_paths_compat
        | by right; exists Z; split=> //; apply/x39_separates_xy_compat].
Qed.

(** ** Certificates: X40 (through the frozen X39 chain) *)

Lemma coarse_menger_distance_two_separator_statement_compat :
  X40Legacy.statement <-> coarse_menger_distance_two_separator_statement.
Proof.
split=> h k k1; have [ell [ell0 he]] := h k k1; exists ell; split=> // G S T;
  case: (he G S T) => [l | [X [Xk sep]]];
  first [by left; apply/x39_has_k_distant_xy_paths_compat
        | by right; exists X; split=> //; apply/x39_separates_xy_compat].
Qed.

(** ** Certificates: X113 *)

Lemma x113_path_vertices_compat (G : sgraph) (p : seq G) :
  Legacy.x113_path_vertices p = x113_path_vertices p.
Proof. by rewrite /x113_path_vertices seq_verticesE. Qed.

Lemma x113_pairwise_distant_cycles_compat (G : sgraph) (d : nat) (cs : seq (seq G)) :
  X113Legacy.pairwise_distant_cycles d cs <-> x113_pairwise_distant_cycles d cs.
Proof. exact: iff_refl. Qed.

Lemma x113_has_k_distant_cycles_compat (G : sgraph) (d k : nat) :
  X113Legacy.has_k_distant_cycles G d k <-> x113_has_k_distant_cycles G d k.
Proof. exact: iff_refl. Qed.

Lemma x113_is_forest_after_compat (G : sgraph) (A : {set G}) :
  X113Legacy.is_forest_after A <-> x113_is_forest_after A.
Proof. exact: iff_refl. Qed.

Lemma coarse_erdos_posa_cycles_forest_statement_compat :
  X113Legacy.statement <-> coarse_erdos_posa_cycles_forest_statement.
Proof. exact: iff_refl. Qed.

(** ** Certificates: X116 *)

Lemma x116_path_vertices_compat (G : sgraph) (p : seq G) :
  Legacy.x116_path_vertices p = x116_path_vertices p.
Proof. by rewrite /x116_path_vertices seq_verticesE. Qed.

Lemma x116_pairwise_distant_paths_compat (G : sgraph) (d : nat) (paths : seq (seq G)) :
  X116Legacy.pairwise_distant_paths d paths <-> x116_pairwise_distant_paths d paths.
Proof. exact: distant_paths.pairwise_distant_seqsP. Qed.

Lemma x116_has_k_distant_ST_paths_compat (G : sgraph) (d k : nat) (S T : {set G}) :
  X116Legacy.has_k_distant_ST_paths d k S T <-> x116_has_k_distant_ST_paths d k S T.
Proof. exact: distant_paths.has_k_distant_set_pathsP. Qed.

Lemma coarse_menger_paths_bounded_separator_statement_compat :
  X116Legacy.statement <-> coarse_menger_paths_bounded_separator_statement.
Proof.
split=> h k d k1 d1; have [l [l0 hl]] := h k d k1 d1; exists l; split=> // G S T;
  case: (hl G S T) => [hk | r];
  first [by left; apply/x116_has_k_distant_ST_paths_compat | by right].
Qed.

(** ** Certificates: X146 *)

Lemma x146_path_vertices_compat (G : sgraph) (p : seq G) :
  Legacy.x146_path_vertices p = x146_path_vertices p.
Proof. by rewrite /x146_path_vertices seq_verticesE. Qed.

Lemma x146_pairwise_distant_A_paths_compat (G : sgraph) (d : nat) (paths : seq (seq G)) :
  X146Legacy.pairwise_distant_A_paths d paths <-> x146_pairwise_distant_A_paths d paths.
Proof. exact: distant_paths.pairwise_distant_seqsP. Qed.

Lemma x146_has_k_distant_A_paths_compat (G : sgraph) (A : {set G}) (d k : nat) :
  X146Legacy.has_k_distant_A_paths A d k <-> x146_has_k_distant_A_paths A d k.
Proof.
split=> -[ps [sz [u [ap dist]]]]; exists ps; split=> //; split=> //; split=> //.
  exact: (proj1 (x146_pairwise_distant_A_paths_compat d ps) dist).
exact: (proj2 (x146_pairwise_distant_A_paths_compat d ps) dist).
Qed.

Lemma x146_every_A_path_hits_ball_compat (G : sgraph) (A Z : {set G}) (r : nat) :
  X146Legacy.every_A_path_hits_ball A Z r <-> x146_every_A_path_hits_ball A Z r.
Proof. exact: iff_refl. Qed.

Lemma geelen_coarse_gallai_A_paths_statement_compat :
  X146Legacy.statement <-> geelen_coarse_gallai_A_paths_statement.
Proof.
split=> -[f [g h]]; exists f, g => k d G A k1 d1;
  case: (h k d G A k1 d1) => [hk | r];
  first [by left; apply/x146_has_k_distant_A_paths_compat | by right].
Qed.
