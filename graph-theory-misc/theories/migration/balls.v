(** A22 balls (graph-theory-misc): the frozen X20/X39/X113/X116/X146 vertex balls and seed-set balls, their sixteen
    reaching chains and six rows, and the complete X39, X40, X113, X116 and X146 rows.  Baseline, hashes and exact
    substitutions are recorded in meta/migration_reports/balls.spec.json.
    - [Legacy]: each local Fixpoint (radius 0 the centre, each step adding the neighbours of the previous ball) equals
      [GTBase.base.ball r x] pointwise, by induction on the radius; each seed-set ball equals
      [GTBase.balls.set_ball r S].
      Set equalities, not conversions; no connectedness, nonempty or radius guard is added.
    - [X20Legacy], [X39Legacy], [X40Legacy], [X113Legacy], [X116Legacy], [X146Legacy]: the chains and rows over the
      frozen balls.  X20's positive order, connectivity, least-square t and truncated [t.-1 - i] radii; X39's k before
      c before d, G, X, Y; X40's fixed distance 2; X113's uniform f, g; X116's l depending on k and d; X146's distinct
      A-path endpoints; all [d.-1] radii and natural subtractions are verbatim.  B1's path support, B5's set paths and
      B10's cycles stay live in these per-row copies.
    - [X39Original] ... [X146Original] (texts at the pre-migration 9e03072): the same chains and rows over B1's, B5's
      and B10's frozen pieces and the frozen balls; X39/X40 reuse B5's complete separator, X113 B10's complete
      forest-after chain.  B1's, B5's and B10's modules are aliased, not imported; their certificates are reused or
      their frozen pieces convert. *)
From Corelib Require Import Setoid Morphisms.
From GTBase Require Import base balls.
From GTBase Require distant_paths.
From GTMisc.conjectures Require Import X20 X39 X40 X113 X116 X146.
From GTMisc.migration Require path_vertices set_path genuine_cycle.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** B1's, B5's and B10's certificate modules, aliased without Import: their module names coincide with this file's. *)
Module B1 := GTMisc.migration.path_vertices.
Module B5 := GTMisc.migration.set_path.
Module B10 := GTMisc.migration.genuine_cycle.

Module Legacy.

Fixpoint x20_ball (G : sgraph) (r : nat) (x : G) : {set G} :=
  if r is r'.+1 then x20_ball r' x :|: \bigcup_(z in x20_ball r' x) N(z)
  else [set x].

Fixpoint x39_ball (G : sgraph) (r : nat) (x : G) : {set G} :=
  if r is r'.+1 then x39_ball r' x :|: \bigcup_(z in x39_ball r' x) N(z)
  else [set x].

Definition x39_set_ball (G : sgraph) (r : nat) (S : {set G}) : {set G} :=
  \bigcup_(x in S) Legacy.x39_ball r x.

Fixpoint x113_ball (G : sgraph) (r : nat) (x : G) : {set G} :=
  if r is r'.+1 then x113_ball r' x :|: \bigcup_(z in x113_ball r' x) N(z)
  else [set x].

Definition x113_set_ball (G : sgraph) (r : nat) (S : {set G}) : {set G} :=
  \bigcup_(x in S) Legacy.x113_ball r x.

Fixpoint x116_ball (G : sgraph) (r : nat) (x : G) : {set G} :=
  if r is r'.+1 then x116_ball r' x :|: \bigcup_(z in x116_ball r' x) N(z)
  else [set x].

Definition x116_set_ball (G : sgraph) (r : nat) (S : {set G}) : {set G} :=
  \bigcup_(x in S) Legacy.x116_ball r x.

Fixpoint x146_ball (G : sgraph) (r : nat) (x : G) : {set G} :=
  if r is r'.+1 then x146_ball r' x :|: \bigcup_(z in x146_ball r' x) N(z)
  else [set x].

Definition x146_set_ball (G : sgraph) (r : nat) (S : {set G}) : {set G} :=
  \bigcup_(x in S) Legacy.x146_ball r x.

End Legacy.

Module X20Legacy.

Definition x20_burning_cover (G : sgraph) (t : nat) : Prop :=
  exists c : 'I_t -> G,
    forall v : G, exists i : 'I_t,
      v \in Legacy.x20_ball (t.-1 - val i) (c i).

Definition burning_number_conjecture_statement : Prop :=
  forall (G : sgraph) (t : nat),
    0 < #|G| ->
    connected [set: G] ->
    x20_ceil_sqrt #|G| t ->
    X20Legacy.x20_burning_cover G t.

End X20Legacy.

Module X39Legacy.

Definition x39_pairwise_distant_paths
    (G : sgraph) (d : nat) (paths : seq (seq G)) : Prop :=
  forall p q : seq G,
    p \in paths -> q \in paths -> p != q ->
    [disjoint x39_path_vertices p & x39_path_vertices q] /\
    [disjoint Legacy.x39_set_ball (d.-1) (x39_path_vertices p) & x39_path_vertices q].

Definition x39_has_k_distant_xy_paths
    (G : sgraph) (d k : nat) (X Y : {set G}) : Prop :=
  exists paths : seq (seq G),
    size paths = k /\
    uniq paths /\
    (forall p : seq G, p \in paths -> x39_xy_path X Y p) /\
    X39Legacy.x39_pairwise_distant_paths d paths.

Definition coarse_menger_ball_separator_statement : Prop :=
  forall k : nat, exists c : nat,
    forall (d : nat) (G : sgraph) (X Y : {set G}),
      X39Legacy.x39_has_k_distant_xy_paths d k X Y \/
      exists Z : {set G},
        #|Z| < k /\
        x39_separates_xy X Y (Legacy.x39_set_ball (c * d) Z).

End X39Legacy.

Module X40Legacy.

Definition coarse_menger_distance_two_separator_statement : Prop :=
  forall k : nat,
    1 <= k ->
    exists ell : nat,
      0 < ell /\
      forall (G : sgraph) (S T : {set G}),
        X39Legacy.x39_has_k_distant_xy_paths 2 k S T \/
        exists X : {set G},
          #|X| <= k - 1 /\
          x39_separates_xy S T (Legacy.x39_set_ball ell X).

End X40Legacy.

Module X113Legacy.

Definition x113_pairwise_distant_cycles
    (G : sgraph) (d : nat) (cs : seq (seq G)) : Prop :=
  forall p q : seq G,
    p \in cs -> q \in cs -> p != q ->
    [disjoint Legacy.x113_set_ball d (x113_path_vertices p) & x113_path_vertices q].

Definition x113_has_k_distant_cycles
    (G : sgraph) (d k : nat) : Prop :=
  exists cs : seq (seq G),
    size cs = k /\
    uniq cs /\
    (forall c : seq G, c \in cs -> x113_is_cycle c) /\
    X113Legacy.x113_pairwise_distant_cycles d cs.

Definition coarse_erdos_posa_cycles_forest_statement : Prop :=
  exists f g : nat -> nat,
    forall (k d : nat) (G : sgraph),
      1 <= k -> 1 <= d ->
      X113Legacy.x113_has_k_distant_cycles G d k \/
      exists X : {set G},
        #|X| <= f k /\
        x113_is_forest_after (Legacy.x113_set_ball (g d) X).

End X113Legacy.

Module X116Legacy.

Definition x116_pairwise_distant_paths
    (G : sgraph) (d : nat) (paths : seq (seq G)) : Prop :=
  forall p q : seq G,
    p \in paths -> q \in paths -> p != q ->
    [disjoint x116_path_vertices p & x116_path_vertices q] /\
    [disjoint Legacy.x116_set_ball (d.-1) (x116_path_vertices p) & x116_path_vertices q].

Definition x116_has_k_distant_ST_paths
    (G : sgraph) (d k : nat) (S T : {set G}) : Prop :=
  exists paths : seq (seq G),
    size paths = k /\
    uniq paths /\
    (forall p : seq G, p \in paths -> x116_ST_path S T p) /\
    X116Legacy.x116_pairwise_distant_paths d paths.

Definition coarse_menger_paths_bounded_separator_statement : Prop :=
  forall (k d : nat),
    1 <= k -> 1 <= d ->
    exists l : nat,
      0 < l /\
      forall (G : sgraph) (S T : {set G}),
        X116Legacy.x116_has_k_distant_ST_paths d k S T \/
        exists X : {set G},
          #|X| <= k - 1 /\
          forall p : seq G,
            x116_ST_path S T p ->
            exists v : G,
              v \in x116_path_vertices p /\ v \in Legacy.x116_set_ball l X.

End X116Legacy.

Module X146Legacy.

Definition x146_pairwise_distant_A_paths
    (G : sgraph) (d : nat) (paths : seq (seq G)) : Prop :=
  forall p q : seq G,
    p \in paths -> q \in paths -> p != q ->
    [disjoint x146_path_vertices p & x146_path_vertices q] /\
    [disjoint Legacy.x146_set_ball (d.-1) (x146_path_vertices p) & x146_path_vertices q].

Definition x146_has_k_distant_A_paths
    (G : sgraph) (A : {set G}) (d k : nat) : Prop :=
  exists paths : seq (seq G),
    size paths = k /\
    uniq paths /\
    (forall p : seq G, p \in paths -> x146_A_path A p) /\
    X146Legacy.x146_pairwise_distant_A_paths d paths.

Definition x146_every_A_path_hits_ball
    (G : sgraph) (A Z : {set G}) (r : nat) : Prop :=
  forall p : seq G,
    x146_A_path A p ->
    exists v : G,
      v \in x146_path_vertices p /\ v \in Legacy.x146_set_ball r Z.

Definition geelen_coarse_gallai_A_paths_statement : Prop :=
  exists f g : nat -> nat,
    forall (k d : nat) (G : sgraph) (A : {set G}),
      1 <= k ->
      1 <= d ->
      X146Legacy.x146_has_k_distant_A_paths A d k \/
      exists Z : {set G},
        #|Z| <= f k /\
        X146Legacy.x146_every_A_path_hits_ball A Z (g d).

End X146Legacy.

Module X39Original.

Definition x39_pairwise_distant_paths
    (G : sgraph) (d : nat) (paths : seq (seq G)) : Prop :=
  forall p q : seq G,
    p \in paths -> q \in paths -> p != q ->
    [disjoint B1.Legacy.x39_path_vertices p & B1.Legacy.x39_path_vertices q] /\
    [disjoint Legacy.x39_set_ball (d.-1) (B1.Legacy.x39_path_vertices p) & B1.Legacy.x39_path_vertices q].

Definition x39_has_k_distant_xy_paths
    (G : sgraph) (d k : nat) (X Y : {set G}) : Prop :=
  exists paths : seq (seq G),
    size paths = k /\
    uniq paths /\
    (forall p : seq G, p \in paths -> B5.Legacy.x39_xy_path X Y p) /\
    X39Original.x39_pairwise_distant_paths d paths.

Definition coarse_menger_ball_separator_statement : Prop :=
  forall k : nat, exists c : nat,
    forall (d : nat) (G : sgraph) (X Y : {set G}),
      X39Original.x39_has_k_distant_xy_paths d k X Y \/
      exists Z : {set G},
        #|Z| < k /\
        B5.X39Original.separates_xy X Y (Legacy.x39_set_ball (c * d) Z).

End X39Original.

Module X40Original.

Definition coarse_menger_distance_two_separator_statement : Prop :=
  forall k : nat,
    1 <= k ->
    exists ell : nat,
      0 < ell /\
      forall (G : sgraph) (S T : {set G}),
        X39Original.x39_has_k_distant_xy_paths 2 k S T \/
        exists X : {set G},
          #|X| <= k - 1 /\
          B5.X39Original.separates_xy S T (Legacy.x39_set_ball ell X).

End X40Original.

Module X113Original.

Definition x113_pairwise_distant_cycles
    (G : sgraph) (d : nat) (cs : seq (seq G)) : Prop :=
  forall p q : seq G,
    p \in cs -> q \in cs -> p != q ->
    [disjoint Legacy.x113_set_ball d (B1.Legacy.x113_path_vertices p) & B1.Legacy.x113_path_vertices q].

Definition x113_has_k_distant_cycles
    (G : sgraph) (d k : nat) : Prop :=
  exists cs : seq (seq G),
    size cs = k /\
    uniq cs /\
    (forall c : seq G, c \in cs -> B10.Legacy.x113_is_cycle c) /\
    X113Original.x113_pairwise_distant_cycles d cs.

Definition coarse_erdos_posa_cycles_forest_statement : Prop :=
  exists f g : nat -> nat,
    forall (k d : nat) (G : sgraph),
      1 <= k -> 1 <= d ->
      X113Original.x113_has_k_distant_cycles G d k \/
      exists X : {set G},
        #|X| <= f k /\
        B10.X113Original.is_forest_after (Legacy.x113_set_ball (g d) X).

End X113Original.

Module X116Original.

Definition x116_pairwise_distant_paths
    (G : sgraph) (d : nat) (paths : seq (seq G)) : Prop :=
  forall p q : seq G,
    p \in paths -> q \in paths -> p != q ->
    [disjoint B1.Legacy.x116_path_vertices p & B1.Legacy.x116_path_vertices q] /\
    [disjoint Legacy.x116_set_ball (d.-1) (B1.Legacy.x116_path_vertices p) & B1.Legacy.x116_path_vertices q].

Definition x116_has_k_distant_ST_paths
    (G : sgraph) (d k : nat) (S T : {set G}) : Prop :=
  exists paths : seq (seq G),
    size paths = k /\
    uniq paths /\
    (forall p : seq G, p \in paths -> B5.Legacy.x116_ST_path S T p) /\
    X116Original.x116_pairwise_distant_paths d paths.

Definition coarse_menger_paths_bounded_separator_statement : Prop :=
  forall (k d : nat),
    1 <= k -> 1 <= d ->
    exists l : nat,
      0 < l /\
      forall (G : sgraph) (S T : {set G}),
        X116Original.x116_has_k_distant_ST_paths d k S T \/
        exists X : {set G},
          #|X| <= k - 1 /\
          forall p : seq G,
            B5.Legacy.x116_ST_path S T p ->
            exists v : G,
              v \in B1.Legacy.x116_path_vertices p /\ v \in Legacy.x116_set_ball l X.

End X116Original.

Module X146Original.

Definition x146_pairwise_distant_A_paths
    (G : sgraph) (d : nat) (paths : seq (seq G)) : Prop :=
  forall p q : seq G,
    p \in paths -> q \in paths -> p != q ->
    [disjoint B1.Legacy.x146_path_vertices p & B1.Legacy.x146_path_vertices q] /\
    [disjoint Legacy.x146_set_ball (d.-1) (B1.Legacy.x146_path_vertices p) & B1.Legacy.x146_path_vertices q].

Definition x146_has_k_distant_A_paths
    (G : sgraph) (A : {set G}) (d k : nat) : Prop :=
  exists paths : seq (seq G),
    size paths = k /\
    uniq paths /\
    (forall p : seq G, p \in paths -> x146_A_path A p) /\
    X146Original.x146_pairwise_distant_A_paths d paths.

Definition x146_every_A_path_hits_ball
    (G : sgraph) (A Z : {set G}) (r : nat) : Prop :=
  forall p : seq G,
    x146_A_path A p ->
    exists v : G,
      v \in B1.Legacy.x146_path_vertices p /\ v \in Legacy.x146_set_ball r Z.

Definition geelen_coarse_gallai_A_paths_statement : Prop :=
  exists f g : nat -> nat,
    forall (k d : nat) (G : sgraph) (A : {set G}),
      1 <= k ->
      1 <= d ->
      X146Original.x146_has_k_distant_A_paths A d k \/
      exists Z : {set G},
        #|Z| <= f k /\
        X146Original.x146_every_A_path_hits_ball A Z (g d).

End X146Original.

(** Not conversions: the local Fixpoints against [GTBase.base.ball], by induction on the radius. *)
Lemma x20_ball_compat (G : sgraph) (r : nat) (x : G) :
  Legacy.x20_ball r x = x20_ball r x.
Proof.
rewrite /x20_ball; elim: r => [//|r IH].
by rewrite /= IH.
Qed.

Lemma x39_ball_compat (G : sgraph) (r : nat) (x : G) :
  Legacy.x39_ball r x = x39_ball r x.
Proof.
rewrite /x39_ball; elim: r => [//|r IH].
by rewrite /= IH.
Qed.

Lemma x113_ball_compat (G : sgraph) (r : nat) (x : G) :
  Legacy.x113_ball r x = x113_ball r x.
Proof.
rewrite /x113_ball; elim: r => [//|r IH].
by rewrite /= IH.
Qed.

Lemma x116_ball_compat (G : sgraph) (r : nat) (x : G) :
  Legacy.x116_ball r x = x116_ball r x.
Proof.
rewrite /x116_ball; elim: r => [//|r IH].
by rewrite /= IH.
Qed.

Lemma x146_ball_compat (G : sgraph) (r : nat) (x : G) :
  Legacy.x146_ball r x = x146_ball r x.
Proof.
rewrite /x146_ball; elim: r => [//|r IH].
by rewrite /= IH.
Qed.

(** The seed-set balls: the same union over the supplied seeds, ball by ball. *)
Lemma x39_set_ball_compat (G : sgraph) (r : nat) (S : {set G}) :
  Legacy.x39_set_ball r S = x39_set_ball r S.
Proof.
rewrite /Legacy.x39_set_ball /x39_set_ball /set_ball.
by apply: eq_bigr => x _; exact: x39_ball_compat.
Qed.

Lemma x113_set_ball_compat (G : sgraph) (r : nat) (S : {set G}) :
  Legacy.x113_set_ball r S = x113_set_ball r S.
Proof.
rewrite /Legacy.x113_set_ball /x113_set_ball /set_ball.
by apply: eq_bigr => x _; exact: x113_ball_compat.
Qed.

Lemma x116_set_ball_compat (G : sgraph) (r : nat) (S : {set G}) :
  Legacy.x116_set_ball r S = x116_set_ball r S.
Proof.
rewrite /Legacy.x116_set_ball /x116_set_ball /set_ball.
by apply: eq_bigr => x _; exact: x116_ball_compat.
Qed.

Lemma x146_set_ball_compat (G : sgraph) (r : nat) (S : {set G}) :
  Legacy.x146_set_ball r S = x146_set_ball r S.
Proof.
rewrite /Legacy.x146_set_ball /x146_set_ball /set_ball.
by apply: eq_bigr => x _; exact: x146_ball_compat.
Qed.

Lemma x20_burning_cover_compat (G : sgraph) (t : nat) :
  X20Legacy.x20_burning_cover G t <-> x20_burning_cover G t.
Proof.
rewrite /X20Legacy.x20_burning_cover.
setoid_rewrite x20_ball_compat.
reflexivity.
Qed.

Lemma burning_number_conjecture_statement_compat :
  X20Legacy.burning_number_conjecture_statement <-> burning_number_conjecture_statement.
Proof.
rewrite /X20Legacy.burning_number_conjecture_statement.
setoid_rewrite x20_burning_cover_compat.
reflexivity.
Qed.

(** B27 (2026-10-03): the live X39 / X116 / X146 distant-path relations and wrappers are now aliases of
    GTBase.distant_paths, which drops their redundant support-disjointness conjunct, so the certificates below
    that reach them through a frozen copy of that conjunct are proved through [pairwise_distant_seqsP],
    [has_k_distant_set_pathsP] and pointwise row transports instead of by conversion; their statements and
    every frozen body are unchanged. *)

Lemma x39_pairwise_distant_paths_compat (G : sgraph) (d : nat) (paths : seq (seq G)) :
  X39Legacy.x39_pairwise_distant_paths d paths <-> x39_pairwise_distant_paths d paths.
Proof.
rewrite /X39Legacy.x39_pairwise_distant_paths.
setoid_rewrite x39_set_ball_compat.
exact: distant_paths.pairwise_distant_seqsP.
Qed.

Lemma x39_has_k_distant_xy_paths_compat (G : sgraph) (d k : nat) (X Y : {set G}) :
  X39Legacy.x39_has_k_distant_xy_paths d k X Y <-> x39_has_k_distant_xy_paths d k X Y.
Proof.
rewrite /X39Legacy.x39_has_k_distant_xy_paths.
setoid_rewrite x39_pairwise_distant_paths_compat.
reflexivity.
Qed.

Lemma coarse_menger_ball_separator_statement_compat :
  X39Legacy.coarse_menger_ball_separator_statement <-> coarse_menger_ball_separator_statement.
Proof.
rewrite /X39Legacy.coarse_menger_ball_separator_statement.
setoid_rewrite x39_has_k_distant_xy_paths_compat.
setoid_rewrite x39_set_ball_compat.
reflexivity.
Qed.

Lemma coarse_menger_distance_two_separator_statement_compat :
  X40Legacy.coarse_menger_distance_two_separator_statement <->
  coarse_menger_distance_two_separator_statement.
Proof.
rewrite /X40Legacy.coarse_menger_distance_two_separator_statement.
setoid_rewrite x39_has_k_distant_xy_paths_compat.
setoid_rewrite x39_set_ball_compat.
reflexivity.
Qed.

Lemma x113_pairwise_distant_cycles_compat (G : sgraph) (d : nat) (cs : seq (seq G)) :
  X113Legacy.x113_pairwise_distant_cycles d cs <-> x113_pairwise_distant_cycles d cs.
Proof.
rewrite /X113Legacy.x113_pairwise_distant_cycles.
setoid_rewrite x113_set_ball_compat.
reflexivity.
Qed.

Lemma x113_has_k_distant_cycles_compat (G : sgraph) (d k : nat) :
  X113Legacy.x113_has_k_distant_cycles G d k <-> x113_has_k_distant_cycles G d k.
Proof.
rewrite /X113Legacy.x113_has_k_distant_cycles.
setoid_rewrite x113_pairwise_distant_cycles_compat.
reflexivity.
Qed.

Lemma coarse_erdos_posa_cycles_forest_statement_compat :
  X113Legacy.coarse_erdos_posa_cycles_forest_statement <-> coarse_erdos_posa_cycles_forest_statement.
Proof.
rewrite /X113Legacy.coarse_erdos_posa_cycles_forest_statement.
setoid_rewrite x113_has_k_distant_cycles_compat.
setoid_rewrite x113_set_ball_compat.
reflexivity.
Qed.

Lemma x116_pairwise_distant_paths_compat (G : sgraph) (d : nat) (paths : seq (seq G)) :
  X116Legacy.x116_pairwise_distant_paths d paths <-> x116_pairwise_distant_paths d paths.
Proof.
rewrite /X116Legacy.x116_pairwise_distant_paths.
setoid_rewrite x116_set_ball_compat.
exact: distant_paths.pairwise_distant_seqsP.
Qed.

Lemma x116_has_k_distant_ST_paths_compat (G : sgraph) (d k : nat) (S T : {set G}) :
  X116Legacy.x116_has_k_distant_ST_paths d k S T <-> x116_has_k_distant_ST_paths d k S T.
Proof.
rewrite /X116Legacy.x116_has_k_distant_ST_paths.
setoid_rewrite x116_pairwise_distant_paths_compat.
reflexivity.
Qed.

Lemma coarse_menger_paths_bounded_separator_statement_compat :
  X116Legacy.coarse_menger_paths_bounded_separator_statement <->
  coarse_menger_paths_bounded_separator_statement.
Proof.
rewrite /X116Legacy.coarse_menger_paths_bounded_separator_statement.
setoid_rewrite x116_has_k_distant_ST_paths_compat.
setoid_rewrite x116_set_ball_compat.
reflexivity.
Qed.

Lemma x146_pairwise_distant_A_paths_compat (G : sgraph) (d : nat) (paths : seq (seq G)) :
  X146Legacy.x146_pairwise_distant_A_paths d paths <-> x146_pairwise_distant_A_paths d paths.
Proof.
rewrite /X146Legacy.x146_pairwise_distant_A_paths.
setoid_rewrite x146_set_ball_compat.
exact: distant_paths.pairwise_distant_seqsP.
Qed.

Lemma x146_has_k_distant_A_paths_compat (G : sgraph) (A : {set G}) (d k : nat) :
  X146Legacy.x146_has_k_distant_A_paths A d k <-> x146_has_k_distant_A_paths A d k.
Proof.
rewrite /X146Legacy.x146_has_k_distant_A_paths.
setoid_rewrite x146_pairwise_distant_A_paths_compat.
reflexivity.
Qed.

Lemma x146_every_A_path_hits_ball_compat (G : sgraph) (A Z : {set G}) (r : nat) :
  X146Legacy.x146_every_A_path_hits_ball A Z r <-> x146_every_A_path_hits_ball A Z r.
Proof.
rewrite /X146Legacy.x146_every_A_path_hits_ball.
setoid_rewrite x146_set_ball_compat.
reflexivity.
Qed.

Lemma geelen_coarse_gallai_A_paths_statement_compat :
  X146Legacy.geelen_coarse_gallai_A_paths_statement <-> geelen_coarse_gallai_A_paths_statement.
Proof.
rewrite /X146Legacy.geelen_coarse_gallai_A_paths_statement.
setoid_rewrite x146_has_k_distant_A_paths_compat.
setoid_rewrite x146_every_A_path_hits_ball_compat.
reflexivity.
Qed.

(** Complete rows: the frozen balls are rewritten, then B1's and B5's chain certificates, or conversion of their
    frozen pieces. After B26, B1's and B5's separator and affected row certificates use the unconditional seq_separatorP bridge and pointwise transport; the explicit rewrites below retain their exact types and proofs. *)
Lemma x39_pairwise_distant_paths_original_compat (G : sgraph) (d : nat) (paths : seq (seq G)) :
  X39Original.x39_pairwise_distant_paths d paths <-> x39_pairwise_distant_paths d paths.
Proof.
rewrite /X39Original.x39_pairwise_distant_paths.
setoid_rewrite x39_set_ball_compat.
exact: B1.x39_pairwise_distant_paths_compat d paths.
Qed.

Lemma x39_has_k_distant_xy_paths_original_compat (G : sgraph) (d k : nat) (X Y : {set G}) :
  X39Original.x39_has_k_distant_xy_paths d k X Y <-> x39_has_k_distant_xy_paths d k X Y.
Proof.
rewrite /X39Original.x39_has_k_distant_xy_paths.
setoid_rewrite x39_pairwise_distant_paths_original_compat.
exact: B5.x39_has_k_distant_xy_paths_compat d k X Y.
Qed.

Lemma coarse_menger_ball_separator_statement_original_compat :
  X39Original.coarse_menger_ball_separator_statement <-> coarse_menger_ball_separator_statement.
Proof.
rewrite /X39Original.coarse_menger_ball_separator_statement.
setoid_rewrite x39_has_k_distant_xy_paths_original_compat.
setoid_rewrite B5.x39_separates_xy_original_compat.
setoid_rewrite x39_set_ball_compat.
reflexivity.
Qed.

Lemma coarse_menger_distance_two_separator_statement_original_compat :
  X40Original.coarse_menger_distance_two_separator_statement <->
  coarse_menger_distance_two_separator_statement.
Proof.
rewrite /X40Original.coarse_menger_distance_two_separator_statement.
setoid_rewrite x39_has_k_distant_xy_paths_original_compat.
setoid_rewrite B5.x39_separates_xy_original_compat.
setoid_rewrite x39_set_ball_compat.
reflexivity.
Qed.

Lemma x113_pairwise_distant_cycles_original_compat (G : sgraph) (d : nat) (cs : seq (seq G)) :
  X113Original.x113_pairwise_distant_cycles d cs <-> x113_pairwise_distant_cycles d cs.
Proof.
rewrite /X113Original.x113_pairwise_distant_cycles.
setoid_rewrite x113_set_ball_compat.
exact: B1.x113_pairwise_distant_cycles_compat d cs.
Qed.

Lemma x113_has_k_distant_cycles_original_compat (G : sgraph) (d k : nat) :
  X113Original.x113_has_k_distant_cycles G d k <-> x113_has_k_distant_cycles G d k.
Proof.
rewrite /X113Original.x113_has_k_distant_cycles.
setoid_rewrite x113_pairwise_distant_cycles_original_compat.
exact: B10.x113_has_k_distant_cycles_compat G d k.
Qed.

Lemma coarse_erdos_posa_cycles_forest_statement_original_compat :
  X113Original.coarse_erdos_posa_cycles_forest_statement <-> coarse_erdos_posa_cycles_forest_statement.
Proof.
rewrite /X113Original.coarse_erdos_posa_cycles_forest_statement.
setoid_rewrite x113_has_k_distant_cycles_original_compat.
setoid_rewrite B10.x113_is_forest_after_original_compat.
setoid_rewrite x113_set_ball_compat.
reflexivity.
Qed.

Lemma x116_pairwise_distant_paths_original_compat (G : sgraph) (d : nat) (paths : seq (seq G)) :
  X116Original.x116_pairwise_distant_paths d paths <-> x116_pairwise_distant_paths d paths.
Proof.
rewrite /X116Original.x116_pairwise_distant_paths.
setoid_rewrite x116_set_ball_compat.
exact: B1.x116_pairwise_distant_paths_compat d paths.
Qed.

Lemma x116_has_k_distant_ST_paths_original_compat (G : sgraph) (d k : nat) (S T : {set G}) :
  X116Original.x116_has_k_distant_ST_paths d k S T <-> x116_has_k_distant_ST_paths d k S T.
Proof.
rewrite /X116Original.x116_has_k_distant_ST_paths.
setoid_rewrite x116_pairwise_distant_paths_original_compat.
exact: B5.x116_has_k_distant_ST_paths_compat d k S T.
Qed.

Lemma coarse_menger_paths_bounded_separator_statement_original_compat :
  X116Original.coarse_menger_paths_bounded_separator_statement <->
  coarse_menger_paths_bounded_separator_statement.
Proof.
rewrite /X116Original.coarse_menger_paths_bounded_separator_statement.
setoid_rewrite x116_has_k_distant_ST_paths_original_compat.
setoid_rewrite B5.x116_ST_path_compat.
setoid_rewrite B1.x116_path_vertices_compat.
setoid_rewrite x116_set_ball_compat.
reflexivity.
Qed.

Lemma x146_pairwise_distant_A_paths_original_compat (G : sgraph) (d : nat) (paths : seq (seq G)) :
  X146Original.x146_pairwise_distant_A_paths d paths <-> x146_pairwise_distant_A_paths d paths.
Proof.
rewrite /X146Original.x146_pairwise_distant_A_paths.
setoid_rewrite x146_set_ball_compat.
exact: B1.x146_pairwise_distant_A_paths_compat d paths.
Qed.

Lemma x146_has_k_distant_A_paths_original_compat (G : sgraph) (A : {set G}) (d k : nat) :
  X146Original.x146_has_k_distant_A_paths A d k <-> x146_has_k_distant_A_paths A d k.
Proof.
rewrite /X146Original.x146_has_k_distant_A_paths.
setoid_rewrite x146_pairwise_distant_A_paths_original_compat.
reflexivity.
Qed.

Lemma x146_every_A_path_hits_ball_original_compat (G : sgraph) (A Z : {set G}) (r : nat) :
  X146Original.x146_every_A_path_hits_ball A Z r <-> x146_every_A_path_hits_ball A Z r.
Proof.
rewrite /X146Original.x146_every_A_path_hits_ball.
setoid_rewrite x146_set_ball_compat.
exact: B1.x146_every_A_path_hits_ball_compat A Z r.
Qed.

Lemma geelen_coarse_gallai_A_paths_statement_original_compat :
  X146Original.geelen_coarse_gallai_A_paths_statement <-> geelen_coarse_gallai_A_paths_statement.
Proof.
rewrite /X146Original.geelen_coarse_gallai_A_paths_statement.
setoid_rewrite x146_has_k_distant_A_paths_original_compat.
setoid_rewrite x146_every_A_path_hits_ball_original_compat.
reflexivity.
Qed.
