(** A22 balls (packing): the frozen X26 and X111 vertex balls and X26's seed-set ball, X26's distant-path chains and
    row, X111's transversal, packing, tau and nu and its row, and the complete X26 row.  Baseline, hashes and exact
    substitutions are recorded in meta/migration_reports/balls.spec.json.
    - [Legacy]: each local Fixpoint equals [GTBase.base.ball r x] pointwise, by induction on the radius; X26's seed-set
      ball equals [GTBase.balls.set_ball r S].  Set equalities, not conversions; no guard is added.
    - [X26Legacy], [X111Legacy]: X26 keeps d and Dmax before C > 0 before k, G, X, Y, the degree bound, [C * k] and the
      stronger d = 0 reading; X111 keeps one c before r, G and U, [wagner_planar], tau's arg-min default [[set: G]]
      and nu's maximum, with exact natural values (empty U gives 0 and 0).  B1's path support and B5's set paths stay
      live in the per-row X26 copies.
    - [X26Original] (texts at the pre-migration 9e03072): the chains and row over B1's and B5's frozen pieces, the
      frozen balls and B5's complete separator.  B1's and B5's modules are aliased, not imported; their certificates
      are reused. *)
From Corelib Require Import Setoid Morphisms.
From GTBase Require Import base balls.
From Packing.conjectures Require Import X26 X111.
From Packing.migration Require path_vertices set_path.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** B1's and B5's certificate modules, aliased without Import: their module names coincide with this file's. *)
Module B1 := Packing.migration.path_vertices.
Module B5 := Packing.migration.set_path.

Module Legacy.

Fixpoint x26_ball (G : sgraph) (r : nat) (x : G) : {set G} :=
  if r is r'.+1 then x26_ball r' x :|: \bigcup_(z in x26_ball r' x) N(z)
  else [set x].

Definition x26_set_ball (G : sgraph) (r : nat) (S : {set G}) : {set G} :=
  \bigcup_(x in S) Legacy.x26_ball r x.

Fixpoint x111_ball (G : sgraph) (r : nat) (x : G) : {set G} :=
  if r is r'.+1 then x111_ball r' x :|: \bigcup_(z in x111_ball r' x) N(z)
  else [set x].

End Legacy.

Module X26Legacy.

Definition x26_pairwise_distant_paths
    (G : sgraph) (d : nat) (paths : seq (seq G)) : Prop :=
  forall p q : seq G,
    p \in paths -> q \in paths -> p != q ->
    [disjoint Legacy.x26_set_ball (d.-1) (x26_path_vertices p) & x26_path_vertices q].

Definition x26_has_k_distant_xy_paths
    (G : sgraph) (d k : nat) (X Y : {set G}) : Prop :=
  exists paths : seq (seq G),
    size paths = k /\
    uniq paths /\
    (forall p : seq G, p \in paths -> x26_xy_path X Y p) /\
    X26Legacy.x26_pairwise_distant_paths d paths.

Definition bounded_degree_distant_induced_menger_statement : Prop :=
  forall d Dmax : nat, exists C : nat,
    0 < C /\
    forall (k : nat) (G : sgraph) (X Y : {set G}),
      Delta G <= Dmax ->
      X26Legacy.x26_has_k_distant_xy_paths d k X Y \/
      exists Z : {set G},
        #|Z| < C * k /\
        x26_separates_xy X Y Z.

End X26Legacy.

Module X111Legacy.

Definition x111_is_transversal (G : sgraph) (r : nat) (U T : {set G}) : bool :=
  [forall u, (u \in U) ==> (T :&: Legacy.x111_ball r u != set0)].

Definition x111_is_packing (G : sgraph) (r : nat) (U S : {set G}) : bool :=
  (S \subset U) &&
  [forall u, [forall v,
     (u \in S) ==> (v \in S) ==> (u != v) ==>
     [disjoint Legacy.x111_ball r u & Legacy.x111_ball r v]]].

Definition x111_tau (G : sgraph) (r : nat) (U : {set G}) : nat :=
  #|[arg min_(T < [set: G] | X111Legacy.x111_is_transversal r U T) #|T|]|.

Definition x111_nu (G : sgraph) (r : nat) (U : {set G}) : nat :=
  \max_(S : {set G} | X111Legacy.x111_is_packing r U S) #|S|.

Definition chepoi_estellon_vaxes_ball_hypergraph_transversal_statement : Prop :=
  exists c : nat,
    forall (r : nat) (G : sgraph),
      wagner_planar G ->
      forall U : {set G},
        X111Legacy.x111_tau r U <= c * X111Legacy.x111_nu r U.

End X111Legacy.

Module X26Original.

Definition x26_pairwise_distant_paths
    (G : sgraph) (d : nat) (paths : seq (seq G)) : Prop :=
  forall p q : seq G,
    p \in paths -> q \in paths -> p != q ->
    [disjoint Legacy.x26_set_ball (d.-1) (B1.Legacy.x26_path_vertices p) & B1.Legacy.x26_path_vertices q].

Definition x26_has_k_distant_xy_paths
    (G : sgraph) (d k : nat) (X Y : {set G}) : Prop :=
  exists paths : seq (seq G),
    size paths = k /\
    uniq paths /\
    (forall p : seq G, p \in paths -> B5.Legacy.x26_xy_path X Y p) /\
    X26Original.x26_pairwise_distant_paths d paths.

Definition bounded_degree_distant_induced_menger_statement : Prop :=
  forall d Dmax : nat, exists C : nat,
    0 < C /\
    forall (k : nat) (G : sgraph) (X Y : {set G}),
      Delta G <= Dmax ->
      X26Original.x26_has_k_distant_xy_paths d k X Y \/
      exists Z : {set G},
        #|Z| < C * k /\
        B5.X26Original.separates_xy X Y Z.

End X26Original.

(** Not conversions: the local Fixpoints against [GTBase.base.ball], by induction on the radius. *)
Lemma x26_ball_compat (G : sgraph) (r : nat) (x : G) :
  Legacy.x26_ball r x = x26_ball r x.
Proof.
rewrite /x26_ball; elim: r => [//|r IH].
by rewrite /= IH.
Qed.

Lemma x111_ball_compat (G : sgraph) (r : nat) (x : G) :
  Legacy.x111_ball r x = x111_ball r x.
Proof.
rewrite /x111_ball; elim: r => [//|r IH].
by rewrite /= IH.
Qed.

Lemma x26_set_ball_compat (G : sgraph) (r : nat) (S : {set G}) :
  Legacy.x26_set_ball r S = x26_set_ball r S.
Proof.
rewrite /Legacy.x26_set_ball /x26_set_ball /set_ball.
by apply: eq_bigr => x _; exact: x26_ball_compat.
Qed.

Lemma x26_pairwise_distant_paths_compat (G : sgraph) (d : nat) (paths : seq (seq G)) :
  X26Legacy.x26_pairwise_distant_paths d paths <-> x26_pairwise_distant_paths d paths.
Proof.
rewrite /X26Legacy.x26_pairwise_distant_paths.
setoid_rewrite x26_set_ball_compat.
reflexivity.
Qed.

Lemma x26_has_k_distant_xy_paths_compat (G : sgraph) (d k : nat) (X Y : {set G}) :
  X26Legacy.x26_has_k_distant_xy_paths d k X Y <-> x26_has_k_distant_xy_paths d k X Y.
Proof.
rewrite /X26Legacy.x26_has_k_distant_xy_paths.
setoid_rewrite x26_pairwise_distant_paths_compat.
reflexivity.
Qed.

Lemma bounded_degree_distant_induced_menger_statement_compat :
  X26Legacy.bounded_degree_distant_induced_menger_statement <->
  bounded_degree_distant_induced_menger_statement.
Proof.
rewrite /X26Legacy.bounded_degree_distant_induced_menger_statement.
setoid_rewrite x26_has_k_distant_xy_paths_compat.
reflexivity.
Qed.

(** Boolean equalities, ball by ball. *)
Lemma x111_is_transversal_compat (G : sgraph) (r : nat) (U T : {set G}) :
  X111Legacy.x111_is_transversal r U T = x111_is_transversal r U T.
Proof.
rewrite /X111Legacy.x111_is_transversal /x111_is_transversal.
by apply: eq_forallb => u; rewrite x111_ball_compat.
Qed.

Lemma x111_is_packing_compat (G : sgraph) (r : nat) (U S : {set G}) :
  X111Legacy.x111_is_packing r U S = x111_is_packing r U S.
Proof.
rewrite /X111Legacy.x111_is_packing /x111_is_packing; congr (_ && _).
by apply: eq_forallb => u; apply: eq_forallb => v; rewrite !x111_ball_compat.
Qed.

(** The same natural numbers: the arg-min over equal transversal predicates (default [[set: G]]) and the maximum over
    equal packing predicates. *)
Lemma x111_tau_compat (G : sgraph) (r : nat) (U : {set G}) :
  X111Legacy.x111_tau r U = x111_tau r U.
Proof.
rewrite /X111Legacy.x111_tau /x111_tau /arg_min /extremum.
suff -> : pick [pred T | X111Legacy.x111_is_transversal r U T & [forall (T' | X111Legacy.x111_is_transversal r U T'),
                 #|T| <= #|T'|]] =
          pick [pred T | x111_is_transversal r U T & [forall (T' | x111_is_transversal r U T'), #|T| <= #|T'|]] by [].
apply: eq_pick => T /=; rewrite x111_is_transversal_compat; congr (_ && _).
by apply: eq_forallb => T'; rewrite x111_is_transversal_compat.
Qed.

Lemma x111_nu_compat (G : sgraph) (r : nat) (U : {set G}) :
  X111Legacy.x111_nu r U = x111_nu r U.
Proof.
rewrite /X111Legacy.x111_nu /x111_nu.
by apply: eq_bigl => S; exact: x111_is_packing_compat.
Qed.

Lemma chepoi_estellon_vaxes_ball_hypergraph_transversal_statement_compat :
  X111Legacy.chepoi_estellon_vaxes_ball_hypergraph_transversal_statement <->
  chepoi_estellon_vaxes_ball_hypergraph_transversal_statement.
Proof.
rewrite /X111Legacy.chepoi_estellon_vaxes_ball_hypergraph_transversal_statement.
setoid_rewrite x111_tau_compat.
setoid_rewrite x111_nu_compat.
reflexivity.
Qed.

(** Complete X26: the frozen balls are rewritten, then B1's and B5's chain certificates and B5's complete separator. *)
Lemma x26_pairwise_distant_paths_original_compat (G : sgraph) (d : nat) (paths : seq (seq G)) :
  X26Original.x26_pairwise_distant_paths d paths <-> x26_pairwise_distant_paths d paths.
Proof.
rewrite /X26Original.x26_pairwise_distant_paths.
setoid_rewrite x26_set_ball_compat.
exact: B1.x26_pairwise_distant_paths_compat d paths.
Qed.

Lemma x26_has_k_distant_xy_paths_original_compat (G : sgraph) (d k : nat) (X Y : {set G}) :
  X26Original.x26_has_k_distant_xy_paths d k X Y <-> x26_has_k_distant_xy_paths d k X Y.
Proof.
rewrite /X26Original.x26_has_k_distant_xy_paths.
setoid_rewrite x26_pairwise_distant_paths_original_compat.
exact: B5.x26_has_k_distant_xy_paths_compat d k X Y.
Qed.

Lemma bounded_degree_distant_induced_menger_statement_original_compat :
  X26Original.bounded_degree_distant_induced_menger_statement <->
  bounded_degree_distant_induced_menger_statement.
Proof.
rewrite /X26Original.bounded_degree_distant_induced_menger_statement.
setoid_rewrite x26_has_k_distant_xy_paths_original_compat.
setoid_rewrite B5.x26_separates_xy_original_compat.
reflexivity.
Qed.
