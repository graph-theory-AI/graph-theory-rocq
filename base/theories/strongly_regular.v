(** * GTBase.strongly_regular -- strongly regular parameters and their two existential wrappers

    [strongly_regular_parameters G k lam mu]: [G] is [k]-regular ([GTBase.base.regular]), every adjacent pair has
    exactly [lam] common neighbours and every pair of distinct non-adjacent vertices has exactly [mu]
    ([GTBase.base.common_nbr]).  No guard is added: on degenerate graphs the parameters are not functions of [G] (the
    empty graph satisfies every triple, [K_2] satisfies [(1, 0, mu)] for every [mu], an edgeless graph [(0, lam, 0)]
    for every [lam]); they are unique only under the hypotheses of the three uniqueness lemmas below.
    Two distinct existential wrappers, never identified:
    - [has_strongly_regular_parameters G]: some triple, unguarded; it accepts [K_2], complete graphs, edgeless graphs,
      disjoint unions of cliques and the empty graph;
    - [connected_nontrivial_strongly_regular G]: some triple with exactly the guards [connected [set: G]], [0 < k] and
      [k < #|G|.-1] (nat predecessor, so [#|G| >= 3]); it excludes all the degenerate graphs above, while [K_{2,2}]
      with [(2, 0, 2)] satisfies it.
    Only the guarded-to-unguarded direction holds ([connected_nontrivial_strongly_regularW]).  The adjacency-matrix
    identity [A^2 = k I + lam A + mu (J - I - A)] is Spectral's ([Spectral.foundations.strongly_regular_matrix]);
    GTBase does not depend on the spectral layer.  Registry: meta/library_primitives/strongly-regular.json (A33). *)
From GTBase Require Import base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** The three unguarded parameter clauses. *)
Definition strongly_regular_parameters (G : sgraph) (k lam mu : nat) : Prop :=
  [/\ regular G k,
      (forall x y : G, x -- y -> #|common_nbr x y| = lam)
    & (forall x y : G, x != y -> ~~ x -- y -> #|common_nbr x y| = mu)].

(** Some parameters, with no guard. *)
Definition has_strongly_regular_parameters (G : sgraph) : Prop :=
  exists k lam mu : nat, strongly_regular_parameters G k lam mu.

(** Some parameters of a connected graph whose degree lies strictly between [0] and [#|G|.-1]. *)
Definition connected_nontrivial_strongly_regular (G : sgraph) : Prop :=
  exists k lam mu : nat,
    [/\ connected [set: G], (0 < k)%N /\ (k < (#|G|).-1)%N & strongly_regular_parameters G k lam mu].

Section StronglyRegularAPI.
Variable G : sgraph.

Lemma strongly_regular_parameters_regular k lam mu :
  strongly_regular_parameters G k lam mu -> regular G k.
Proof. by case. Qed.

(** The degree is unique on an inhabited graph, [lam] once some edge exists, [mu] once some distinct non-adjacent pair
    exists. *)
Lemma strongly_regular_parameters_degree_unique (v : G) k lam mu k' lam' mu' :
  strongly_regular_parameters G k lam mu -> strongly_regular_parameters G k' lam' mu' -> k = k'.
Proof. by case=> rk _ _ [rk' _ _]; rewrite -(rk v) (rk' v). Qed.

Lemma strongly_regular_parameters_lambda_unique (x y : G) k lam mu k' lam' mu' :
  x -- y -> strongly_regular_parameters G k lam mu -> strongly_regular_parameters G k' lam' mu' -> lam = lam'.
Proof. by move=> xy [_ hl _] [_ hl' _]; rewrite -(hl x y xy) (hl' x y xy). Qed.

Lemma strongly_regular_parameters_mu_unique (x y : G) k lam mu k' lam' mu' :
  x != y -> ~~ x -- y ->
  strongly_regular_parameters G k lam mu -> strongly_regular_parameters G k' lam' mu' -> mu = mu'.
Proof. by move=> xy nxy [_ _ hm] [_ _ hm']; rewrite -(hm x y xy nxy) (hm' x y xy nxy). Qed.

Lemma connected_nontrivial_strongly_regularW :
  connected_nontrivial_strongly_regular G -> has_strongly_regular_parameters G.
Proof. by case=> k [lam] [mu] [_ _ P]; exists k, lam, mu. Qed.

Lemma connected_nontrivial_strongly_regular_connected :
  connected_nontrivial_strongly_regular G -> connected [set: G].
Proof. by case=> k [lam] [mu] []. Qed.

Lemma connected_nontrivial_strongly_regular_regular :
  connected_nontrivial_strongly_regular G -> exists k, regular G k.
Proof. by case=> k [lam] [mu] [_ _ [rk _ _]]; exists k. Qed.

(** The degree guard forces at least three vertices. *)
Lemma connected_nontrivial_strongly_regular_card :
  connected_nontrivial_strongly_regular G -> 2 < #|G|.
Proof.
case=> k [lam] [mu] [_ [k0 kn] _].
have : 1 < #|G|.-1 by exact: leq_ltn_trans k0 kn.
by case: #|G| => [|[|[|n]]].
Qed.

End StronglyRegularAPI.
