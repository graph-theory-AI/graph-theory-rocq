(** * Hom.conjectures.grounding_X227 — grounding lemmas for wave X227.

    Qed-closed, axiom-free sanity results for the single X227 statement
    [kneser_cartesian_power_independence_ratio_statement] and for the two new
    primitives it introduces ([x227_kneser], [x227_box_power]).

    Per primitive: a NON-VACUITY witness (the object is inhabited / has edges)
    and a structural law the definition must satisfy (the cardinalities of the
    Kneser graph and of a Cartesian power).  Per statement: a GUARD-HAS-TEETH
    pair showing that both guards of the body are load-bearing — the [0 < q]
    hypothesis (at [q = 0] the body is trivially true) and the two thresholds
    [T] / [n0] (at [t = 0] the body FAILS for [q = 2]).  Finally the settled
    instance recorded by the source's own context, [alpha-bar(K(1)) = 1/2]. *)

From GTBase Require Import base.
From Hom.conjectures Require Import X227.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** [x227_kneser] — non-vacuity and structural laws *)

(** NON-VACUITY: as soon as the ground set is nonempty the Kneser graph really
    has an edge (the empty subset is disjoint from, and distinct from, the full
    subset).  So the carrier of the statement is not an edgeless graph. *)
Lemma x227_kneser_has_edge n : 0 < n ->
  exists x y : x227_kneser n, x -- y.
Proof.
move=> n0; exists set0, [set: 'I_n].
rewrite /edge_rel /= /x227_kneser_rel disjoints_subset sub0set andbT.
apply/eqP => /(congr1 (fun S : {set 'I_n} => #|S|)).
by rewrite cards0 cardsT card_ord => /esym/eqP; rewrite (negbTE (lt0n_neq0 n0)).
Qed.

(** STRUCTURAL LAW: the Kneser graph of the corpus row is the graph on the whole
    cube [{0,1}^n], so it has exactly [2^n] vertices. *)
Lemma card_x227_kneser n : #|x227_kneser n| = 2 ^ n.
Proof.
have <- : #|powerset [set: 'I_n]| = #|x227_kneser n| by rewrite powersetT cardsT.
by rewrite card_powerset cardsT card_ord.
Qed.

(** STRUCTURAL LAW: adjacency in the Kneser graph is exactly "distinct and
    disjoint" — the definition has both halves, and the second is what the
    source calls "supports disjoint". *)
Lemma x227_kneser_adj n (x y : x227_kneser n) :
  x -- y -> (x != y) /\ [disjoint x & y].
Proof. by rewrite /edge_rel /= /x227_kneser_rel => /andP[]. Qed.

(** ** [x227_box_power] — structural laws *)

(** The empty power is the one-vertex graph. *)
Lemma x227_box_power0 (G : sgraph) : x227_box_power G 0 = 'K_1.
Proof. by []. Qed.

(** STRUCTURAL LAW: the [t]-th Cartesian power has [#|G| ^ t] vertices — the
    denominator of the independence ratio of the statement. *)
Lemma card_x227_box_power (G : sgraph) t : #|x227_box_power G t| = #|G| ^ t.
Proof.
elim: t => [|t IH] /=; first by rewrite card_ord.
by rewrite card_prod IH expnS mulnC.
Qed.

(** ** The independence ratio is a genuine ratio *)

(** The independence number never exceeds the number of vertices, so the cleared
    inequality [q * α <= #|V|] of the statement really says
    "independence ratio at most 1/q". *)
Lemma x227_alphaT_leq_card (G : sgraph) : α([set: G]) <= #|G|.
Proof.
case: alphaP => S /maxstabsetS SsubT.
by rewrite -[#|G|]cardsT; exact: subset_leq_card.
Qed.

(** ** Guards have teeth *)

(** The one-vertex graph has independence number 1. *)
Lemma x227_alpha_K1 : α([set: 'K_1]) = 1.
Proof.
apply/eqP; rewrite eqn_leq; apply/andP; split.
  by apply: leq_trans (x227_alphaT_leq_card _) _; rewrite card_ord.
have H : #|[set ord0] : {set 'K_1}| <= α([set: 'K_1]).
  by apply: stabset_bound; rewrite inE subsetT stable1.
by rewrite cards1 in H.
Qed.

(** TEETH #1 — the thresholds are load-bearing: at [t = 0] the Cartesian power
    is the single vertex ['K_1], whose independence ratio is 1, so the body of
    the statement is FALSE there for every [q >= 2].  The existential [T] (and
    with it the whole "for large t" reading) is therefore doing real work. *)
Lemma x227_body_fails_at_t0 n :
  ~ (2 * α([set: x227_box_power (x227_kneser n) 0])
       <= #|x227_box_power (x227_kneser n) 0|).
Proof. by rewrite x227_box_power0 x227_alpha_K1 card_ord. Qed.

(** TEETH #2 — the [0 < q] guard is load-bearing: at [q = 0] the body holds for
    every [t] and every [n], so without the guard the statement would be
    vacuously true. *)
Lemma x227_body_trivial_at_q0 t n :
  0 * α([set: x227_box_power (x227_kneser n) t])
    <= #|x227_box_power (x227_kneser n) t|.
Proof. by []. Qed.

(** ** Settled instance recorded by the source's context *)

(** In [{set 'I_1}] there are exactly two subsets. *)
Lemma x227_I1_set (z : {set 'I_1}) : (z == set0) || (z == [set: 'I_1]).
Proof.
have ord1 : forall i : 'I_1, i = ord0 by move=> i; apply: val_inj; case: i => -[].
case: (boolP (ord0 \in z)) => [z0|z0]; apply/orP; [right|left]; apply/eqP.
- by apply/setP => i; rewrite inE (ord1 i).
- by apply/setP => i; rewrite inE (ord1 i) (negbTE z0).
Qed.

(** [K(1)] is the complete graph on its two vertices. *)
Lemma x227_kneser1_complete (x y : x227_kneser 1) : x != y -> x -- y.
Proof.
rewrite /edge_rel /= /x227_kneser_rel => xy; rewrite xy /=.
case/orP: (x227_I1_set x) => /eqP xE;
  first by rewrite xE disjoints_subset sub0set.
case/orP: (x227_I1_set y) => /eqP yE; last by move: xy; rewrite xE yE eqxx.
by rewrite yE disjoint_sym disjoints_subset sub0set.
Qed.

(** SETTLED CASE (source context: p_intersecting(t,n) = alpha-bar(K(n)^{box t}),
    and p_intersecting(1,1) = 1/2): the independence ratio of [K(1)] is exactly
    1/2, i.e. [2 * α = #|V|].  This is the first point of the sequence whose
    double limit the conjecture claims to be 0. *)
Lemma x227_kneser1_ratio : 2 * α([set: x227_kneser 1]) = #|x227_kneser 1|.
Proof.
rewrite card_x227_kneser expn1.
suff -> : α([set: x227_kneser 1]) = 1 by [].
apply/eqP; rewrite eqn_leq; apply/andP; split; last first.
  have H : #|[set set0] : {set x227_kneser 1}| <= α([set: x227_kneser 1]).
    by apply: stabset_bound; rewrite inE subsetT stable1.
  by rewrite cards1 in H.
case: alphaP => S /maxstabset_stable /stableP Sst.
rewrite leqNgt; apply/negP => /card_gt1P[x [y [xS yS xy]]].
by move: (Sst x y xS yS); rewrite x227_kneser1_complete.
Qed.

Print Assumptions kneser_cartesian_power_independence_ratio_statement.
Print Assumptions x227_kneser1_ratio.
Print Assumptions x227_body_fails_at_t0.
