(** * Hom.conjectures.X227 -- graph-products rows (wave X227, 2026-09-23) *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local x227 vocabulary ***********************************************

    Two notions are missing from coq-graph-theory / GTBase and are introduced
    here: the KNESER GRAPH on the subsets of a finite ground set (a
    homomorphism-theory object, first use in this package) and the ITERATED
    CARTESIAN POWER of a graph.  The Cartesian product itself is base's
    [cartesian_product]; the independence number is coq-graph-theory's [alpha]
    ([α(A)], coloring.v), and the independence RATIO is kept in cleared nat
    form (a numerator/denominator inequality), never as a rational. *)

Section Kneser.
Variable n : nat.

(** Vertices are the subsets of ['I_n], i.e. the points of [{0,1}^n] read as
    their supports; two DISTINCT subsets are adjacent iff they are disjoint.
    The [x != y] guard is what makes the relation irreflexive: without it the
    empty subset would carry a loop (it is disjoint from itself). *)
Definition x227_kneser_rel : rel {set 'I_n} :=
  fun x y => (x != y) && [disjoint x & y].

Lemma x227_kneser_sym : symmetric x227_kneser_rel.
Proof. by move=> x y; rewrite /x227_kneser_rel eq_sym disjoint_sym. Qed.

Lemma x227_kneser_irrefl : irreflexive x227_kneser_rel.
Proof. by move=> x; rewrite /x227_kneser_rel eqxx. Qed.

Definition x227_kneser : sgraph := SGraph x227_kneser_sym x227_kneser_irrefl.

End Kneser.

(** The [t]-th Cartesian (Hamming, box) power of [G].  The empty power is the
    one-vertex graph ['K_1], the unit of [cartesian_product], so
    [x227_box_power G 1] is [cartesian_product 'K_1 G], a copy of [G]. *)
Fixpoint x227_box_power (G : sgraph) (t : nat) : sgraph :=
  if t is t'.+1 then cartesian_product (x227_box_power G t') G else 'K_1.

(** ** X227 statements *****************************************************)

(** Corpus row: arxiv:2208.06858#02
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/2208.06858__02/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/2208.06858__02.json
    English statement: (Alon, Friedgut, Kalai, Kindler, arXiv:2208.06858, Conjecture 2.6)
      Let K(n) be the Kneser graph whose vertices are the subsets of an n-element
      set, two distinct subsets being adjacent when they are disjoint, and let
      K(n)^t denote the t-th Cartesian (Hamming) power of K(n).  Then the
      independence ratio of K(n)^t tends to 0 as first n and then t tend to
      infinity: for every positive integer q there is a threshold T such that for
      every t at least T there is a threshold n0 such that for every n at least
      n0, q times the independence number of K(n)^t is at most the number of its
      vertices.
    Definitions: [x227_kneser n] - the Kneser graph on [{set 'I_n}], distinct
      subsets adjacent iff disjoint (this file, X227.v); [x227_box_power G t] -
      the t-fold Cartesian power of G, with ['K_1] as the empty power (this file,
      X227.v), built on base's [cartesian_product] (base/theories/base.v);
      [α(A)] - the independence number, the largest size of a stable subset of A
      (coq-graph-theory coloring.v, re-exported by GTBase.base).
    Notes: MODELLING of the iterated limit.  The source reads
      lim_{t -> oo} lim_{n -> oo} alpha-bar(K(n)^{box t}) = 0 with alpha-bar the
      independence RATIO alpha/|V|.  Since the ratio lies in [0,1], the limit
      being 0 is the upper-bound half alone, and "ratio at most eps" is cleared
      of division as q * alpha <= |V| for eps = 1/q; quantifying eps over the
      reciprocals 1/q (q >= 1) is equivalent to quantifying it over all positive
      reals, because every positive eps exceeds some 1/q.  The OUTER limit is
      rendered as "exists T, forall t >= T" (not the weaker "exists t"), and the
      INNER limit as the limsup form "exists n0, forall n >= n0", so no existence
      claim about the inner limit is smuggled in: the body is exactly
      "for every eps > 0 there is T such that for every t >= T,
      limsup_n alpha-bar(K(n)^t) <= eps".  The vertex set {0,1}^n of the source is
      rendered by [{set 'I_n}] (a point of the cube read as its support), which is
      the bijection the source's own context uses. *)
Definition kneser_cartesian_power_independence_ratio_statement : Prop :=
  forall q : nat, 0 < q ->
    exists T : nat, forall t : nat, T <= t ->
      exists n0 : nat, forall n : nat, n0 <= n ->
        q * α([set: x227_box_power (x227_kneser n) t])
          <= #|x227_box_power (x227_kneser n) t|.
