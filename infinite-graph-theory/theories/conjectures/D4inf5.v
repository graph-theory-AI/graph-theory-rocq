(** * Infinite.conjectures.D4inf5 — colouring the odd-distance graph (PARTIAL).

    The Odd Distance Graph O has vertex set ℝ² with two points adjacent iff their
    distance is an odd integer.  We ask whether χ(O) = ∞.

    Carrier: an [iGraph] on [R * R] over an abstract REAL-CLOSED field [R]
    ([rcfType], not axiom-laden Stdlib [Reals]); the edge is sqrt-free —
    [∃ m, odd m ∧ (Δx)² + (Δy)² = (m:R)²].

    PARTIAL (two labelled proxies):
    (1) READING-2.  χ(O) = ∞ is rendered as "the finite subgraphs have unbounded
        chromatic number": for every [n] there is a FINITE point set not properly
        [n]-colourable.  This implies χ(O) = ∞; the converse is De Bruijn–Erdős,
        which needs choice — so this is the choice-free direction, formally
        stronger than (hence a faithful proxy for) the literal χ = ∞.
    (2) FIELD-GENERIC.  Quantifying [forall R : rcfType] is a proxy for the
        specific field ℝ (colourings are second-order, so no Tarski transfer). *)

From GTBase Require Export base.
From Infinite Require Import foundations.igraph.
From mathcomp Require Import all_boot all_algebra.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section OddDistance.
Variable R : rcfType.
Definition oddpt := (R * R)%type.

(** Two points are at ODD-INTEGER distance (squared, to avoid a square root). *)
Definition odd_dist (p q : oddpt) : Prop :=
  exists m : nat, odd m /\ (p.1 - q.1) ^+ 2 + (p.2 - q.2) ^+ 2 = (m%:R) ^+ 2.

Lemma odd_dist_sym : irel_sym odd_dist.
Proof.
move=> p q [m [Hm E]]; exists m; split=> //.
by rewrite -[q.1 - p.1]opprB sqrrN -[q.2 - p.2]opprB sqrrN.
Qed.

Lemma odd_dist_irr : irel_irr odd_dist.
Proof.
move=> p [m [Hm E]].
have H2 : (m%:R : R) ^+ 2 == 0 by rewrite -E !subrr !expr2 !mulr0 addr0.
move: H2; rewrite expf_eq0 pnatr_eq0 => /andP[_ /eqP m0].
by move: Hm; rewrite m0.
Qed.

Definition OddG : iGraph := Build_iGraph odd_dist_sym odd_dist_irr.

(** A finite point set [S] is properly [n]-colourable in O. *)
Definition n_colorable (S : seq oddpt) (n : nat) : Prop :=
  exists c : oddpt -> 'I_n,
    forall p q, p \in S -> q \in S -> odd_dist p q -> c p <> c q.

End OddDistance.

Arguments odd_dist {R} p q.
Arguments n_colorable {R} S n.

(** Corpus row: opg:coloring_the_odd_distance_graph
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/coloring_the_odd_distance_graph/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/coloring_the_odd_distance_graph.json
    English statement: (Open Problem Garden, "Coloring the Odd Distance Graph")
      The Odd Distance Graph has the points of the plane as vertices, two points
      adjacent when their distance is an odd integer; the question is whether
      its chromatic number is infinite.  Back-translating the Rocq body: for
      every real-closed field R and every number of colours n there is a finite
      list S of points of R x R that is not properly n-colourable - no map from
      points to n colours gives different colours to every two points of S whose
      squared distance is the square of an odd natural number.
    Definitions: [oddpt] - a point, an element of R x R (this file, D4inf5.v);
      [odd_dist p q] - there is an odd natural m with
      (p1 - q1)^2 + (p2 - q2)^2 = m^2, the sqrt-free form of "the distance is an
      odd integer" (D4inf5.v); [OddG] - the resulting [iGraph] (D4inf5.v);
      [n_colorable S n] - S admits a proper colouring by 'I_n for the
      odd-distance relation (D4inf5.v); [iGraph]/[irel_sym]/[irel_irr]
      (infinite-graph-theory/theories/foundations/igraph.v).
    Notes: PARTIAL, two labelled PROXIES.  (1) READING: "chromatic number is
      infinite" is rendered as "the finite subgraphs have unbounded chromatic
      number".  This IMPLIES the literal statement; the converse is
      De Bruijn-Erdos and needs choice, so the choice-free direction chosen here
      is formally stronger.  (2) FIELD-GENERIC: quantifying over every
      [rcfType] is a proxy for the specific field of real numbers - colourings
      are second-order, so Tarski transfer does not apply - and again makes the
      statement formally stronger.  Distance is kept squared to avoid a square
      root, which is exact for odd-integer distances. *)
Definition coloring_the_odd_distance_graph_statement : Prop :=
  forall (R : rcfType) (n : nat), exists S : seq (R * R), ~ n_colorable S n.
