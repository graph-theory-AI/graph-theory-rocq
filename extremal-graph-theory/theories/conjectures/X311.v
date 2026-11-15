(** * Extremal.conjectures.X311 -- v2 row: the Friedgut-Kalai-Kindler hitting conjecture (pairwise disjoint k-sets,
      covering a positive fraction of the vertices, each meeting every maximum independent set) *)

From GTBase Require Import base common.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** X311 statement ********************************************************* *)

(** Corpus row: studies:std_friedgut_kalai_kindler_conjectures
    Site: none
    Review: none
    English statement: (Friedgut, Kalai and Kindler's conjecture; studies slice of the corpus, record arXiv:2103.05998)
      For every alpha in (0, 1/2) there exists k and tau > 0 such that if G is a graph on n vertices with maximum
      independent set of size alpha n, then there exist pairwise disjoint subsets of vertices A_1, A_2, ..., A_r in G
      such that (1) |A_i| = k for all i, (2) |A_1 u ... u A_r| >= tau n, (3) every maximum independent set in G
      intersects every set A_i.
    Definitions: [stable S] - no two vertices of S are adjacent (coq-graph-theory); α([set: G]) - the independence
      number of G, the largest size of a stable set (coq-graph-theory); [cover F] - the union of the sets of the
      family F (MathComp finset); [disjoint A & B] - A and B have no common vertex (MathComp).
    Notes: encoded as stated.  alpha = p / q and tau = s / t with natural numbers: for a finite graph alpha(G) / n is
      rational, so for an irrational alpha only the graph with no vertex meets the hypothesis, where the empty family
      satisfies (1)-(3); and a smaller positive rational tau only weakens (2).  So the natural-number ratios are
      equivalent to the real parameters.  0 < p and 2 p < q say alpha in (0, 1/2); "maximum independent set of size
      alpha n" is q * alpha(G) = p * n.  k is a positive integer: (2) and (3) force a nonempty family of nonempty sets
      for every graph with a vertex, so k = 0 could serve only the empty graph.  The sets A_1, ..., A_r form a family
      F of vertex sets, pairwise disjoint, with union cover F; pairwise disjoint sets of size k > 0 are distinct, so a
      set of sets loses nothing against a sequence.  "Maximum independent set" is a stable S with #|S| = alpha(G).
      Source: the conjecture is Friedgut, Kalai and Kindler's (their Conjecture 3.1), restated word for word by Alon,
      "Hitting all maximum independent sets", arXiv:2103.05998v2 (4 April 2021), main.tex l.75-92.  Status: pinned
      open, but refuted at the pin in its own record: "Here we show that this is false for every fixed alpha in
      (0,1/2) even if the requirement (2) is omitted, but that the assertion does hold for any alpha > 1/2"
      (l.93-95); Theorems 1.3 and 1.4 (l.113-126; "counterexamples", l.127-128): the shift graph G_k on 2k(2k-1)
      vertices with independence number k^2 and no set of k vertices meeting all its maximum independent sets
      (l.197-224), and a Cayley graph of Z_2^m.  No kernel disproof here.  The status correction is a separate
      corpus item. *)
Definition friedgut_kalai_kindler_maximum_independent_set_hitting_statement : Prop :=
  forall p q : nat, 0 < p -> 2 * p < q ->
    exists k s t : nat, [/\ 0 < k, 0 < s, 0 < t &
      forall G : sgraph, q * α([set: G]) = p * #|G| ->
        exists F : {set {set G}},
          [/\ {in F &, forall A B : {set G}, A != B -> [disjoint A & B]},
              {in F, forall A : {set G}, #|A| = k},
              s * #|G| <= t * #|cover F| &
              forall S : {set G}, stable S -> #|S| = α([set: G]) ->
                {in F, forall A : {set G}, ~~ [disjoint S & A]}]].
