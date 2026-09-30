(** * Topological.conjectures.D3cr — milestone D3cr (namespace Topological, plan v4)

    Statement-only formalizations (axiom-free: no Conjecture/Axiom/Parameter/
    Admitted) of four crossing-number conjectures.

    CROSSING NUMBER.  All four rows are about the crossing number [cr(G)].  We use
    the axiom-free combinatorial split-planarization proxy from
    [Topological.foundations.crossing]:

      [is_crossing_number G n]  :  n is the least number of "crossing splits"
                                   (degree-4 resolutions of two independent edges)
                                   that planarize G onto base's [wagner_planar].

    This needs NO geometry / drawings / surfaces / faces / point-sets and NO
    planarity stack (it bottoms out at the Wagner no-K5/K3,3-minor predicate), and
    it is grounded there by:  [crossing_number0] (split-cr = 0 ⇔ planar, both ways),
    [wagner_planar_sub] (planarity subgraph-closed — the base case of cr
    monotonicity), and [not_wagner_planar_K5] ⇒ [is_crossing_number_K5] (cr(K5) ≥ 1).
    See crossing.v for why cr is exposed RELATIONALLY (a total [nat]-valued cr
    would need a finite-drawing/geometry existence fact, excluded here) and for the
    honest note on the full subgraph-monotonicity (open in this model).
    [is_crossing_number] is FUNCTIONAL ([is_crossing_number_uniq]).

    STATUS.  The rows are stated in DIRECT, NON-VACUOUS form, but are recorded as
    PARTIAL after the #5/#6 readback review: the [xsplit] model lacks local
    drawing rotation/alternation data at crossing vertices, so equivalence to the
    usual drawing crossing number is not yet validated.  Rows 1–2 assert
    [is_crossing_number <carrier> <formula>] outright — the conjectured split
    value both achievable and minimal, no inhabitance gate (the former
    [forall v, is_crossing_number _ v -> v = _] shape was vacuity-conditional).
    Row 3 uses the sub-level comparison of minima ([forall k achievable for G,
    exists j <= k achievable for K_t] — robust to the exactly-k non-monotonicity
    of [crossing_planar_in]); Row 4 states the 5/32 limit two-sidedly on the
    achievable counts.  No totality theorem is needed: each existence half is part
    of the conjecture's own claim.

    CARRIERS (per row.rocq_idiom): complete-bipartite [KB m n], complete ['K_n],
    arbitrary [sgraph], and the hypercube [hypercube d] (= iterated cartesian power
    of ['K_2], built on base's [cartesian_product]).

    NEW AREA PRIMITIVES: crossing notions live in crossing.v (area-local
    planarization invariant).  [hypercube] is defined here; it is a generic graph
    family (not crossing-specific), tagged [@MOVE-to-base] for promotion once a
    second area needs it. *)

From Topological Require Import foundations.crossing.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** The d-dimensional hypercube Q_d: vertices are binary strings of length d, two
    adjacent iff they differ in exactly one coordinate.  Equivalently the d-fold
    cartesian (box) power of K_2 (Q_0 = K_1, Q_{d+1} = K_2 □ Q_d).  Reuses base's
    [cartesian_product] (□).  [@MOVE-to-base]: generic graph family.

    NB. base's [graph_power] is NOT the right primitive here: it is the DISTANCE
    power (same vertex set, vertices adjacent iff joined by a walk of length ≤ m,
    via [pow_rel]), not the cartesian/box power.  Hence the local fixpoint over
    [cartesian_product] is the correct construction, not a redefinition of an
    existing base primitive.  Grounding (witness + textbook identities — base case
    Q_0 = K_1, recurrence, and #|Q_d| = 2^d) is in [grounding_D3cr]. *)
Fixpoint hypercube (d : nat) : sgraph :=
  match d with
  | 0 => 'K_1
  | d'.+1 => cartesian_product 'K_2 (hypercube d')
  end.

(** Corpus row: opg:the_crossing_number_of_the_complete_bipartite_graph
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/the_crossing_number_of_the_complete_bipartite_graph/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/the_crossing_number_of_the_complete_bipartite_graph.json
    English statement: (Open Problem Garden, "The Crossing Number of the Complete Bipartite
      Graph"; Zarankiewicz's conjecture)
      For all naturals m and n, the crossing number of the complete bipartite graph K(m,n)
      equals the product of the floors of m/2, (m-1)/2, n/2 and (n-1)/2.  In the Rocq body
      this is the assertion that exactly that many crossing splits planarize K(m,n) and that
      no smaller number of splits does.
    Definitions: [is_crossing_number G n] - n is the LEAST k such that k successive
      "crossing splits" (each replacing two vertex-disjoint edges a-b and c-d by a new
      degree-4 vertex joined to a, b, c, d) turn G into a graph with no K5 and no K3,3 minor
      (topological-graph-theory/theories/foundations/crossing.v, on top of [wagner_planar],
      base/theories/base.v); [KB m n] - the complete bipartite graph (coq-graph-theory
      sgraph.v).  Floors are nat division.
    Notes: PARTIAL PROXY.  The crossing number is the axiom-free split-planarization
      invariant of crossing.v, not the drawing crossing number: the #5/#6 readback review
      found the model lacks the local rotation/alternation data at each new degree-4
      crossing vertex, so equality with the usual cr is not validated (the split value is at
      least well defined - [is_crossing_number_uniq] - and grounded by
      [crossing_number0]: split-cr = 0 iff planar, [wagner_planar_sub], and
      [is_crossing_number_K5]).  A total nat-valued cr is deliberately avoided: totality
      would need "every finite graph admits a finite-crossing drawing", i.e. geometry, which
      this layer excludes; hence the relational form.  The statement is stated DIRECTLY
      (not gated on inhabitance), so both achievability of the Zarankiewicz value and its
      minimality are part of the claim and the row is non-vacuous. *)
Definition the_crossing_number_of_the_complete_bipartite_graph_statement : Prop :=
  forall m n : nat,
    is_crossing_number (KB m n)
      ((m %/ 2) * ((m - 1) %/ 2) * (n %/ 2) * ((n - 1) %/ 2)).

(** Corpus row: opg:the_crossing_number_of_the_complete_graph
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/the_crossing_number_of_the_complete_graph/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/the_crossing_number_of_the_complete_graph.json
    English statement: (Open Problem Garden, "The Crossing Number of the Complete Graph";
      Guy's conjecture)
      For every natural n, the crossing number of the complete graph on n vertices equals one
      quarter of the product of the floors of n/2, (n-1)/2, (n-2)/2 and (n-3)/2.  In the Rocq
      body this is the assertion that exactly that many crossing splits planarize K_n and
      that no smaller number of splits does.
    Definitions: [is_crossing_number G n] - the least number of crossing splits planarizing
      G, relational (topological-graph-theory/theories/foundations/crossing.v); ['K_n] - the
      complete graph (coq-graph-theory sgraph.v).  Floors and the quarter are nat division.
    Notes: PARTIAL PROXY - same split-planarization model and same missing
      rotation/alternation layer as the Zarankiewicz row above; equality with the drawing
      crossing number is not validated.  ARITHMETIC ASSUMPTION: the Guy product is divisible
      by 4 (checked for all n in the literature), and the encoding relies on it - the
      division [_ %/ 4] is nat division and would silently truncate were divisibility ever to
      fail.  Stated directly, so achievability (Guy's construction) and minimality (the open
      half) are both part of the claim. *)
Definition the_crossing_number_of_the_complete_graph_statement : Prop :=
  forall n : nat,
    is_crossing_number 'K_n
      (((n %/ 2) * ((n - 1) %/ 2) * ((n - 2) %/ 2) * ((n - 3) %/ 2)) %/ 4).

(** Corpus row: opg:crossing_numbers_and_coloring
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/crossing_numbers_and_coloring/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/crossing_numbers_and_coloring.json
    English statement: (Open Problem Garden, "Crossing numbers and coloring"; Albertson's
      conjecture)
      Corpus claim: every graph G whose chromatic number is at least t satisfies
      cr(G) >= cr(K_t).  Back-translation of the Rocq body: for every finite simple graph G
      and all naturals t and k, if t is at most the chromatic number of G and k crossing
      splits planarize G, then some j <= k crossing splits planarize the complete graph K_t.
    Definitions: [crossing_planar_in k G] - EXACTLY k successive crossing splits turn G into
      a graph with no K5 and no K3,3 minor
      (topological-graph-theory/theories/foundations/crossing.v); the chromatic number is
      coq-graph-theory's [chi(A)] taken on the full vertex set; ['K_t] - the complete graph.
    Notes: PARTIAL PROXY (split-planarization model, see the two rows above).  The source
      inequality cr(K_t) <= cr(G) is rendered at the level of ACHIEVABLE split counts rather
      than of the two minima: [crossing_planar_in] counts EXACT split numbers and is not
      monotone in k, so "every count achievable for G dominates some count achievable for
      K_t" is the correct rendering of the comparison of minima; the [exists j <= k] (rather
      than exactly k) is deliberate.  The form has content for every planarizable G, with no
      inhabitance gate. *)
Definition crossing_numbers_and_coloring_statement : Prop :=
  forall (G : sgraph) (t k : nat),
    (t <= χ([set: G]))%N ->
    crossing_planar_in k G ->
    exists j : nat, (j <= k)%N /\ crossing_planar_in j 'K_t.

(** Corpus row: opg:the_crossing_number_of_the_hypercube
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/the_crossing_number_of_the_hypercube/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/the_crossing_number_of_the_hypercube.json
    English statement: (Open Problem Garden, "The Crossing Number of the Hypercube")
      Corpus claim: cr(Q_d)/4^d tends to 5/32, where Q_d is the d-dimensional hypercube (its
      vertices are the binary strings of length d, two being adjacent when they differ in
      exactly one coordinate).  Back-translation of the Rocq body: for every positive
      rational epsilon = eps_num/eps_den there is an N such that for every d >= N, (i) some
      split count k planarizes Q_d with eps_den * |32k - 5*4^d| < eps_num * 32 * 4^d, and
      (ii) every split count k that planarizes Q_d satisfies
      eps_den * 5 * 4^d < eps_den * 32 * k + eps_num * 32 * 4^d.
    Definitions: [crossing_planar_in k G] - exactly k crossing splits planarize G
      (topological-graph-theory/theories/foundations/crossing.v); [hypercube d] - Q_d as the
      d-fold cartesian (box) power of ['K_2] over base's [cartesian_product], with Q_0 = 'K_1
      (this file).
    Notes: PARTIAL PROXY (split-planarization model; see the rows above).  The limit is
      written in cross-multiplied epsilon-N form over the naturals, with the absolute value
      expressed as the sum of the two truncated nat subtractions.  Clause (i) carries BOTH
      the upper bound and the achievability half (existence of a planarizing count in the
      window); clause (ii) is the lower bound and is the only one quantified over ALL
      achievable counts - one-sided on purpose, since counts above the minimum are
      legitimate.  Together they pin the minimum into the epsilon window.  [hypercube] is not
      base's [graph_power] (that is the DISTANCE power, not the cartesian power); it is
      tagged @MOVE-to-base as a generic graph family, with witnesses and the identities
      Q_0 = 'K_1, the recurrence and |Q_d| = 2^d proved in grounding_D3cr.v. *)
Definition the_crossing_number_of_the_hypercube_statement : Prop :=
  forall (eps_num eps_den : nat),
    (0 < eps_num)%N -> (0 < eps_den)%N ->
    exists N : nat,
      forall d : nat,
        (N <= d)%N ->
        (exists k : nat,
            crossing_planar_in k (hypercube d) /\
            (eps_den * ((32 * k - 5 * 4 ^ d) + (5 * 4 ^ d - 32 * k))
               < eps_num * (32 * 4 ^ d))%N) /\
        (forall k : nat,
            crossing_planar_in k (hypercube d) ->
            (eps_den * (5 * 4 ^ d)
               < eps_den * (32 * k) + eps_num * (32 * 4 ^ d))%N).
