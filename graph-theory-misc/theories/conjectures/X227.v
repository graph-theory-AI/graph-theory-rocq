(** * GTMisc.conjectures.X227 -- hat-guessing and independent-set rows (wave X227, 2026-09-23) *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local x227 vocabulary ***********************************************)

(** *** The hat guessing game

    [q] colours; an adversary colours the vertices; every vertex sees the colours of its
    NEIGHBOURS only and guesses its own colour; the players win a colouring when at least
    one guess is correct.  A strategy is a guessing function per vertex, and the locality
    constraint says that the guess of [v] depends only on the colours of [N(v)].  The hat
    guessing number [HG(G)] is the largest [q] for which a winning strategy exists, so
    "[HG(G) >= q]" is [x227_hat_guessing_win G q] and "[HG(G) <= m]" is
    [x227_hat_guessing_le G m]; neither needs a maximisation operator. *)

Definition x227_hat_strategy (G : sgraph) (q : nat) : Type :=
  G -> {ffun G -> 'I_q} -> 'I_q.

(** A strategy is admissible when each vertex guesses from the colours of its neighbours. *)
Definition x227_sees_only_neighbours (G : sgraph) (q : nat)
    (s : x227_hat_strategy G q) : Prop :=
  forall (v : G) (c c' : {ffun G -> 'I_q}),
    (forall u : G, u -- v -> c u = c' u) -> s v c = s v c'.

(** The players win the [q]-colour game on [G]: some admissible strategy guesses at least
    one hat correctly on every colouring. *)
Definition x227_hat_guessing_win (G : sgraph) (q : nat) : Prop :=
  exists s : x227_hat_strategy G q,
    x227_sees_only_neighbours s /\
    forall c : {ffun G -> 'I_q}, exists v : G, s v c = c v.

(** The hat guessing number of [G] is at most [m]. *)
Definition x227_hat_guessing_le (G : sgraph) (m : nat) : Prop :=
  forall q : nat, x227_hat_guessing_win G q -> (q <= m)%N.

(** The minimum degree of [G] is exactly [d] (this forces [G] to be nonempty). *)
Definition x227_min_degree (G : sgraph) (d : nat) : Prop :=
  (forall v : G, (d <= #|N(v)|)%N) /\ (exists v : G, #|N(v)| = d).

(** *** Independent sets in a uniformly random vertex subset

    [alpha(G[W])] is the library's [α(W)] ([alpha_induced]: the independence number of the
    induced subgraph on [W] is [α(W)]).  The expectation over a BINOMIAL random subset,
    i.e. over the [2^n] subsets each with probability [2^-n], is the finite average
    [x227_stable_sum G / 2 ^ #|G|]; no probability layer is needed. *)
Definition x227_stable_sum (G : sgraph) : nat := \sum_(W : {set G}) α(W).

(** *** Rational sequences (for the blocked Levine rows)

    [p t = (a, b)] is read as the rational [a / b]. *)
Definition x227_rat_seq : Type := nat -> nat * nat.

(** Every term is a probability. *)
Definition x227_success_family (p : x227_rat_seq) : Prop :=
  forall t : nat, (0 < (p t).2)%N /\ ((p t).1 <= (p t).2)%N.

(** The sequence is non-increasing (more players never help). *)
Definition x227_nonincreasing (p : x227_rat_seq) : Prop :=
  forall t t' : nat, (t <= t')%N -> ((p t').1 * (p t).2 <= (p t).1 * (p t').2)%N.

(** The sequence tends to 0: below every positive rational from some point on. *)
Definition x227_rat_seq_to_zero (p : x227_rat_seq) : Prop :=
  forall e1 e2 : nat, 0 < e1 -> 0 < e2 ->
    eventually (fun t => ((p t).1 * e2 <= e1 * (p t).2)%N).

(** The class of winning-set families in Levine's hat problem.  This is a LABEL ONLY:
    the defining property of each class (dictatorships; intersecting families on the
    cube; balanced monotone families on the cube) is precisely what cannot be expressed
    without a probability layer over families of subsets of [{0,1}^n], which is why the
    two rows using it are BLOCKED. *)
Inductive x227_family_class : Type :=
  | x227_dictatorship
  | x227_intersecting
  | x227_monotone.

(** The recorded properties of the optimal success probability of Levine's hat problem
    with [t] players, when the winning sets range over the family class [cls]: each term
    is a probability, and the sequence is non-increasing in the number of players.  The
    class itself does no work here -- see the BLOCKED notes. *)
Definition x227_levine_success (cls : x227_family_class) (p : x227_rat_seq) : Prop :=
  x227_success_family p /\ x227_nonincreasing p.

(** ** X227 statements *****************************************************)

(** Corpus row: arxiv:1812.09752#00
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/1812.09752__00/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/1812.09752__00.json
    English statement: (Alon, Ben-Eliezer, Shangguan and Tamo 2018, Problem 1.4)
      All three of the following hold.  (i) There is a function f1 of one natural number
      such that every finite simple graph G has hat guessing number at most f1 of the
      maximum degree of G.  (ii) There is a function f2 such that every d-degenerate graph
      has hat guessing number at most f2 of d.  (iii) There is a function f3 such that
      every graph of minimum degree exactly d has hat guessing number at least f3 of d,
      and f3 of d is eventually at least M for every M, i.e. f3 tends to infinity.
    Definitions: [x227_hat_guessing_win G q] - some strategy in which every vertex guesses
      its colour from the colours of its neighbours only guesses one hat right on every
      q-colouring, i.e. HG(G) >= q (this file); [x227_hat_guessing_le G m] - every q with
      a winning q-colour strategy satisfies q <= m, i.e. HG(G) <= m (this file);
      [x227_hat_strategy], [x227_sees_only_neighbours] - a guessing function per vertex
      and its locality constraint (this file); [x227_min_degree G d] - every vertex has
      degree at least d and some vertex has degree exactly d (this file); [Delta G] -
      maximum degree (GTBase base.v); [k_degenerate G d] - every nonempty vertex set has a
      vertex of degree at most d inside it (GTBase base.v); [eventually P] - P n for all
      large enough n (GTBase asymptotics.v); [N(v)] (coq-graph-theory sgraph.v).
    Notes: modelling choices.  (1) The hat guessing number is the value of a FINITE
      perfect-information game, so "HG(G) >= q" is the plain existential over strategies
      [x227_hat_guessing_win] and "HG(G) <= m" is the universally quantified
      [x227_hat_guessing_le]; no maximisation operator and no monotonicity of the game in
      q is used, so the three parts read exactly as in the source.  (2) The locality
      constraint quantifies over colourings agreeing on the OPEN neighbourhood [N(v)], so
      the vertex v does not see its own hat.  (3) Part (iii) uses the exact minimum degree
      (some vertex realises it), which also forces G nonempty -- on the empty graph the
      winning condition "some vertex guesses right" is unsatisfiable, so an unguarded (iii)
      would be false for a trivial reason.  (4) "f3 tends to infinity" is rendered as: for
      every M, f3 d >= M for all large enough d ([eventually]); no monotonicity of f3 is
      required, matching the source.  Corpus status: partial - part (i) is known (Lovasz
      Local Lemma, HG(G) < e^Delta), (ii) and (iii) are open. *)
Definition hat_guessing_degree_degeneracy_bounds_statement : Prop :=
  [/\ (exists f1 : nat -> nat,
         forall G : sgraph, x227_hat_guessing_le G (f1 (Delta G))),
      (exists f2 : nat -> nat,
         forall (G : sgraph) (d : nat), k_degenerate G d -> x227_hat_guessing_le G (f2 d))
    & (exists f3 : nat -> nat,
         (forall (G : sgraph) (d : nat),
            x227_min_degree G d -> x227_hat_guessing_win G (f3 d)) /\
         (forall M : nat, eventually (fun d => (M <= f3 d)%N)))].

(** Corpus row: arxiv:2107.05995#00
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/2107.05995__00/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/2107.05995__00.json
    English statement: (Alon and Chizewer 2021, open problem: degeneracy bound for the hat
      guessing number)
      There is a function f of one natural number such that every d-degenerate finite
      simple graph has hat guessing number at most f of d.
    Definitions: [x227_hat_guessing_le G m] - every q for which the players win the
      q-colour hat game on G satisfies q <= m, i.e. HG(G) <= m (this file);
      [x227_hat_guessing_win], [x227_hat_strategy], [x227_sees_only_neighbours] (this
      file); [k_degenerate G d] (GTBase base.v).
    Notes: this is part (ii) of the companion Problem 1.4 (row arxiv:1812.09752#00,
      corpus edge e061), stated here on its own; the same hat-game vocabulary is used, so
      the implication of e061 is the projection recorded in implications_X227.v.  The
      source phrases it as "it seems plausible that there exists f"; the Rocq body is the
      positive assertion, as the corpus statement_text does. *)
Definition hat_guessing_degeneracy_bounded_statement : Prop :=
  exists f : nat -> nat,
    forall (G : sgraph) (d : nat), k_degenerate G d -> x227_hat_guessing_le G (f d).

(** Corpus row: arxiv:2208.06858#04
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/2208.06858__04/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/2208.06858__04.json
    English statement: (Alon, Friedgut, Kalai and Kindler 2022, Conjecture 2.9)
      For every rational a/b strictly between 0 and 1/2 there is a positive rational
      e1/e2 such that every finite simple graph G with at least one vertex whose
      independence number is exactly the fraction a/b of its order satisfies: the average,
      over all 2^n subsets W of the vertex set, of the independence number of the subgraph
      induced on W is at most (a/b - e1/e2) times the order n of G.
    Definitions: [x227_stable_sum G] - the sum over all vertex subsets W of the graph of
      the independence number of W, [\sum_(W : {set G}) α(W)] (this file); [α(A)] - the
      largest stable subset of A, which for an induced subgraph is its independence number
      ([alpha_induced], coq-graph-theory coloring.v).
    Notes: modelling choices.  (1) EXPECTATION AS A FINITE AVERAGE.  W binomial with
      p = 1/2 means W uniform over the 2^n subsets, so E_W[alpha(G[W])] is
      [x227_stable_sum G] / 2 ^ n exactly; no probability layer is needed.  (2) RATIONALS
      AND CROSS-MULTIPLICATION.  alpha = a/b and eps = e1/e2 are rationals given by pairs
      of naturals; the conclusion E_W[alpha(G[W])]/n <= a/b - e1/e2 is cross-multiplied
      into the subtraction-free nat inequality [S * (b * e2) + e1 * (b * (2^n * n)) <=
      a * e2 * (2^n * n)], which is equivalent over the rationals since b, e2, 2^n and n
      are positive.  (3) QUANTIFIER ORDER, and what is NOT imposed.  The body is the
      source's own displayed ("in other words") form: for every alpha there is a positive
      eps such that every G whose independence ratio is EXACTLY alpha satisfies
      E_W[alpha(G[W])]/n <= alpha - eps.  Second reader, 2026-09-23: this is implied by,
      but formally WEAKER than, the headline form "eps**(alpha) > 0", where the source
      sets eps**(alpha) = inf over all G with independence ratio AT LEAST alpha of
      (ratio(G) - alpha**(G)) -- that form demands in addition ONE eps uniform over every
      ratio >= alpha, equivalently the monotone non-decreasing eps** of the "in other
      words" sentence, and it is not obtained by renormalising the per-alpha form (the
      infimum that is monotone non-decreasing is the one over the LARGER ratios, and it
      can be 0 while every per-alpha gap is positive).  The two coincide unless the gap
      degenerates as the ratio grows, which is why the source calls them one assertion.
      Consequence of the choice: a proof of the source's conjecture transfers to this
      body, and a refutation of this body refutes the source; a refutation of the
      headline form alone need not refute this body.  (4) The hypothesis is
      [b * α([set: G]) = a * #|G|], i.e. the independence number is exactly alpha * n, as
      in the source ("maximum independent set of size alpha n"); the range 0 < a and
      2 * a < b is alpha in (0,1/2).  (5) [0 < #|G|] excludes the empty graph, for which
      the conclusion would be an empty statement about n = 0.  Corpus status: partial -
      proved for alpha > 1/4 (Theorem 2.10) and for regular graphs with alpha > 1/8
      (Theorem 2.11). *)
Definition independent_set_binomial_gap_statement : Prop :=
  forall a b : nat,
    0 < a -> 2 * a < b ->
    exists e1 e2 : nat,
      [/\ 0 < e1, 0 < e2 &
          forall G : sgraph,
            0 < #|G| -> b * α([set: G]) = a * #|G| ->
            x227_stable_sum G * (b * e2) + e1 * (b * (2 ^ #|G| * #|G|))
              <= a * e2 * (2 ^ #|G| * #|G|)].

(** Corpus row: arxiv:2208.06858#03
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/2208.06858__03/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/2208.06858__03.json
    English statement: (Alon, Friedgut, Kalai and Kindler 2022, Conjecture 2.8)
      PLACEHOLDER, see the Notes: the body asserts the BINOMIAL special case of the
      conjecture, i.e. the statement of Conjecture 2.9, which Conjecture 2.8 implies.
    Definitions: [independent_set_binomial_gap_statement] - the binomial gap conjecture
      (this file); [x227_stable_sum], [α(A)] (this file, coq-graph-theory coloring.v).
    Notes: BLOCKED.  The row's own quantity alpha*(G) is the supremum, over an OPTIMAL
      PARTITION of V(G)^r and over POSITIVELY CORRELATED random-subset distributions with
      Bernoulli(1/2) marginals, of the expected independence ratio of the random subset.
      That is a genuine correlated probability space over subsets (with an r-fold product
      structure and a positive-correlation constraint on increasing events), and GTBase
      has no layer for it; the finite-average trick that makes the binomial companion row
      (arxiv:2208.06858#04) expressible does not apply, since the distribution is not
      uniform and is quantified over.  The body is therefore the strictly WEAKER binomial
      instance, which the row implies (corpus edge e152), recorded as a candidate edge in
      implications_X227.v; it must NOT be read as Conjecture 2.8.  The corpus leg stays
      blocked until a correlated-distribution layer exists. *)
Definition independent_set_correlated_gap_statement : Prop :=
  independent_set_binomial_gap_statement.

(** Corpus row: arxiv:2208.06858#00
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/2208.06858__00/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/2208.06858__00.json
    English statement: (Alon, Friedgut, Kalai and Kindler 2022, Conjecture 2.1)
      PLACEHOLDER, see the Notes: the body asserts that every non-increasing sequence of
      rational probabilities labelled "intersecting" tends to 0, the label standing for
      the optimal success probability of Levine's hat problem with t players when the
      winning sets form an intersecting family on the cube.
    Definitions: [x227_rat_seq] - a sequence of rationals given as numerator/denominator
      pairs (this file); [x227_success_family p] - every term is a probability (this
      file); [x227_nonincreasing p] - the sequence does not increase (this file);
      [x227_levine_success cls p] - the recorded properties of the optimal success
      probability of Levine's hat problem for the winning-set class cls (this file);
      [x227_family_class] - the LABEL of the class, which carries no formal content (this
      file); [x227_rat_seq_to_zero p] - the sequence is below every positive rational
      from some point on (this file); [eventually] (GTBase asymptotics.v).
    Notes: BLOCKED, and refutable as written.  p_intersecting(t) is the supremum of a
      success probability over intersecting winning-set families on {0,1}^n in Levine's
      hat problem; expressing it needs a probability layer over families of subsets of
      the cube (and the absorption of the parameter n), which GTBase does not have.  The
      body therefore keeps only the two properties the corpus records -- each term is a
      probability and the sequence is non-increasing in the number of players -- and the
      class is a bare label [x227_intersecting] that does no formal work; a constant
      sequence 1/2 satisfies the hypotheses and refutes the body, so the statement is
      strictly weaker than nothing and must NOT be read as Conjecture 2.1.  The paper's
      own equivalent GRAPH form, Conjecture 2.6 on the independence ratio of Cartesian
      powers of the Kneser graph (corpus edge e150, equivalent_to), is authored in the
      same phase as arxiv:2208.06858#02 (homomorphism-theory); that row is where this
      conjecture has a faithful Rocq statement. *)
Definition levine_hat_intersecting_success_vanishes_statement : Prop :=
  forall p : x227_rat_seq,
    x227_levine_success x227_intersecting p -> x227_rat_seq_to_zero p.

(** Corpus row: arxiv:2208.06858#01
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/2208.06858__01/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/2208.06858__01.json
    English statement: (Alon, Friedgut, Kalai and Kindler 2022, Conjecture 2.2)
      PLACEHOLDER, see the Notes: the body asserts that every non-increasing sequence of
      rational probabilities labelled "balanced monotone" tends to 0, the label standing
      for the optimal success probability of Levine's hat problem with t players when the
      winning sets form a balanced monotone family on the cube.
    Definitions: [x227_levine_success cls p], [x227_family_class], [x227_rat_seq],
      [x227_success_family], [x227_nonincreasing], [x227_rat_seq_to_zero] (this file);
      [eventually] (GTBase asymptotics.v).
    Notes: BLOCKED, and refutable as written, for the same reason as the companion row
      arxiv:2208.06858#00: p_monotone(t) is the same success probability taken over all
      balanced monotone winning-set families on {0,1}^n, and the missing probability
      layer is the same.  The only difference between the two rows -- the winning-set
      class -- is carried by the inert label [x227_monotone], so the two bodies are
      logically the same proposition; the corpus implication e149 (monotone implies
      intersecting, since p_monotone >= p_intersecting) is therefore recorded in
      implications_X227.v as a candidate that is NOT evidence of anything.  Do not read
      the body as Conjecture 2.2. *)
Definition levine_hat_monotone_success_vanishes_statement : Prop :=
  forall p : x227_rat_seq,
    x227_levine_success x227_monotone p -> x227_rat_seq_to_zero p.
