(** * Chromatic.conjectures.X273 -- wave X273: many 3-colourings of triangle-free planar graphs, the chromatic number
    of Alon's graph G_(m,t), and a nine-colour set colouring with five colours at one vertex (2026-11-01)

    A three-row wave under the prospective contract of meta/faithfulness_policy.json.  Rows: arxiv:2108.12669#00
    (Conjecture 1 of Dvorak and Postle: some c > 1 such that every n-vertex triangle-free planar graph has at least
    c^(n^(log_(9/2) 3)) proper 3-colourings), arxiv:2103.05998#00 (Alon: the chromatic number of G_(m,t) is
    Theta(t^2)) and arxiv:1809.05439#00 (Dvorak and Hu: every triangle-free planar graph with a vertex x has a set
    colouring by subsets of {1, ..., 9} with at least three colours at every vertex and five at x).
    Shared vocabulary: GTBase's [wagner_planar], [triangle_free] (base.v), [fg_mk_sgraph] (finite_graph.v) and
    [proper_colouring] (colourings.v); coq-graph-theory's chromatic number.
    Local helper: Alon's graph [x273_alon].
    Pinned statuses: all three open; literature lines are dated against the corpus pin (graph-conjectures b72c5857,
    2026-09-23).  The sources are the Mac's deposits coordination/sources/x272-source-mac-20261031 (2108.12669v1)
    and x273-source-mac-20261101 (2103.05998v2, 1809.05439v1; TeX line numbers below).  The grounding certificates
    are in grounding_X273.v. *)

From GTBase Require Import base common colourings.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** X273 vocabulary ********************************************************* *)

(** Alon's graph G_(m,t) (arXiv:2103.05998v2, proof of Theorem 1.4, main.tex l.228-232): the binary vectors of
    length m, two of them adjacent iff the Hamming distance between them exceeds m - 2t.  A vector is a map
    'I_m -> bool and the Hamming distance of u and v is the number of coordinates where they differ.  [fg_mk_sgraph]
    takes the symmetric irreflexive closure, which changes nothing here: the relation is symmetric, and a vector is
    at distance 0 from itself, which never exceeds m - 2t.  The subtraction m - 2t is truncated at 0 (then the graph
    is complete); the statement's guards 0 < t and 4 t^2 <= m give 2t <= m, where it is exact. *)
Definition x273_alon (m t : nat) : sgraph :=
  fg_mk_sgraph (fun u v : {ffun 'I_m -> bool} => m - 2 * t < #|[set i | u i != v i]|).

(** ** X273 statements ********************************************************* *)

(** Corpus row: arxiv:2108.12669#00
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/2108.12669__00/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/2108.12669__00.json
    English statement: (Dvorak and Postle, Conjecture 1)
      There exists a constant c > 1 such that every n-vertex triangle-free planar graph has at least
      c^(n^(log_(9/2) 3)) distinct proper 3-colorings.
    Definitions: [wagner_planar G] - G has neither K_5 nor K_(3,3) as a minor (GTBase base.v); [triangle_free G] - no
      three mutually adjacent vertices (GTBase base.v); [proper_colouring f] - adjacent vertices get different
      colours (GTBase colourings.v); #|[set f : {ffun G -> 'I_3} | proper_colouring f]| - the number N of proper
      colourings of G with the three labelled colours of 'I_3.
    Notes: encoded in natural numbers, equivalent to the statement; pinned status open.  It is Conjecture 1 of Dvorak
      and Postle (arXiv:2108.12669v1, 28 August 2021, bebound.tex l.68-71), after their Theorem 1
      (l.60-63): for infinitely many n, an n-vertex triangle-free planar graph with at most 64^(n^alpha)
      3-colourings, alpha = log_(9/2) 3 = 0.7304; the conjecture says this exponent is tight.  Stdlib's reals are not
      used: R, Rpower and ln depend on four axioms (ClassicalDedekindReals and functional extensionality), which the
      axiom-free gate refuses (meta/v2_reconciliation.json, followups_axiom_dependent).  The body replaces c by k
      with c^k >= 2, the irrational alpha by the rationals a / b below it (9^a < 3^b * 2^a iff (9/2)^a < 3^b; b = 0
      never satisfies it), and n^alpha by the integers m <= n^(a/b) (m^b <= n^a).  Equivalence: given c, take k with
      c^k >= 2; then m <= n^(a/b) <= n^alpha gives 2^m <= c^(k m) <= N^k.  Given k, take c = 2^(1/(2k)): the instance
      a = 0, m = 1 gives N >= 2 >= c^(n^alpha) when n^alpha < 2; when n^alpha >= 2, m = ceil(n^alpha) - 1 is below
      n^alpha, so m <= n^(a/b) for some a / b < alpha, and m >= n^alpha / 2 gives N >= 2^(m/k) >= c^(n^alpha).
      "Distinct proper 3-colorings" are labelled, maps G -> 'I_3, as X272 counts them.  The guard 0 < #|G| is the
      source's n-vertex graphs and is load-bearing: at n = 0 and a = 0, 0^0 = 1 allows m = 1 and asks 2 <= 1.
      0 < k is not load-bearing (k = 0 fails at K_1). *)
Definition dvorak_postle_triangle_free_planar_three_colourings_lower_bound_statement : Prop :=
  exists k : nat, 0 < k /\
    forall G : sgraph, 0 < #|G| -> wagner_planar G -> triangle_free G ->
      forall a b m : nat, 9 ^ a < 3 ^ b * 2 ^ a -> m ^ b <= #|G| ^ a ->
        2 ^ m <= #|[set f : {ffun G -> 'I_3} | proper_colouring f]| ^ k.

(** Corpus row: arxiv:2103.05998#00
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/2103.05998__00/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/2103.05998__00.json
    English statement: (Alon, a conjecture in the closing remarks)
      The chromatic number of the graph G_(m,t) described in the proof of Theorem 1.4, where 4t^2 <= m, is
      Theta(t^2).
    Definitions: [x273_alon m t] - G_(m,t): the binary vectors of length m, adjacent iff their Hamming distance
      exceeds m - 2t (this file); [χ([set: G])] - the chromatic number of G (coq-graph-theory's [chi_mem]).
    Notes: encoded as stated over the admissible parameters; pinned status open.  The statement is the last remark of
      Alon (arXiv:2103.05998v2, 4 April 2021, main.tex l.493-500), a conjecture he raised more than ten years
      earlier. The graph is that of Theorem 1.4 (l.119-126), stated "for any positive integers m and t, where m is
      even and 4t^2 <= m"; the body keeps the three conditions (0 < t, m even, 4 t^2 <= m; 0 < m follows).
      Theta(t^2) has constants uniform over the admissible (m, t): c1 t^2 <= chi <= c2 t^2 with c1, c2 > 0,
      equivalently one natural k with t^2 <= k chi and chi <= k t^2 (k >= 1 / c1 and k >= c2; conversely c1 = 1 / k,
      c2 = k).  A form for t >= t0 only is equivalent, as chi >= 1 for the finitely many smaller t.  The paper proves
      2t <= chi and chi = O(t^2) (l.498-500), so the open part is the lower bound.  The guard 0 < t is load-bearing:
      at t = 0 the graph has no edge and chi = 1 > k * 0.  The guard 4 t^2 <= m is load-bearing too: at m = 2 the
      graph has four vertices while t^2 grows.  The FOCS 2008 paper of Alon, Hassidim, Lubetzky, Stav and Weinstein,
      the conjecture's motivation, is background (in the deposit). *)
Definition alon_hamming_graph_chromatic_number_theta_t_squared_statement : Prop :=
  exists k : nat, 0 < k /\
    forall m t : nat, 0 < t -> ~~ odd m -> 4 * t ^ 2 <= m ->
      t ^ 2 <= k * χ([set: x273_alon m t]) /\ χ([set: x273_alon m t]) <= k * t ^ 2.

(** Corpus row: arxiv:1809.05439#00
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/1809.05439__00/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/1809.05439__00.json
    English statement: (Dvorak and Hu, after Theorem 5)
      It might be possible to improve the ratio of extra colors assigned to the vertex x in Theorem 5 a bit; e.g., it
      could be true that there exists a coloring by subsets of {1, ..., 9} such that all vertices get at least three
      colors and x gets five.
    Definitions: [wagner_planar G] - G has neither K_5 nor K_(3,3) as a minor (GTBase base.v); [triangle_free G] - no
      three mutually adjacent vertices (GTBase base.v); [phi : G -> {set 'I_9}] - an assignment of subsets of nine
      colours, a set colouring when adjacent vertices get disjoint sets (the source's definition).
    Notes: encoded as its affirmative form; pinned status open.  The text is the remark after Theorem 5 of Dvorak and
      Hu (arXiv:1809.05439v1, 14 September 2018, nofrapl.tex l.157-159), and the class and quantifiers are Theorem
      5's (l.147-152): every triangle-free planar graph G and every vertex x of G, where Theorem 5 gives a set
      colouring by subsets of {1, ..., 6} with |phi(v)| >= 2 and |phi(x)| = 3.  A set colouring assigns disjoint sets
      to adjacent vertices (l.81-82).  "x gets five" is read as |phi(x)| = 5, as Theorem 5 reads |phi(x)| = 3; the
      form |phi(x)| >= 5 is equivalent: keeping five of x's colours keeps every edge disjoint and x above three.  The
      remark's example (l.159-161: the five-spoke wheel with its spokes subdivided once, x its centre, at least k / 3
      colours everywhere force |phi(x)| <= k / 3 + 2k / 9) gives |phi(x)| <= 5 at k = 9, so five is the most it can
      ask for.  The graph with no vertex holds vacuously; at K_1 five colours suffice. *)
Definition dvorak_hu_triangle_free_planar_nine_colour_sets_statement : Prop :=
  forall G : sgraph, wagner_planar G -> triangle_free G -> forall x : G,
    exists phi : G -> {set 'I_9},
      [/\ forall v : G, 3 <= #|phi v|, #|phi x| = 5 & forall u v : G, u -- v -> [disjoint phi u & phi v]].
