(** * Chromatic.conjectures.X277 -- wave X277: chromatic numbers of random graphs, the correspondence chromatic
    number of G(n, 1 - p) and the non-concentration of chi(G(n, 1/2)) (2026-11-02)

    A two-row wave under the prospective contract of meta/faithfulness_policy.json.  Rows: arxiv:2307.15048#00 (the
    correspondence chromatic number of G(n, 1 - p) is a.a.s. Theta(n / log n), for every fixed positive p <= 1) and
    erdos:1156 (two questions on the concentration of chi(G(n, 1/2)); the second is encoded, PARTIAL).  Shared
    vocabulary: the labelled random-graph weights [fg_gnp_weight] with [fg_whp], [fg_event_weight] and
    [fg_total_weight] (GTBase.finite_graph), [eventually] (GTBase.asymptotics), the chromatic number chi([set: G]) of
    coq-graph-theory and MathComp's [trunc_log].  Local notion: correspondence colourability with k colours per
    vertex, as a Boolean so that it can describe an event of G(n, p).  Chromatic.conjectures.X159's
    [x159_correspondence_3_colourable] is the same notion with the palette fixed to three colours and stated as a Prop;
    it cannot be generalised in place without changing X159's reviewed statement, and grounding_X277 proves the two
    equivalent at k = 3.  Pinned statuses: both open.  The sources are the Mac's deposit
    coordination/sources/x277-source-mac-20261102 (text line numbers below).  The grounding certificates are in
    grounding_X277.v. *)

From GTBase Require Import base common finite_graph.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local x277 vocabulary ************************************************* *)

(** G is correspondence colourable with k colours (DP-colourable): for every correspondence assignment C with the
    lists {v} x 'I_k, there is a colouring col choosing one colour per vertex such that no edge has its two chosen
    colours matched.  An assignment is a relation C on (G * 'I_k) * (G * 'I_k) that, on every edge uv, is symmetric
    under swapping the two ends and is a partial matching between {u} x 'I_k and {v} x 'I_k (functional in each
    argument); its pairs on non-edges are never consulted.  These are the three clauses of X159's
    [x159_correspondence_assignment] with 'I_k for 'I_3.  It is a Boolean (finite quantifiers over the finite sets C
    and the finite functions col). *)
Definition x277_correspondence_colourable (G : sgraph) (k : nat) : bool :=
  [forall C : {set (G * 'I_k) * (G * 'I_k)},
    [&& [forall u : G, [forall v : G, (u -- v) ==> [forall a : 'I_k, [forall b : 'I_k,
           (((u, a), (v, b)) \in C) == (((v, b), (u, a)) \in C)]]]],
        [forall u : G, [forall v : G, (u -- v) ==> [forall a : 'I_k, [forall b1 : 'I_k, [forall b2 : 'I_k,
           ((((u, a), (v, b1)) \in C) && (((u, a), (v, b2)) \in C)) ==> (b1 == b2)]]]]] &
        [forall u : G, [forall v : G, (u -- v) ==> [forall a1 : 'I_k, [forall a2 : 'I_k, [forall b : 'I_k,
           ((((u, a1), (v, b)) \in C) && (((u, a2), (v, b)) \in C)) ==> (a1 == a2)]]]]]]
    ==> [exists col : {ffun G -> 'I_k}, [forall u : G, [forall v : G,
          (u -- v) ==> (((u, col u), (v, col v)) \notin C)]]]].

(** ** X277 statements ******************************************************* *)

(** Corpus row: arxiv:2307.15048#00
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/2307.15048__00/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/2307.15048__00.json
    English statement: (Dvorak and Yepremyan, Correspondence coloring of random graphs, arXiv:2307.15048, Conjecture
      1.4)  For every fixed positive p <= 1, the Erdos-Renyi random graph G(n, 1 - p) asymptotically almost surely
      has correspondence chromatic number Theta(n / log n).
    Definitions: [x277_correspondence_colourable G k] - every correspondence assignment with k colours per vertex
      admits a colouring (this file); [fg_labelled_sgraph E] - the graph on 'I_n with edge set E, [fg_gnp_weight r q
      n] - the G(n, r/q) weight of a labelled edge set, defined for 0 < r < q, [fg_whp] - the probability of the
      event tends to 1 (GTBase base/theories/finite_graph.v); [eventually] (GTBase base/theories/asymptotics.v);
      [trunc_log 2 n] - the binary logarithm of n rounded down (MathComp).
    Notes: encoded as printed in arXiv:2307.15048v1 (main.tex l.246-248), p in (0, 1] included.  Correspondence
      colouring as defined at l.194-201: lists of at least l colours and, for each edge, a not necessarily perfect
      matching between the two lists; the correspondence chromatic number is the least l such that every
      l-assignment admits a colouring.  Lists of exactly k colours, renamed to {v} x 'I_k, give the same number (a
      longer list can be shortened, and only the matchings between lists matter).  p = a/b is rational: by the
      monotone coupling of G(n, q) in q and the monotonicity of the correspondence chromatic number under
      subgraphs, the statement for all real p in (0, 1) follows from the rational one (bound p between rationals),
      and the constants may depend on p as in the source.  The body is the conjunction over p in (0, 1) (the
      fg_whp clause, G(n, (b - a)/b), constants c1, c2 >= 1 before n) and over p = 1, where G(n, 0) is the
      edgeless graph with probability 1, so "a.a.s." is "eventually"; fg_gnp_weight has no mass at edge
      probability 0.  Theta(n / log n): n <= c1 k trunc_log 2 n for every colourable k (the lower bound; k ranges
      over 'I_n.+1, since k > n satisfies it once c1 >= 1 and n >= 2) and some colourable k with k trunc_log 2 n <=
      c2 n (the upper bound; k ranges over 'I_(c2 * n).+1, which that inequality forces once n >= 2); the base of
      the logarithm and its rounding change only the constants.  AT p = 1 THE STATEMENT AS PRINTED IS FALSE: the
      edgeless graph is 1-colourable, so a lower bound of order n / log n fails (the p = 1 clause is refuted in
      grounding_X277, [g277_p_one_clause_false]).  The source's lower-bound remarks are mixed:
      l.227-228 derive chi(G(n, 1 - p)) = Omega(n / log n) "for positive p<=1", which also fails at p = 1, and only
      l.233 says "for any positive p<1".  "False as printed" is a question for Marc through the DAILY (Lancelot's
      (348), (367)); this file changes no status.  Literature: pinned status open; Theorem 1.1 (l.218-220) gives
      only O(n / sqrt(log n)).  The subtraction b - a is guarded by a < b, and the positive constants by 0 < c1, c2. *)
Definition correspondence_chromatic_random_graph_theta_n_over_log_n_statement : Prop :=
  (forall a b : nat, 0 < a -> a < b ->
    exists c1 c2 : nat, [/\ 0 < c1, 0 < c2 &
      @fg_whp (fun n : nat => {set {set 'I_n}}) (fun n => @fg_gnp_weight (b - a) b n)
        (fun n E => let G := fg_labelled_sgraph E in
           [forall k : 'I_n.+1, x277_correspondence_colourable G k ==> (n <= c1 * k * trunc_log 2 n)] &&
           [exists k : 'I_(c2 * n).+1, x277_correspondence_colourable G k && (k * trunc_log 2 n <= c2 * n)])]) /\
  (exists c1 c2 : nat, [/\ 0 < c1, 0 < c2 &
     eventually (fun n => let G := fg_labelled_sgraph (set0 : {set {set 'I_n}}) in
       [forall k : 'I_n.+1, x277_correspondence_colourable G k ==> (n <= c1 * k * trunc_log 2 n)] &&
       [exists k : 'I_(c2 * n).+1, x277_correspondence_colourable G k && (k * trunc_log 2 n <= c2 * n)])]).

(** Corpus row: erdos:1156
    Site: none
    Review: none
    English statement: (Erdos Problems #1156)  Let G be a random graph on n vertices, in which every edge is
      included independently with probability 1/2.  Is there some constant C such that the chromatic number chi(G)
      is, almost surely, concentrated on at most C values?  Is it true that, if omega(n) -> oo sufficiently slowly,
      then for every function f(n), P(|chi(G) - f(n)| < omega(n)) < 1/2 if n is sufficiently large?
    Definitions: chi([set: G]) - the chromatic number (coq-graph-theory); [fg_labelled_sgraph E], [fg_gnp_weight 1 2
      n] - the G(n,1/2) weight (every labelled graph on n vertices has weight 1), [fg_event_weight] and
      [fg_total_weight] - the weight of an event and of the whole space (GTBase base/theories/finite_graph.v);
      [eventually] (GTBase base/theories/asymptotics.v).
    Notes: PARTIAL: the row asks two separate questions, and the second is encoded.  "If omega -> oo sufficiently
      slowly" is: some unbounded omega works (a smaller window has a smaller probability, so every slower unbounded
      omega works too, and conversely the slowest admissible one is itself such an omega).  f and omega are read as
      integer-valued: a real centre gives windows of at most 2 omega consecutive integers, covered by integer centres
      with omega + 1.  "< 1/2" is 2 P(E) < P(total), with the weights written out because [fg_event_at_most_ratio]
      is <=; G(n, 1/2) has positive total weight.  The first question is not encoded.  The literature reads its "C
      values" as C consecutive values (Heckel, arXiv:1906.11808v2, l.114-115: "not concentrated on a series of
      intervals of constant length"; Heckel and Riordan, arXiv:2103.14014v3, l.161), and in that reading Heckel's
      theorem answers it negatively (1906.11808v2 l.120-122: no sequence of intervals of length n^c, c < 1/4,
      contains chi(G(n,1/2)) whp).  The page does not say consecutive, and in the literal reading (any C values) it
      is open, so the question has no single fixed meaning; joining it to the second would not be "false by logic"
      in that reading (three spread values of probability 1/3 each satisfy both), but a conjunction would tie two
      questions with opposite expected answers to one status.  Literature status of the encoded question: open at
      the pin.  Heckel and Riordan (2103.14014v3, l.173-177) extend the interval result to c < 1/2, and
      l.182-183: it "tells us nothing about the concentration ... for any particular n, let alone every n".
      Pinned status open. *)
Definition random_graph_chromatic_number_not_concentrated_in_slowly_growing_windows_statement : Prop :=
  exists w : nat -> nat, (forall M : nat, eventually (fun n => M <= w n)) /\
    forall f : nat -> nat, eventually (fun n =>
      0 < fg_total_weight (@fg_gnp_weight 1 2 n) /\
      2 * fg_event_weight (@fg_gnp_weight 1 2 n)
            (fun E => let G := fg_labelled_sgraph E in
               (f n < χ([set: G]) + w n) && (χ([set: G]) < f n + w n))
        < fg_total_weight (@fg_gnp_weight 1 2 n)).
