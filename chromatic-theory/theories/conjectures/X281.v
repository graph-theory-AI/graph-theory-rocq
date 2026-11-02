(** * Chromatic.conjectures.X281 -- wave X281: almost r-chromatic subgraphs, the limit of max chi / omega and
    generalised chromatic polynomials of random graphs (2026-11-02)

    A three-row wave under the prospective contract of meta/faithfulness_policy.json.  Rows: erdos:1092 (Erdos, Hajnal
    and Szemeredi: deleting fewer than c_r m edges from every m-vertex subgraph to reach chromatic number r forces
    chromatic number r + 1), erdos:627 (does f(n) / (n / (log_2 n)^2) converge, f(n) the largest chi / omega on n
    vertices) and arxiv:2402.04237#01 (Problem 12 of Hogan, Scott, Tamitegama and Tan: does a finite family of
    generalised chromatic polynomials determine almost every graph?).  Shared vocabulary: the chromatic and clique
    numbers chi(A), omega(A) and [induced S] of coq-graph-theory; E(G) and [del_edge_set] (GTBase.common); the labelled
    graphs [fg_labelled_sgraph], the G(n, 1/2) weight [fg_gnp_weight 1 2 n] and [fg_whp] (GTBase.finite_graph);
    MathComp's [trunc_log].  Local notion: the generalised chromatic polynomial [x281_gen_chromatic_poly], which counts
    sets of colourings, so it has no shared counterpart.  Pinned statuses: all three open; erdos:1092 is refuted in the
    literature (Rodl 1982, see its Notes).  The sources are the Mac's deposit coordination/sources/
    x281-source-mac-20261102 (line numbers below).  The grounding certificates are in grounding_X281.v. *)

From GTBase Require Import base common finite_graph.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local x281 vocabulary ************************************************* *)

(** The generalised chromatic polynomial pi^(H)_G(k) of Asgarli, Krehbiel, Levinson and Russell as Hogan, Scott,
    Tamitegama and Tan state it (arXiv:2402.04237v2, chromaticpolys.tex l.122-134).  A k-colouring is a proper
    colouring with colours in [k] = 'I_k (l.122).  The k-colouring graph C_k(G) has the k-colourings as vertices, and
    two of them are adjacent when they differ at exactly one vertex of G (l.126).  pi^(H)_G(k) is the number of sets S
    of vertices of C_k(G) that induce a subgraph isomorphic to H (l.133-134).  Here: the sets S of proper colourings
    that are the image of an injective f from H with x -- y in H exactly when f x and f y differ at exactly one vertex.
    So f is an isomorphism from H onto the subgraph of C_k(G) induced on S.  Sets are counted, not maps. *)
Definition x281_gen_chromatic_poly (G H : sgraph) (k : nat) : nat :=
  #|[set S : {set {ffun G -> 'I_k}} |
      [forall c in S, [forall x : G, [forall y : G, (x -- y) ==> (c x != c y)]]] &&
      [exists f : {ffun H -> {ffun G -> 'I_k}},
         [&& injectiveb f, S == [set f x | x : H] &
             [forall x : H, [forall y : H, (x -- y) == (#|[set v : G | f x v != f y v]| == 1)]]]]]|.

(** ** X281 statements ******************************************************* *)

(** Corpus row: erdos:1092
    Site: none
    Review: none
    English statement: (Erdos Problems #1092)  Let f_r(n) be maximal such that, if a graph G has the property that
      every subgraph H on m vertices is the union of a graph with chromatic number r and a graph with <= f_r(m) edges,
      then G has chromatic number <= r + 1.  Is it true that f_2(n) >> n?  More generally, is f_r(n) >>_r n?
    Definitions: chi(A) - the chromatic number, [induced S] - the subgraph induced on S (coq-graph-theory); E(G) - the
      edge set, [del_edge_set G F] - G with the edges in F deleted (GTBase common.v).
    Notes: the general question, which contains r = 2.  It is encoded in the form of its source, Erdos, Some recent
      problems and results in graph theory, combinatorics and number theory (1976), p.4 (the Mac's deposit,
      Er76c-p4.png): there is c_r > 0 such that if every subgraph G(m) of G(n), 1 <= m <= n, is the union of an
      r-chromatic graph and a graph of fewer than c_r m edges, then chi(G(n)) <= r + 1.
      - c_r = 1 / q: a smaller c only strengthens the hypothesis, so it may be taken of this form.
      - "f_r(n) >> n" is that uniform constant.  A valid f with f(m) >= c m for m >= m0 gives c' = min(c, 1 / m0) for
        every m, since fewer than c' m < 1 edges is none; conversely c_r gives a valid f >= c_r m / 2 for large m.
      - "Chromatic number r" is at most r.  The live page now prints <= r, and exactly r would fail at every subgraph
        with fewer than r vertices.  r >= 1, since at r = 0 the hypothesis fails at any vertex.
      - Every subgraph versus induced subgraphs: equivalent.  A subgraph of G[S] keeps what remains of F's edges, so
        it is r-colourable after fewer deletions.  The body takes the induced subgraph on each nonempty S and the
        deleted edges F inside it.
      Literature: FALSE for every r >= 2.  Rodl, Nearly bipartite graphs with large chromatic number, Combinatorica
      (1982), Ro82-publisher.html.txt l.549-550, answers Erdos and Hajnal's question negatively; Lovasz did too, by a
      different construction.  The page's comment (erdos-1092.txt l.36-39) gives graphs of every chromatic number in
      which every m-vertex subgraph becomes bipartite after deleting at most eps m edges, "f_r(n) = o(n) for all fixed
      r >= 2".  The historical body is kept.  The pinned status is open; the literature status is Lancelot's lit21
      ((397)). *)
Definition erdos_hajnal_szemeredi_almost_r_chromatic_subgraphs_statement : Prop :=
  forall r : nat, 1 <= r -> exists q : nat, 0 < q /\
    forall G : sgraph,
      (forall S : {set G}, S != set0 ->
         exists F : {set {set induced S}},
           [/\ F \subset E(induced S), χ([set: del_edge_set (induced S) F]) <= r & q * #|F| < #|S|]) ->
      χ([set: G]) <= r.+1.

(** Corpus row: erdos:627
    Site: none
    Review: none
    English statement: (Erdos Problems #627)  Let omega(G) denote the clique number of G and chi(G) the chromatic
      number.  If f(n) is the maximum value of chi(G) / omega(G), as G ranges over all graphs on n vertices, then does
      lim_{n -> oo} f(n) / (n / (log_2 n)^2) exist?
    Definitions: [fg_labelled_sgraph E] - the graph on 'I_n with edge set E (GTBase finite_graph.v); chi(A),
      omega(A) - the chromatic and clique numbers (coq-graph-theory); [trunc_log 2 n] - the binary logarithm of n
      rounded down (MathComp).
    Notes: existence of the limit as a Cauchy criterion.  For every rational eps = p / q > 0 there is N >= 2 with
      |b(n1) - b(n2)| < eps for all n1, n2 >= N, where b(n) = f(n) (trunc_log 2 n)^2 / n, cross-multiplied.
      - f(n) is the ratio of a maximiser: a labelled graph on 'I_n whose chi / omega is at least that of every
        labelled graph on 'I_n.  Every graph on n vertices is isomorphic to one, all maximisers have the same ratio,
        and grounding_X281 shows that one exists for every n.
      - n >= 2: the normaliser n / (log_2 n)^2 is undefined at n = 1, and trunc_log 2 n >= 1 from n = 2.
      - trunc_log 2 n for log_2 n: their ratio tends to 1, and f(n) (log_2 n)^2 / n is bounded (2512.16062v2,
        Max_ratio_v2.tex l.166-171, and l.175-178 with 3.71943), so the two sequences differ by o(1) and converge
        together.
      - Base 2 as printed (and l.157).
      Literature: Erdos showed f(n) = Theta(n / (log n)^2) (l.139).  The limit is open at the pin: the theorem at
      l.159-164 ties it to lim log R(k, k) / k only under a Ramsey conjecture ("should they exist", l.157). *)
Definition chi_over_omega_max_ratio_limit_exists_statement : Prop :=
  forall p q : nat, 0 < p -> 0 < q ->
    exists N : nat, 2 <= N /\
      forall (n1 n2 : nat) (E1 : {set {set 'I_n1}}) (E2 : {set {set 'I_n2}}), N <= n1 -> N <= n2 ->
        let G1 := fg_labelled_sgraph E1 in let G2 := fg_labelled_sgraph E2 in
        (forall E : {set {set 'I_n1}},
           χ([set: fg_labelled_sgraph E]) * ω([set: G1]) <= χ([set: G1]) * ω([set: fg_labelled_sgraph E])) ->
        (forall E : {set {set 'I_n2}},
           χ([set: fg_labelled_sgraph E]) * ω([set: G2]) <= χ([set: G2]) * ω([set: fg_labelled_sgraph E])) ->
        q * (χ([set: G1]) * trunc_log 2 n1 ^ 2 * (ω([set: G2]) * n2))
          < q * (χ([set: G2]) * trunc_log 2 n2 ^ 2 * (ω([set: G1]) * n1))
            + p * (ω([set: G1]) * n1 * (ω([set: G2]) * n2)) /\
        q * (χ([set: G2]) * trunc_log 2 n2 ^ 2 * (ω([set: G1]) * n1))
          < q * (χ([set: G1]) * trunc_log 2 n1 ^ 2 * (ω([set: G2]) * n2))
            + p * (ω([set: G1]) * n1 * (ω([set: G2]) * n2)).

(** Corpus row: arxiv:2402.04237#01
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/2402.04237__01/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/2402.04237__01.json
    English statement: (Hogan, Scott, Tamitegama and Tan, A note on graphs of k-colourings, arXiv:2402.04237,
      Problem 12)  Is there a finite set of graphs H_1, ..., H_t such that, for almost every G in G(n, 1/2), if
      pi^(H_i)_G' = pi^(H_i)_G for all i then G' is isomorphic to G?
    Definitions: [x281_gen_chromatic_poly G H k] - the generalised chromatic polynomial pi^(H)_G(k) (this file);
      [fg_labelled_sgraph E] - the graph on 'I_n with edge set E, [fg_gnp_weight 1 2 n] - the G(n, 1/2) weight (every
      labelled graph on n vertices has weight 1), [fg_whp] - the probability of the event tends to 1 (GTBase
      finite_graph.v).
    Notes: encoded affirmatively, the corpus precedent for question rows.  The family is chosen before n, as printed
      (chromaticpolys.tex l.387-389).  G' ranges over graphs on the vertex set of G, and the equality of polynomials
      is equality at k = 0, ..., n * max_i |H_i|.
      - pi^(H)_G is a polynomial in k for every k (l.146-150), of degree at most n |H|.  An |H|-tuple of distinct
        colourings is fixed by a partition of V(G) x H, and each pattern gives a falling factorial of degree at most
        n |H|, as the Mac's source note derives.  l.197's sum up to n is not a degree bound: pi^(K_2) of K_1 is
        k (k - 1) / 2 (grounding_X281).  So two such polynomials that agree at n max_i |H_i| + 1 points are equal.
      - Same order loses nothing.  pi^(K_1)_G' is the chromatic polynomial (l.134), monic of degree |G'|.  A family
        that works here still works with K_1 added, and then equal polynomials force |G'| = n; conversely the
        printed question implies this one.
      Literature: open at the pin.  l.171-174 rules out a finite family for all graphs, and Bollobas, Pebody and
      Riordan conjecture that almost every graph is determined by its chromatic polynomial alone (l.384). *)
Definition generalised_chromatic_polynomials_determine_almost_every_graph_statement : Prop :=
  exists (t : nat) (Hs : 'I_t -> sgraph),
    @fg_whp (fun n : nat => {set {set 'I_n}}) (fun n => @fg_gnp_weight 1 2 n)
      (fun n E => [forall E' : {set {set 'I_n}},
         [forall i : 'I_t, [forall k : 'I_(n * \max_(j < t) #|Hs j|).+1,
            x281_gen_chromatic_poly (fg_labelled_sgraph E') (Hs i) k
              == x281_gen_chromatic_poly (fg_labelled_sgraph E) (Hs i) k]]
         ==> [exists f : {ffun 'I_n -> 'I_n}, injectiveb f && [forall x : 'I_n, [forall y : 'I_n,
               @edge_rel (fg_labelled_sgraph E') x y == @edge_rel (fg_labelled_sgraph E) (f x) (f y)]]]]).
