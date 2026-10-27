(** * Extremal.conjectures.X244 -- wave X244: completing triangle-free graphs to diameter 2, the Edwards excess, independent sets of graphs not Ramsey for K_3, monochromatic triangle packings (2026-10-27)

    A five-row wave under the prospective contract of meta/faithfulness_policy.json.  Rows: erdos:134 and erdos:618
    (adding few edges to a triangle-free graph of small maximum degree to reach a triangle-free graph of diameter 2),
    erdos:127 (the excess of the largest bipartite subgraph over the Edwards bound), erdos:925 (independent sets in
    graphs that are not Ramsey for K_3) and erdos:76 (edge-disjoint monochromatic triangles in 2-colourings of K_n).
    No local helper and no copied vocabulary: GTBase supplies [edge_count], [has_subgraph], 'K_n, [del_edge_set]
    and [graph_dist] (GTBase.graph_metric); [compl], [stable] and N(x) are upstream; [mono_copy] is
    Extremal.foundations.edge_colourings'.  Adding a set X of pairs to G is written [compl (del_edge_set (compl G) X)]:
    x -- y there iff x != y and (x -- y in G or [set x; y] \in X).  All five rows have pinned status "solved"; their
    literature lines are dated against the corpus pin (graph-conjectures b72c5857, 2026-09-23).  The grounding
    certificates are in grounding_X244.v. *)

From Extremal.foundations Require Import edge_colourings.
(* GTBase last, as in X239. *)
From GTBase Require Import base common graph_metric.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** X244 statements ******************************************************* *)

(** Corpus row: erdos:134
    Site: none
    Review: none
    English statement: (Erdos Problems #134, Erdos and Gyarfas)
      For all eps, delta > 0 and n large in terms of eps and delta, every triangle-free graph on n vertices with
      maximum degree < n^{1/2 - eps} can be made into a triangle-free graph of diameter 2 by adding at most
      delta n^2 edges.
    Definitions: [has_subgraph G 'K_3] - G contains a triangle (GTBase.common); N(v) - the neighbourhood of v
      (upstream); [compl G] - the complement of G (upstream GraphTheory.core.sgraph.compl; x -- y iff x != y and not
      x -- y in G) and [del_edge_set G D] - G without the pairs of D (GTBase), so that
      [compl (del_edge_set (compl G) X)] is G with the pairs of X added; [graph_dist x y] - the length of a shortest
      x-y path, truncated at the number of vertices for x and y in different components (GTBase.graph_metric).
    Notes: the pinned statement is the erdosproblems.com question ("Let eps, delta > 0 and n be sufficiently large
      in terms of eps and delta.  Let G be a triangle-free graph on n vertices with maximum degree < n^{1/2-eps}.
      Can G be made into a triangle-free graph with diameter 2 by adding at most delta n^2 edges?"); the affirmative
      form is stated.  eps = 1/q and delta = 1/p: the statement is monotone in both (a smaller eps or delta asks
      more), so reciprocal integers cover every positive real.  deg(v) < n^{1/2 - 1/q} is written
      deg(v)^{2q} n^2 < n^q (no subtraction); the added pairs X are non-edges of G (X \subset E(compl G)), so #|X| is
      the number of added edges.  Diameter 2 is "every distance is at most 2", which for a triangle-free graph on
      n >= 3 vertices is diameter exactly 2 (as for erdos:133 in X243).
      Literature status: PROVED BEFORE the corpus pin (pinned status "solved"): Alon, "Triangle-free graphs of
      diameter 2" (author-hosted note), Theorem 1.2 (p.1): for n large and maximum degree d <= c sqrt(n) with
      2 (log n)^{1/3} / n^{1/6} <= c = c(n) <= 1/10, one can add to G at most 2.5 c n^2 edges and get a
      triangle-free graph of diameter 2; with c = n^{-eps} this covers every 0 < eps < 1/6 (the abstract: fewer than
      3 n^{2-eps} edges), and a larger eps follows since its degree hypothesis is stronger.  The same result is
      Theorem 3.2 (p.8) of Alon, "Problems and results in extremal combinatorics - V", in Sum(m)it 280, Springer
      (DOI 10.1007/978-3-032-18810-6_2, online 2026-05-28 per Crossref).  The mirror (10fb9c15) lists "proved
      (Lean)" (2026-02-07). *)

Definition triangle_free_low_degree_diameter_two_completion_statement : Prop :=
  forall q p : nat, 1 <= q -> 1 <= p -> exists n0 : nat,
    forall G : sgraph, n0 <= #|G| -> ~ has_subgraph G 'K_3 ->
      (forall v : G, #|N(v)| ^ (2 * q) * #|G| ^ 2 < #|G| ^ q) ->
      exists X : {set {set G}},
        [/\ X \subset E(compl G), p * #|X| <= #|G| ^ 2,
            ~ has_subgraph (compl (del_edge_set (compl G) X)) 'K_3 &
            forall x y : compl (del_edge_set (compl G) X), graph_dist x y <= 2].

(** Corpus row: erdos:618
    Site: none
    Review: none
    English statement: (Erdos Problems #618)
      For a triangle-free graph G let h_2(G) be the least number of edges whose addition gives a triangle-free graph
      of diameter 2.  If G has maximum degree o(n^{1/2}) then h_2(G) = o(n^2): for every eps > 0 there are eta > 0
      and n0 such that every triangle-free graph on n >= n0 vertices with maximum degree <= eta sqrt(n) becomes a
      triangle-free graph of diameter 2 after adding at most eps n^2 edges.
    Definitions: as for erdos:134 (has_subgraph, N, compl, del_edge_set, graph_dist).
    Notes: the pinned statement is the erdosproblems.com question ("For a triangle-free graph G let h_2(G) be the
      smallest number of edges that need to be added to G so that it has diameter 2 and is still triangle-free.  Is
      it true that if G has maximum degree o(n^{1/2}) then h(G) = o(n^2)?"); the affirmative form is stated, in its
      uniform version: for sequences of graphs, "maximum degree o(n^{1/2}) implies h_2 = o(n^2)" is equivalent to
      "for every eps = 1/p there are eta = 1/r and n0 with: degree <= sqrt(n)/r implies h_2 <= n^2/p" (failures at
      r = 1, 2, ... would form a counterexample sequence).  deg(v) <= sqrt(n)/r is (r deg(v))^2 <= n.  Added pairs
      and diameter 2 as for erdos:134.
      Literature status: PROVED BEFORE the corpus pin (pinned status "solved"): Alon, "Triangle-free graphs of
      diameter 2" (author-hosted note), Theorem 1.2 (p.1): for n large and maximum degree d <= c sqrt(n) with
      2 (log n)^{1/3} / n^{1/6} <= c = c(n) <= 1/10, at most 2.5 c n^2 added edges give a triangle-free graph of
      diameter 2; for 1/p take an integer r >= max(10, 3p) and c = 1/r (the lower condition holds for large n, and
      2.5/r <= 1/p).  Also Theorem 3.2 (p.8) of Alon, "Problems and results in extremal combinatorics - V", Sum(m)it
      280, Springer (DOI 10.1007/978-3-032-18810-6_2, online 2026-05-28 per Crossref).  The mirror (10fb9c15) lists
      "proved (Lean)" (2026-02-08). *)

Definition triangle_free_sublinear_degree_diameter_two_completion_statement : Prop :=
  forall p : nat, 1 <= p -> exists r n0 : nat, 1 <= r /\
    forall G : sgraph, n0 <= #|G| -> ~ has_subgraph G 'K_3 ->
      (forall v : G, (r * #|N(v)|) ^ 2 <= #|G|) ->
      exists X : {set {set G}},
        [/\ X \subset E(compl G), p * #|X| <= #|G| ^ 2,
            ~ has_subgraph (compl (del_edge_set (compl G) X)) 'K_3 &
            forall x y : compl (del_edge_set (compl G) X), graph_dist x y <= 2].

(** Corpus row: erdos:127
    Site: none
    Review: none
    English statement: (Erdos Problems #127, Erdos, Gyarfas and Kohayakawa)
      Let f(m) be the largest number such that every graph with m edges has a bipartite subgraph with at least
      m/2 + (sqrt(8m+1) - 1)/8 + f(m) edges.  Then f is unbounded: there is a sequence m_i with f(m_i) -> infinity.
    Definitions: [edge_count G] - the number of edges (GTBase); [[set e in E(G) | #|e :&: A| == 1]] - the edges of G
      with exactly one end in A, the edge set of a largest bipartite subgraph when A is chosen well.
    Notes: the pinned statement is the erdosproblems.com question ("Let f(m) be maximal such that every graph with
      m edges must contain a bipartite graph with >= m/2 + (sqrt(8m+1) - 1)/8 + f(m) edges.  Is there an infinite
      sequence of m_i such that f(m_i) -> infinity?"); the affirmative form is stated.  A sequence with
      f(m_i) -> infinity exists iff f is unbounded above, i.e. for every integer K some m has f(m) >= K, i.e. every
      graph with m edges has a cut of size b >= m/2 + (sqrt(8m+1) - 1)/8 + K (a bipartite subgraph lies inside a
      cut of the same graph).  That inequality is X = 8b + 1 - 4m - 8K >= 0 with X^2 >= 8m + 1, written with X as a
      witness (no subtraction, no square root).
      Literature status: PROVED BEFORE the corpus pin (pinned status "solved"): Alon, "Bipartite subgraphs",
      Combinatorica 16 (1996) 301-311 (author PDF), Theorem 1.1 (p.1): there are c > 0 and n0 such that for every
      even n > n0, with e = n^2/2, every graph with e edges has a bipartite subgraph with at least e/2 + sqrt(e/8) +
      c e^{1/4} edges; as (sqrt(8e+1) - 1)/8 <= sqrt(e/8), the excess over Edwards' bound tends to infinity along
      e = n^2/2 (the paper's f(e) is the guaranteed bipartite subgraph size, the problem's f(m) the excess).  The
      mirror (10fb9c15) lists "proved (Lean)" (2026-08-24). *)

Definition bipartite_subgraph_edwards_excess_unbounded_statement : Prop :=
  forall K : nat, exists m : nat,
    forall G : sgraph, edge_count G = m ->
      exists (A : {set G}) (X : nat),
        X + 4 * m + 8 * K = 8 * #|[set e in E(G) | #|e :&: A| == 1]| + 1 /\ 8 * m + 1 <= X ^ 2.

(** Corpus row: erdos:925
    Site: none
    Review: none
    English statement: (Erdos Problems #925)
      There is delta > 0 such that, for all large n, every graph on n vertices which is not Ramsey for K_3 (some
      2-colouring of its edges has no monochromatic triangle) has an independent set of size >> n^{1/3 + delta}.
    Definitions: [mono_copy 'K_3 col b] - a triangle of the host all of whose edges have colour b under the edge
      colouring col (Extremal.foundations.edge_colourings; colours of non-edges are never read); [stable S] - no two
      vertices of S are adjacent (upstream).
    Notes: the pinned statement is the erdosproblems.com question ("Is there a constant delta > 0 such that, for all
      large n, if G is a graph on n vertices which is not Ramsey for K_3 (i.e. there exists a 2-colouring of the
      edges of G with no monochromatic triangle) then G contains an independent set of size >> n^{1/3+delta}?");
      the affirmative form is stated.  delta = 1/q (a smaller delta asks less, so some delta exists iff some 1/q
      does); |S| >= n^{1/3 + 1/q} / c is raised to the 3q-th power: n^{q+3} <= (c |S|)^{3q}.
      Literature status: FALSE BEFORE the corpus pin (pinned status "solved"): Alon and Rodl, "Sharp bounds for some
      multicolor Ramsey numbers", Combinatorica 25 (2005) 125-141 (author PDF), equation (1) (p.2): r_k(K_3; K_m) =
      Theta(m^{k+1} polylog m), here k = 2: r(K_3, K_3, K_m) >= m^{3-o(1)}.  A 3-colouring of K_N, N = r(K_3, K_3,
      K_m) - 1, with no triangle in the first two colours and no K_m in the third gives a graph (the first two colour
      classes) that is not Ramsey for K_3 and has no independent set of size m = N^{1/3 + o(1)}, against every fixed
      delta = 1/q and constant c.  The mirror (10fb9c15) lists "disproved". *)

Definition not_triangle_ramsey_independent_set_exponent_statement : Prop :=
  exists q c n0 : nat, [/\ 1 <= q, 1 <= c &
    forall G : sgraph, n0 <= #|G| ->
      (exists col : {set G} -> bool, forall b : bool, ~ mono_copy 'K_3 col b) ->
      exists S : {set G}, stable S /\ #|G| ^ (q + 3) <= (c * #|S|) ^ (3 * q)].

(** Corpus row: erdos:76
    Site: none
    Review: none
    English statement: (Erdos Problems #76)
      In every 2-colouring of the edges of K_n there are at least (1 + o(1)) n^2/12 edge-disjoint monochromatic
      triangles: for every eps > 0, if n is large enough, at least (1 - eps) n^2/12 of them.
    Definitions: the vertices of K_n are 'I_n and its edges the pairs [set x; y] (x != y), coloured by col; a
      triangle is a 3-set t all of whose pairs have the same colour b; two triangles sharing at most one vertex share
      no edge.
    Notes: the pinned statement is the erdosproblems.com question ("Is it true that in any 2-colouring of the edges
      of K_n there must exist at least (1+o(1)) n^2/12 many edge-disjoint monochromatic triangles?"); the
      affirmative form is stated.  The lower bound (1 - 1/q) n^2/12 <= |T| is written q n^2 <= 12 q |T| + n^2 (no
      subtraction); the matching upper bound (1 + o(1)) belongs to the extremal colouring, not to the question.
      Literature status: PROVED BEFORE the corpus pin (pinned status "solved"): Gruslys and Letzter, "Monochromatic
      triangle packings in red-blue graphs", arXiv:2008.05311v2 (v1 2020-08-12, v2 2020-08-14), Theorem 1.2
      (triangle-packing.tex l.187-188): "Every 2-coloured K_n contains a collection of n^2/12 + o(n^2) pairwise
      edge-disjoint monochromatic triangles" (each triangle monochromatic, possibly in different colours, as
      encoded); earlier Keevash and Sudakov (2004) with a weaker constant.  The mirror (10fb9c15) lists "proved". *)

Definition two_colouring_edge_disjoint_monochromatic_triangles_statement : Prop :=
  forall q : nat, 1 <= q -> exists n0 : nat,
    forall (n : nat) (col : {set 'I_n} -> bool), n0 <= n ->
      exists T : {set {set 'I_n}},
        [/\ forall t : {set 'I_n}, t \in T ->
              #|t| = 3 /\ exists b : bool, forall x y : 'I_n, x \in t -> y \in t -> x != y -> col [set x; y] = b,
            forall t u : {set 'I_n}, t \in T -> u \in T -> t != u -> #|t :&: u| <= 1 &
            q * n ^ 2 <= 12 * q * #|T| + n ^ 2].
