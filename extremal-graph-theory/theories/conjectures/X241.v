(** * Extremal.conjectures.X241 -- wave X241: octahedron-free density, size and off-diagonal Ramsey numbers (2026-10-27)

    A six-row wave under the prospective contract of meta/faithfulness_policy.json.  Rows: erdos:579 (K_{2,2,2}-free
    dense graphs have linear independent sets), erdos:911 (size Ramsey numbers against density), erdos:1182 (triangle
    goodness of sparse connected graphs), erdos:166 (R(4,k)), erdos:546 (R(G) against the number of edges) and
    erdos:1014 (R(k,l+1) / R(k,l)).  No local helper and no copied vocabulary: two-colour Ramsey numbers are
    Extremal.conjectures.XE1's [xe1_graph_ramsey_number H K R] (the least R such that every graph on R vertices
    contains H or its complement contains K), [xe1_diagonal_ramsey_number G R] (= r(G)) and
    [xe1_size_ramsey_number H K m] (the size Ramsey number); GTBase supplies [complete_multipartite_graph 3 2]
    (= K_{2,2,2}), [min_degree_at_least], [edge_count], [has_subgraph] and 'K_n; [stable] and [connected] are
    upstream; [trunc_log] is MathComp's.  Literature dates are against the corpus pin (graph-conjectures b72c5857,
    2026-09-23); these rows carry no review date, so their pinned status is the pin's.  The grounding certificates
    are in grounding_X241.v. *)

From Extremal.conjectures Require Import XE1.
From GTBase Require Import base common complete_multipartite_graphs.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** X241 statements ******************************************************* *)

(** Corpus row: erdos:579
    Site: none
    Review: none
    English statement: (Erdos Problems #579)
      For every delta > 0, if n is large enough and G is a graph on n vertices with no K_{2,2,2} and at least
      delta n^2 edges, then G has an independent set of at least c n vertices, for a constant c = c(delta) > 0.
    Definitions: [complete_multipartite_graph 3 2] - K_{2,2,2}, the octahedron: three parts of size 2 (GTBase);
      [has_subgraph G H] - H is a (not necessarily induced) subgraph of G (GTBase.common); [edge_count G] - the
      number of edges (GTBase); [stable S] - no two vertices of S are adjacent (upstream).
    Notes: the pinned statement is the erdosproblems.com text ("Let delta > 0.  If n is sufficiently large and G is
      a graph on n vertices with no K_{2,2,2} and at least delta n^2 edges then G contains an independent set of
      size >>_delta n").  delta = 1/q, so "at least delta n^2 edges" is n^2 <= q e; ">>_delta n" is n <= c |S|,
      with c and n0 depending on q only.  For q <= 3 the hypotheses fail for large n by mathematics, since
      ex(n; K_{2,2,2}) = n^2/4 + o(n^2) (K_{2,2,2} is 3-chromatic), not by the encoding.  Literature status: open
      at the teorth/erdosproblems mirror (10fb9c15); the problem page reports the case delta > 1/8 (Erdos, Hajnal,
      Sos and Szemeredi). *)
Definition octahedron_free_dense_linear_independent_set_statement : Prop :=
  forall q : nat, 1 <= q -> exists c n0 : nat,
    forall G : sgraph, n0 <= #|G| -> ~ has_subgraph G (complete_multipartite_graph 3 2) ->
      #|G| ^ 2 <= q * edge_count G ->
      exists S : {set G}, stable S /\ #|G| <= c * #|S|.

(** Corpus row: erdos:911
    Site: none
    Review: none
    English statement: (Erdos Problems #911)
      There is a function f with f(x)/x -> oo such that, for all large C, every graph G with n vertices and
      e >= C n edges has size Ramsey number R^(G) > f(C) e, where R^(G) is the least number of edges of a graph
      every 2-colouring of whose edges has a monochromatic copy of G.
    Definitions: [xe1_size_ramsey_number G G m] - m = R^(G) (Extremal.conjectures.XE1); [edge_count G] - the number
      of edges (GTBase).
    Notes: the pinned statement is the erdosproblems.com question ("Is there a function f such that f(x)/x -> oo as
      x -> oo such that, for all large C, if G is a graph with n vertices and e >= Cn edges then R^(G) > f(C) e?");
      the affirmative form is stated, f eliminated: for every M, eventually (C >= C0) every nonempty G with
      e >= C n has R^(G) > M C e.  The two are equivalent: the best f is f*(C) = inf R^(G)/e over the graphs with
      e >= C n, nondecreasing in C, and the question is f*(C)/C -> oo; integer C suffice by monotonicity.  0 < |G|
      excludes the empty graph, whose R^ is 0.  Literature status: open at the teorth/erdosproblems mirror
      (10fb9c15). *)
Definition size_ramsey_superlinear_density_statement : Prop :=
  forall M : nat, exists C0 : nat,
    forall (C : nat) (G : sgraph) (m : nat), C0 <= C -> 0 < #|G| -> C * #|G| <= edge_count G ->
      xe1_size_ramsey_number G G m -> M * C * edge_count G < m.

(** Corpus row: erdos:1182
    Site: none
    Review: none
    English statement: (Erdos Problems #1182)
      Let F(n) be maximal such that every connected graph G with n vertices and at most F(n) edges has
      R(K_3, G) = 2n - 1.  Then F(n)/n -> oo.
    Definitions: [xe1_graph_ramsey_number 'K_3 G R] - R = R(K_3, G): every graph on R vertices contains a triangle
      or its complement contains G, and R is least (Extremal.conjectures.XE1); [connected [set: G]] - G is
      connected (upstream); [edge_count G] - the number of edges (GTBase).
    Notes: the pinned statement is the erdosproblems.com text ("Let f(n) be maximal such that there is a connected
      graph G with n vertices and f(n) edges such that R(K_3,G) = 2n-1.  Let F(n) be maximal such that every
      connected graph G with n vertices and <= F(n) edges has R(K_3,G) = 2n-1.  Estimate f(n) and F(n).  In
      particular, is it true that F(n)/n -> oo?").  The specific question is stated in affirmative form (as
      erdos:715, X183): for every M, eventually every connected n-vertex G with at most M n edges has
      R(K_3, G) = 2n - 1, written R + 1 = 2n; "Estimate f(n) and F(n)" is not formalized.  R(K_3, G) >= 2n - 1 for
      every connected G, so the equality is the K_3-goodness of G.  Literature status: FALSE AS STATED, BEFORE the
      corpus pin, not in the pinned status (the mirror 10fb9c15 lists "open", 2026-03-07): Brandt, "Expanding graphs
      and Ramsey numbers", Preprint A 96-24, FU Berlin, December 1996, p.3 defines f(n;3) = F(n), p.4 states
      f(n;3)/n < 84, and section 5 (pp.7-8) proves it eventually, with random regular graphs of degree d >= 168
      (literature evidence, not kernel-checked; the stronger 11.75 of p.4 is not proved there and not claimed).  The
      problem page credits Brandt with the negative answer.  The row is encoded as stated. *)
Definition triangle_goodness_sparse_connected_statement : Prop :=
  forall M : nat, exists n0 : nat,
    forall (G : sgraph) (R : nat), n0 <= #|G| -> connected [set: G] -> edge_count G <= M * #|G| ->
      xe1_graph_ramsey_number 'K_3 G R -> R + 1 = 2 * #|G|.

(** Corpus row: erdos:166
    Site: none
    Review: none
    English statement: (Erdos Problems #166)
      R(4,k) >> k^3 / (log k)^{O(1)}: there are c and p > 0 with R(4,k) >= k^3 / (p (log k)^c) for all large k,
      where R(4,k) is the least N such that every graph on N vertices contains K_4 or an independent set of k
      vertices.
    Definitions: [xe1_graph_ramsey_number 'K_4 'K_k R] - R = R(4,k) (Extremal.conjectures.XE1); [trunc_log 2 k] -
      the floor of log2 k (MathComp).
    Notes: the pinned statement is the erdosproblems.com text ("Prove that R(4,k) >> k^3/(log k)^{O(1)}").  One
      exponent c serves all large k; the base and floor of the logarithm are absorbed by p (log2 k / 2 <=
      trunc_log 2 k <= log2 k for k >= 2).  Literature status: PROVED BEFORE the corpus pin: Mattheus and
      Verstraete, "The asymptotics of r(4,t)", arXiv:2306.04007v4 (v1 2023-06-06), Theorem thm:main (l.148-151):
      "As t -> oo, r(4,t) = Omega(t^3 / log^4 t)" (the row with c = 4); the mirror (10fb9c15) lists "proved".
      X240's erdos:986 at k = 4 implies this row. *)
Definition ramsey_four_cubic_polylog_lower_statement : Prop :=
  exists c p k0 : nat, 0 < p /\
    forall k R : nat, k0 <= k -> xe1_graph_ramsey_number 'K_4 'K_k R ->
      k ^ 3 <= p * R * trunc_log 2 k ^ c.

(** Corpus row: erdos:546
    Site: none
    Review: none
    English statement: (Erdos Problems #546)
      Every graph G with no isolated vertices and m edges has R(G) <= 2^{O(m^{1/2})}, where R(G) is the least N such
      that every 2-colouring of the edges of K_N has a monochromatic copy of G.
    Definitions: [min_degree_at_least G 1] - G has no isolated vertex (GTBase); [xe1_diagonal_ramsey_number G R] -
      R = R(G) (Extremal.conjectures.XE1); [trunc_log 2 R] - the floor of log2 R (MathComp).
    Notes: the pinned statement is the erdosproblems.com question ("Let G be a graph with no isolated vertices and m
      edges.  Is it true that R(G) <= 2^{O(m^{1/2})}?"); the affirmative form is stated.  R <= 2^{C' sqrt m} is
      log2 R <= C' sqrt m, squared: (trunc_log 2 R)^2 <= C m (the floor costs a constant factor for m >= 1; m = 0
      with no isolated vertex is the empty graph, R = 0).  Literature status: PROVED BEFORE the corpus pin:
      Sudakov, "A conjecture of Erdos on graph Ramsey numbers", arXiv:1002.0095v1 (2010-01-30), Theorem main
      (main.tex l.118-120): "If G is a graph on m edges without isolated vertices, then r(G) <= 2^{250 sqrt m}";
      the mirror (10fb9c15) lists "proved". *)
Definition ramsey_sqrt_edges_exponential_upper_statement : Prop :=
  exists C : nat, forall (G : sgraph) (R : nat), min_degree_at_least G 1 ->
    xe1_diagonal_ramsey_number G R -> trunc_log 2 R ^ 2 <= C * edge_count G.

(** Corpus row: erdos:1014
    Site: none
    Review: none
    English statement: (Erdos Problems #1014)
      For every fixed k >= 3, R(k, l+1) / R(k, l) -> 1 as l -> oo, where R(k, l) is the least n such that every
      graph on at least n vertices contains K_k or an independent set of l vertices.
    Definitions: [xe1_graph_ramsey_number 'K_k 'K_l R0] - R0 = R(k, l) (Extremal.conjectures.XE1).
    Notes: the pinned statement is the erdosproblems.com text ("Prove, for fixed k >= 3, that lim_{l -> oo}
      R(k,l+1)/R(k,l) = 1").  The ratio is at least 1 (monotonicity), so the limit 1 is "for every q >= 1,
      eventually q R(k, l+1) <= (q + 1) R(k, l)".  Literature status: PROVED BEFORE the corpus pin per the
      teorth/erdosproblems mirror (10fb9c15: "proved (Lean)", 2026-04-24); the problem page (a search-index record of
      it, deposited by the Mac) credits an internal OpenAI model and gives R(k, l+1) <= (1 + O(l^{-c/k^2})) R(k, l);
      no paper and no Lean proof were fetched or checked.  The row is encoded as stated. *)
Definition off_diagonal_ramsey_consecutive_ratio_one_statement : Prop :=
  forall k : nat, 3 <= k -> forall q : nat, 1 <= q -> exists l0 : nat,
    forall l R0 R1 : nat, l0 <= l ->
      xe1_graph_ramsey_number 'K_k 'K_l R0 -> xe1_graph_ramsey_number 'K_k 'K_l.+1 R1 ->
      q * R1 <= (q + 1) * R0.
