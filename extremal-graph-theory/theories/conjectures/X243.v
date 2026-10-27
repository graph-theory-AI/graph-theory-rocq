(** * Extremal.conjectures.X243 -- wave X243: induced subgraphs of Ramsey graphs, C_6 in the hypercube, triangle-free graphs of diameter 2, triangles in dense graphs (2026-10-27)

    A six-row wave under the prospective contract of meta/faithfulness_policy.json.  Rows: erdos:88 (Ramsey graphs
    induce every edge count up to delta n^2), erdos:636 (n^{5/2} induced subgraphs with distinct (size, edges)
    pairs), erdos:637 (an induced subgraph on >> n vertices with >> n^{1/2} distinct degrees), erdos:666 (C_6 in
    dense subgraphs of the hypercube), erdos:133 (maximum degree of triangle-free graphs of diameter 2) and erdos:1034
    (a triangle with about n/2 vertices joined to two of its vertices).  No local helper and no copied vocabulary:
    GTBase supplies [edge_count], [has_subgraph], 'K_n, [cycle_graph], [del_edge_set], [product_hypercube]
    (GTBase.hypercubes) and [graph_dist] (GTBase.graph_metric); [cliqueb], [stable], [induced] and N(x) are upstream;
    the distinct-value count size (undup ...) is MathComp's (the idiom of Chromatic.conjectures.U1's
    valency_variety, written inline).  Rows erdos:88, erdos:636 and erdos:637 share the hypothesis "no clique or
    independent set on >= C log n vertices", written [forall S, cliqueb S || stable S -> 2 ^ #|S| < #|G| ^ C].  All
    six rows have pinned status "solved"; their literature lines are dated against the corpus pin (graph-conjectures
    b72c5857, 2026-09-23).  The grounding certificates are in grounding_X243.v. *)

From GTBase Require Import base common hypercubes graph_metric.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** X243 statements ******************************************************* *)

(** Corpus row: erdos:88
    Site: none
    Review: none
    English statement: (Erdos Problems #88, Erdos and McKay)
      For every eps > 0 there is delta > 0 such that every graph G on n vertices with no clique and no independent
      set of size at least eps log n contains, for every m <= delta n^2, an induced subgraph with exactly m edges.
    Definitions: [cliqueb S] - S is a clique (upstream sgraph); [stable S] - no two vertices of S are adjacent
      (upstream); [induced S] - the subgraph of G induced by S (upstream); [edge_count H] - the number of edges
      (GTBase).
    Notes: the pinned statement is the erdosproblems.com text ("For any eps > 0 there exists delta = delta(eps) > 0
      such that if G is a graph on n vertices with no independent set or clique of size >= eps log n then G contains
      an induced subgraph with m edges for all m <= delta n^2").  "No clique or independent set of size >= eps log n"
      is written with an integer C over log_2: every homogeneous S has |S| < C log_2 n, i.e. 2^{|S|} < n^C.  This
      loses nothing: a change of log base rescales eps, the statement is monotone in eps (a larger eps weakens the
      hypothesis), so integer C covers every real eps > 0 (C = 0 is vacuous).  S = set0 is a clique, so the hypothesis
      also asks 1 < n^C and excludes n <= 1, where the claim is trivial anyway (p >= 2 gives m = 0).  delta = 1/p with
      p >= 1.  The text has no "n sufficiently large" and none is added: for small n, p > n^2 forces m = 0, met by
      S = set0.
      Literature status: PROVED BEFORE the corpus pin (pinned status "solved"): Kwan, Sah, Sauermann and Sawhney,
      "Anticoncentration in Ramsey graphs and a proof of the Erdos-McKay conjecture", arXiv:2208.02874v2 (v1
      2022-08-04, v2 2024-05-30), Theorem 1.1 (main.tex l.253-254): for fixed C, eta > 0 and a C-Ramsey graph G on n
      vertices (no homogeneous subgraph of size C log_2 n, l.193), n large, "for any integer x with 0 <= x <=
      (1 - eta) e(G), there is a subset U of V(G) inducing exactly x edges"; its footnote 2 (l.251) derives this
      row's delta n^2 form (e(G) >= eps_C n^2 / 4 by Erdos-Szemeredi, eta = 1/2, and delta_C n_C^2 < 1 for the
      finitely many small n).  The mirror (10fb9c15) lists "proved". *)

Definition ramsey_graph_induced_every_edge_count_statement : Prop :=
  forall C : nat, exists p : nat, 1 <= p /\
    forall (G : sgraph) (m : nat),
      (forall S : {set G}, cliqueb S || stable S -> 2 ^ #|S| < #|G| ^ C) ->
      p * m <= #|G| ^ 2 -> exists S : {set G}, edge_count (induced S) = m.

(** Corpus row: erdos:636
    Site: none
    Review: none
    English statement: (Erdos Problems #636, Erdos, Faudree and Sos)
      If an n-vertex graph G has no clique and no independent set on >= C log n vertices, then G has >> n^{5/2}
      induced subgraphs which pairwise differ in their number of vertices or in their number of edges (the implied
      constant depending on C).
    Definitions: [cliqueb S], [stable S], [induced A] (upstream); [edge_count H] (GTBase); [size (undup s)] - the
      number of distinct entries of the list s (MathComp).
    Notes: the pinned statement is the erdosproblems.com question ("Suppose G is a graph on n vertices which contains
      no complete graph or independent set on >> log n many vertices.  Must G contain >> n^{5/2} induced subgraphs
      which pairwise differ in either the number of vertices or the number of edges?"); the affirmative form is
      stated.  ">> log n" is "some constant C", written as for erdos:88 (integer C over log_2).  A family of induced
      subgraphs with pairwise different (vertex count, edge count) has at most one member per distinct pair, and one
      induced subgraph per pair realises the number of distinct pairs, so the largest such family has size
      size (undup [seq (#|A|, edge_count (induced A)) | A ...]); n^{5/2} <= p N is squared: n^5 <= (p N)^2.
      Literature status: PROVED BEFORE the corpus pin (pinned status "solved"): Kwan and Sudakov, "Proof of a
      conjecture on induced subgraphs of Ramsey graphs", arXiv:1712.05656v4 (v1 2017-12-15, v4 2021-09-07), abstract
      (main.tex l.211-213): "in any C-Ramsey graph there are Omega(n^{5/2}) induced subgraphs, no pair of which have
      the same numbers of vertices and edges", with Psi(G) the set of pairs (v(H), e(H)) over the induced subgraphs H
      (l.270) and the proof's final inequality |Psi(G)| >= ... = Omega(n^{5/2}) (l.860); Theorem 1.1 (l.285-287)
      prints "|Psi(G)| = gamma n^{5/2}", a misprint for that lower bound (recorded in the Mac's deposit).  The mirror
      (10fb9c15) lists "proved". *)

Definition ramsey_graph_distinct_size_edge_pairs_statement : Prop :=
  forall C : nat, exists p : nat, 1 <= p /\
    forall G : sgraph,
      (forall S : {set G}, cliqueb S || stable S -> 2 ^ #|S| < #|G| ^ C) ->
      #|G| ^ 5 <= (p * size (undup [seq (#|A|, edge_count (induced A)) | A : {set G} <- enum [set: {set G}]])) ^ 2.

(** Corpus row: erdos:637
    Site: none
    Review: none
    English statement: (Erdos Problems #637, Erdos, Faudree and Sos)
      If an n-vertex graph G has no clique and no independent set on >= C log n vertices, then G has an induced
      subgraph on >> n vertices in which >> n^{1/2} distinct degrees occur (the implied constants depending on C).
    Definitions: [cliqueb S], [stable S], [induced S], N(x) - the neighbourhood of x, here in the induced subgraph
      (upstream); [size (undup s)] - the number of distinct entries of the list s (MathComp).
    Notes: the pinned statement is the erdosproblems.com text ("If G is a graph on n vertices which contains no
      complete graph or independent set on >> log n vertices then G contains an induced subgraph on >> n vertices
      which contains >> n^{1/2} distinct degrees").  ">> log n" as for erdos:88 (integer C over log_2); one constant
      p for both ">>": n <= p |S| and n^{1/2} <= p D, squared; the degrees are those of the induced subgraph.
      Literature status: PROVED BEFORE the corpus pin (pinned status "solved"): Bukh and Sudakov, "Induced subgraphs
      of Ramsey graphs with many distinct degrees", J. Combin. Theory Ser. B 97 (2007) 612-619 (author PDF), Theorem
      1.1 (p.2): "Let G be a graph on n vertices with hom(G) <= C log n, for some constant C. Then G contains an
      induced subgraph of order alpha n with beta sqrt(n) vertices of different degrees, where alpha and beta depend
      only on C" (logarithms to base 2, p.1; hom(G) <= C log n against this row's < only shifts C).  Jenssen,
      Keevash, Long and Yepremyan, arXiv:1910.01361v1, give n^{2/3} distinct degrees without the linear vertex count.
      The mirror (10fb9c15) lists "proved". *)

Definition ramsey_graph_induced_distinct_degrees_statement : Prop :=
  forall C : nat, exists p : nat, 1 <= p /\
    forall G : sgraph,
      (forall S : {set G}, cliqueb S || stable S -> 2 ^ #|S| < #|G| ^ C) ->
      exists S : {set G}, #|G| <= p * #|S| /\
        #|G| <= (p * size (undup [seq #|N(x)| | x <- enum [set: induced S]])) ^ 2.

(** Corpus row: erdos:666
    Site: none
    Review: none
    English statement: (Erdos Problems #666)
      For every eps > 0, if n is large enough, every subgraph of the n-dimensional hypercube Q_n (2^n vertices,
      n 2^{n-1} edges) with at least eps n 2^{n-1} edges contains a C_6.
    Definitions: [product_hypercube n] - Q_n (GTBase.hypercubes); [del_edge_set G (E(G) :\: F)] - the spanning
      subgraph of G with edge set F (GTBase); [has_subgraph H C] - C is a (not necessarily induced) subgraph of H
      (GTBase.common); [cycle_graph 6] - C_6 (GTBase).
    Notes: the pinned statement is the erdosproblems.com question ("Is it true that, for every eps > 0, if n is
      sufficiently large, every subgraph of Q_n with >= eps n 2^{n-1} many edges contains a C_6?"); the affirmative
      form is stated, as X239's erdos:86 (C_4) with C_6.  eps = 1/q (the statement is monotone in eps), and
      |F| >= n 2^{n-1} / q is written n 2^n <= 2 q |F|.  A subgraph is taken spanning, given by its edge set F, which
      is enough since containing a C_6 is monotone.
      Literature status: FALSE BEFORE the corpus pin (pinned status "solved"): Chung, "Subgraphs of a hypercube
      containing no small even cycles", J. Graph Theory 16 (1992) 273-286, Theorem 3 (p.274): "The edge set E(Q_n) of
      Q_n can be partitioned into four subgraphs, each of which contains no C_6", so f_6(n) >= e(Q_n)/4 and Erdos's
      question "is answered in the negative"; Brouwer, Dejter and Thomassen, "Highly symmetric subgraphs of
      hypercubes", J. Algebraic Combin. 2 (1993) 25-29, Section 3 (p.28): a 4-colouring of the edges of the n-cube
      with no monochromatic quadrangle or hexagon shows that the conjecture "is false for eps <= 1/4".  The row fails
      at q = 4.  Conder, J. Graph Theory 17 (1993) 477-479, uses three colours (from the publisher's abstract and the
      author's later account, not the journal text).  The mirror (10fb9c15) lists "disproved (Lean)" (2026-02-06). *)

Definition hypercube_dense_subgraph_C6_statement : Prop :=
  forall q : nat, 1 <= q -> exists n0 : nat,
    forall (n : nat) (F : {set {set product_hypercube n}}), n0 <= n -> F \subset E(product_hypercube n) ->
      n * 2 ^ n <= 2 * q * #|F| ->
      has_subgraph (del_edge_set (product_hypercube n) (E(product_hypercube n) :\: F)) (cycle_graph 6).

(** Corpus row: erdos:133
    Site: none
    Review: none
    English statement: (Erdos Problems #133)
      Let f(n) be the least integer such that every triangle-free graph on n vertices of diameter 2 has a vertex of
      degree at least f(n).  Then f(n)/sqrt(n) tends to infinity: for every c, if n is large enough, every
      triangle-free n-vertex graph of diameter 2 has a vertex of degree at least c sqrt(n).
    Definitions: [has_subgraph G 'K_3] - G contains a triangle (GTBase.common); [graph_dist x y] - the length of a
      shortest x-y path, truncated at #|G| when x and y lie in different components (GTBase.graph_metric); N(v) -
      the neighbourhood of v (upstream).
    Notes: the pinned statement is the erdosproblems.com question ("Let f(n) be minimal such that every
      triangle-free graph G with n vertices and diameter 2 contains a vertex with degree >= f(n).  What is the order
      of growth of f(n)?  Does f(n)/sqrt(n) -> infinity?").  The specific question is stated in affirmative form (as
      erdos:715, X183); "What is the order of growth" is not formalized.  f(n) is the least maximum degree over the
      class, so f(n)/sqrt(n) -> infinity is "for every c, eventually every member has a vertex of degree >= c sqrt(n)",
      squared: c^2 n <= deg(v)^2.  Diameter 2 is written "every distance is at most 2": for n >= 3 this excludes
      disconnected graphs (their truncated distance is n), and a triangle-free graph on n >= 3 vertices is not
      complete, so some distance is exactly 2; n0 is existential, so the statement is the one with "diameter exactly
      2".
      Literature status: FALSE BEFORE the corpus pin (pinned status "solved"): Furedi and Seress, "Maximal
      triangle-free graphs with restrictions on the degrees", J. Graph Theory 18 (1994) 11-24, Lemma 2.4 (p.14): "Let
      D >= 5 sqrt(n). Then F(n, D) < (4n^2/D) + 2n", F(n, D) being the least number of edges of a maximal
      triangle-free n-vertex graph of maximal valency <= D (abstract, p.11); so such a graph exists with
      D = ceil(5 sqrt(n)), and a maximal triangle-free graph on n >= 3 vertices has diameter 2 (two non-adjacent
      vertices have a common neighbour), hence f(n) <= 5 sqrt(n) + 1 and the row fails at c = 6.  The problem page
      also credits Hanson and Seyffarth (1984, f(n) <= (sqrt 2 + o(1)) sqrt(n); not read) and gives Furedi-Seress's
      2/sqrt(3) constant; the mirror (10fb9c15) lists "disproved". *)

Definition triangle_free_diameter_two_max_degree_statement : Prop :=
  forall c : nat, exists n0 : nat,
    forall G : sgraph, n0 <= #|G| -> ~ has_subgraph G 'K_3 -> (forall x y : G, graph_dist x y <= 2) ->
      exists v : G, c ^ 2 * #|G| <= #|N(v)| ^ 2.

(** Corpus row: erdos:1034
    Site: none
    Review: none
    English statement: (Erdos Problems #1034, Erdos and Faudree)
      For every eps > 0, if n is large enough, every graph on n vertices with more than n^2/4 edges contains a
      triangle T and more than (1/2 - eps) n vertices each joined to at least two vertices of T.
    Definitions: [edge_count G] - the number of edges (GTBase); [x -- y] - adjacency (upstream), a boolean counted as
      0 or 1 in the sum.
    Notes: the pinned statement is the erdosproblems.com question ("Let G be a graph on n vertices with > n^2/4 many
      edges.  Must there be a triangle T in G and vertices y_1, ..., y_t, where t > (1/2 - o(1)) n, such that every
      vertex is joined to at least two vertices of T?"); the affirmative form is stated, "every vertex" being every
      y_i.  The o(1) is "for every eps = 1/q, eventually": t > (1/2 - 1/q) n is written q n < 2 q t + 2 n (no
      subtraction), and n^2/4 < e(G) is n^2 < 4 e(G).  The set Y of the y_i may contain the triangle's vertices a, b, c
      (each is joined to the other two): at most 3 vertices, which the o(1) n absorbs for every q, eventually.
      Literature status: FALSE BEFORE the corpus pin (pinned status "solved"): Ma and Tang, "On Erdos problem #1034"
      (author note, 3 pages), Theorem 2.1 (p.1): for every eps > 0 and all large n there is a graph G on n vertices
      with e(G) > n^2/4 such that, for every triangle T, at most (2 - sqrt(5/2) + eps) n vertices (about 0.4189 n;
      the triangle's own vertices included, which covers this row's Y) are adjacent to at least two vertices of T; so
      the row fails at q = 20, for instance.  The problem page (last edited 2025-10-28) credits the note; the mirror
      (10fb9c15) lists "disproved (Lean)" (2025-12-04). *)

Definition dense_graph_triangle_half_two_neighbour_vertices_statement : Prop :=
  forall q : nat, 1 <= q -> exists n0 : nat,
    forall G : sgraph, n0 <= #|G| -> #|G| ^ 2 < 4 * edge_count G ->
      exists (a b c : G) (Y : {set G}),
        [/\ a -- b, b -- c, a -- c, q * #|G| < 2 * q * #|Y| + 2 * #|G| &
            forall y : G, y \in Y -> 2 <= (y -- a) + (y -- b) + (y -- c)].
