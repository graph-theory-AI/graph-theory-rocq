(** * Extremal.conjectures.X242 -- wave X242: regular subgraphs, cycle-family and degree Turan exponents, Ramsey-Turan for K_5, C_4-free subgraphs (2026-10-27)

    A five-row wave under the prospective contract of meta/faithfulness_policy.json.  Rows: erdos:182 (k-regular
    subgraphs of graphs with n^{1+o(1)} edges), erdos:574 (ex(n; {C_{2k-1}, C_{2k}})), erdos:147 (Turan exponents of
    bipartite graphs of minimum degree r), erdos:533 (triangle-free sets in dense K_5-free graphs) and erdos:1008
    (C_4-free subgraphs with >> m^{2/3} edges).  No local helper and no copied vocabulary: Turan numbers are
    Extremal.conjectures.D2tur's [is_turan_number n Fam m] (m = ex(n; Fam), an attained maximum over n-vertex graphs
    with no member of Fam as a subgraph); GTBase supplies [regular], [bipartite], [min_degree_at_least], [cycle_graph],
    [del_edge_set], [has_subgraph], [edge_count] and 'K_n; [induced] is upstream.  All five rows have pinned status
    "solved"; their literature lines are dated against the corpus pin (graph-conjectures b72c5857, 2026-09-23).  The
    grounding certificates are in grounding_X242.v. *)

From Extremal.conjectures Require Import D2tur.
(* GTBase last: its canonical [edge_count] must shadow D2tur's eta-alias of the same name. *)
From GTBase Require Import base common.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** X242 statements ******************************************************* *)

(** Corpus row: erdos:182
    Site: none
    Review: none
    English statement: (Erdos Problems #182)
      For every k >= 3, the maximum number of edges of an n-vertex graph with no k-regular subgraph is << n^{1+o(1)}:
      for every eps > 0, if n is large enough, every n-vertex graph with at least n^{1+eps} edges contains a nonempty
      k-regular subgraph.
    Definitions: [regular H k] - every vertex of H has exactly k neighbours (GTBase.base); [has_subgraph G H] - H is a
      (not necessarily induced) subgraph of G (GTBase.common); [edge_count G] - the number of edges (GTBase).
    Notes: the pinned statement is the erdosproblems.com text ("Let k >= 3.  What is the maximum number of edges that a
      graph on n vertices can contain if it does not have a k-regular subgraph?  Is it << n^{1+o(1)}?").  The specific
      question is stated in affirmative form (as erdos:715, X183); "What is the maximum" is not formalized.  eps = 1/q,
      so "at least n^{1+1/q} edges" is n^{q+1} <= e^q; 0 < |H| is required, the empty graph being k-regular.
      Literature status: PROVED BEFORE the corpus pin (pinned status "solved"): Janzer and Sudakov, "Resolution of the
      Erdos-Sauer problem on regular subgraphs", arXiv:2204.12455v2 (v1 2022-04-26), Theorem thm:logloglog error term
      (l.99-101): "any n-vertex graph with average degree at least C log log n contains such a subgraph" (a k-regular
      one, C = C(k)); the teorth/erdosproblems mirror (10fb9c15) lists "proved". *)
Definition regular_subgraph_superlinear_edges_statement : Prop :=
  forall k : nat, 3 <= k -> forall q : nat, 1 <= q -> exists n0 : nat,
    forall G : sgraph, n0 <= #|G| -> #|G| ^ q.+1 <= edge_count G ^ q ->
      exists H : sgraph, [/\ 0 < #|H|, regular H k & has_subgraph G H].

(** Corpus row: erdos:574
    Site: none
    Review: none
    English statement: (Erdos Problems #574, Erdos and Simonovits)
      For every k >= 2, ex(n; {C_{2k-1}, C_{2k}}) = (1 + o(1)) (n/2)^{1+1/k}: the maximum number of edges of an
      n-vertex graph with no cycle of length 2k-1 and no cycle of length 2k is asymptotic to (n/2)^{1+1/k}.
    Definitions: [is_turan_number n Fam m] - m = ex(n; Fam) (Extremal.conjectures.D2tur); the family
      [fun i : 'I_2 => cycle_graph (i + (2 * j + 3))] is {C_{2j+3}, C_{2j+4}} = {C_{2k-1}, C_{2k}} for k = j + 2
      (GTBase).
    Notes: the pinned statement is the erdosproblems.com question ("Is it true that, for k >= 2, ex(n; {C_{2k-1},
      C_{2k}}) = (1+o(1)) (n/2)^{1+1/k}"); the affirmative form is stated.  k = j + 2 (no subtraction); m ~
      (n/2)^{1+1/k} iff m^k ~ n^{k+1} / 2^{k+1}: for epsilon = 1/q the ratio lies in [q/(q+1), (q+1)/q] for large n,
      raised to the k-th power and multiplied out.  At j = 0 the family and the arithmetic are X239's erdos:573
      ({C_3, C_4}, (n/2)^{3/2}).  Literature status: FALSE BEFORE the corpus pin (pinned status
      "solved"): Lazebnik, Ustimenko and Woldar, "Properties of certain families of 2k-cycle free graphs", J. Combin.
      Theory Ser. B 60 (1994) 293-298 (the author-hosted copy deposited by the Mac, its pp.3-4, Corollary): bipartite
      C_{2k}-free graphs (bipartite, so also free of the odd cycle C_{2k-1}) with at least about (2/3^{4/3}) n^{4/3}
      edges for k = 3 and (4/5^{6/5}) n^{6/5} for k = 5, more than (n/2)^{1+1/k} = 2^{-4/3} n^{4/3} and 2^{-6/5} n^{6/5};
      for k = 3 also Furedi, Naor and Verstraete, "On the Turan number for the hexagon", Adv. Math. 203 (2006), Theorem
      1.2 (p.2: bipartite, parts m and 2m, 2 m^{4/3} = (2/3^{4/3}) N^{4/3} edges).  The mirror (10fb9c15) lists
      "disproved" (2026-03-28).  The row is encoded as stated. *)
Definition odd_even_cycle_free_turan_asymptotic_statement : Prop :=
  forall j q : nat, 1 <= q -> exists n0 : nat,
    forall n m : nat, n0 <= n ->
      is_turan_number n (fun i : 'I_2 => cycle_graph (i + (2 * j + 3))) m ->
      q ^ (j + 2) * n ^ (j + 3) <= 2 ^ (j + 3) * (q + 1) ^ (j + 2) * m ^ (j + 2) /\
      2 ^ (j + 3) * q ^ (j + 2) * m ^ (j + 2) <= (q + 1) ^ (j + 2) * n ^ (j + 3).

(** Corpus row: erdos:147
    Site: none
    Review: none
    English statement: (Erdos Problems #147, Erdos and Simonovits)
      If H is bipartite with minimum degree r (r >= 2), then there is eps = eps(H) > 0 such that
      ex(n; H) >> n^{2 - 1/(r-1) + eps}.
    Definitions: [bipartite H] - H has a proper 2-colouring (GTBase.base); [min_degree_at_least H d] - every vertex of
      H has at least d neighbours (GTBase.base); [is_turan_number n Fam m] - m = ex(n; Fam) (Extremal.conjectures.D2tur;
      here Fam is the single graph H).
    Notes: the pinned statement is the erdosproblems.com text ("If H is bipartite with minimum degree r then there
      exists eps = eps(H) > 0 such that ex(n;H) >> n^{2-1/(r-1)+eps}").  r = t + 2 >= 2 (r - 1 >= 1) and eps = 1/s;
      ex >> n^{2 - 1/(t+1) + 1/s} is n^{((2t+1) s + t + 1)/((t+1) s)} <= c m, raised to the (t+1) s-th power.
      "Minimum degree r" is read as "at least r": equivalent, since the exponent grows with r.  Literature status:
      FALSE BEFORE the corpus pin (pinned status
      "solved"): for r = 3, Janzer, arXiv:2109.06110v2 (v1 2021-09-13), Theorem thm:disproofES (l.88-90): "For any
      eps > 0 there is a 3-regular (bipartite) graph H for which ex(n,H) = O(n^{4/3+eps})" (4/3 + eps < 3/2); for every
      even r >= 4, Janzer, "Rainbow Turan number of even cycles, repeated patterns and blow-ups of cycles",
      arXiv:2006.01062v3 (v3 2021-04-12), Theorem thm:turanblowup2k and the paragraph after Conjecture con:nondegenerate
      (TeX l.180-191; p.4): the blow-up C_{2k}[r] has minimum degree 2r and ex(n, C_{2k}[r]) = O(n^{2 - 1/r + delta}) for
      large k, below n^{2 - 1/(2r-1)}.  The mirror (10fb9c15) lists "disproved (Lean)" (2026-08-24).  The row is
      encoded as stated. *)
Definition bipartite_min_degree_turan_exponent_statement : Prop :=
  forall (t : nat) (H : sgraph), bipartite H -> min_degree_at_least H (t + 2) ->
    exists s c n0 : nat, 1 <= s /\
      forall n m : nat, n0 <= n -> is_turan_number n (fun _ : 'I_1 => H) m ->
        n ^ ((2 * t + 1) * s + t + 1) <= (c * m) ^ ((t + 1) * s).

(** Corpus row: erdos:533
    Site: none
    Review: none
    English statement: (Erdos Problems #533)
      For every delta > 0, if n is large enough and G is a graph on n vertices with no K_5 and at least delta n^2
      edges, then G has a set of at least c n vertices containing no triangle, for a constant c = c(delta) > 0.
    Definitions: [has_subgraph G H] - H is a (not necessarily induced) subgraph of G (GTBase.common); [induced S] - the
      subgraph induced by S (upstream GraphTheory.core.sgraph.induced: Locate in this file's context resolves the
      unqualified name to it, not to digraph.induced or mgraph.induced); [edge_count G] - the number of edges (GTBase).
    Notes: the pinned statement is the erdosproblems.com text ("Let delta > 0.  If n is sufficiently large and G is a
      graph on n vertices with no K_5 and at least delta n^2 edges then G contains a set of >>_delta n vertices
      containing no triangle").  delta = 1/q, as erdos:579 (X241); "a set containing no triangle" is a vertex set
      whose induced subgraph has no K_3.  Literature status: FALSE BEFORE the corpus pin (pinned status "solved"):
      Balogh and Lenz, "On the Ramsey-Turan numbers of graphs and hypergraphs", arXiv:1109.4428v2 (v1 2011-09-20),
      intro.tex l.107 ("Determine if theta_3(K_5) > 0") and l.173 (1/64 <= theta_3(K_5)), and "Some exact Ramsey-Turan
      numbers", arXiv:1109.4472v2 (v1 2011-09-21), rt2-main.tex l.378 (1/16 <= theta_3(K_5) <= 1/12): K_5-free graphs
      with about theta n^2 edges whose triangle-free sets are all o(n); the threshold 1/12 is Liu, Reiher,
      Sharifzadeh and Staden, "Geometric constructions for Ramsey-Turan theory", arXiv:2103.10423v2.  The mirror
      (10fb9c15) lists "disproved (Lean)" (2026-08-23).  The row is encoded as stated. *)
Definition k5_free_dense_linear_triangle_free_set_statement : Prop :=
  forall q : nat, 1 <= q -> exists c n0 : nat,
    forall G : sgraph, n0 <= #|G| -> ~ has_subgraph G 'K_5 -> #|G| ^ 2 <= q * edge_count G ->
      exists S : {set G}, ~ has_subgraph (induced S) 'K_3 /\ #|G| <= c * #|S|.

(** Corpus row: erdos:1008
    Site: none
    Review: none
    English statement: (Erdos Problems #1008)
      Every graph with m edges contains a subgraph with at least c m^{2/3} edges that contains no C_4, for an absolute
      constant c > 0.
    Definitions: [edge_count G] - the number of edges (GTBase); [del_edge_set G (E(G) :\: F)] - the spanning subgraph of
      G with edge set F (GTBase); [has_subgraph H C] - C is a subgraph of H (GTBase.common); [cycle_graph 4] - C_4
      (GTBase).
    Notes: the pinned statement is the erdosproblems.com question ("Does every graph with m edges contain a subgraph
      with >> m^{2/3} edges which contains no C_4?"); the affirmative form is stated.  m^{2/3} <= c |F| is cubed:
      m^2 <= (c |F|)^3; the subgraph is spanning, given by its edge set F, enough since C_4-freeness is monotone; the
      edge count is a hypothesis "edge_count G = m".  Literature status: PROVED BEFORE the corpus pin (pinned status
      "solved"): Conlon, Fox and Sudakov, "Short proofs of some extremal results II", arXiv:1507.00547v2 (v1
      2015-07-02), Theorem th1 (main.tex l.138-140): "Every graph G with m edges contains a K_{r,r}-free subgraph of
      size at least (1/4) m^{r/(r+1)}" (r = 2: K_{2,2} = C_4, m^{2/3}/4); the mirror (10fb9c15) lists "proved (Lean)"
      (2026-01-17). *)
Definition c4_free_subgraph_two_thirds_statement : Prop :=
  exists c : nat, 1 <= c /\
    forall (G : sgraph) (m : nat), edge_count G = m ->
      exists F : {set {set G}}, [/\ F \subset E(G),
        ~ has_subgraph (del_edge_set G (E(G) :\: F)) (cycle_graph 4) & m ^ 2 <= (c * #|F|) ^ 3].
