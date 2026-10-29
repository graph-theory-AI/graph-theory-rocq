(** * Chromatic.conjectures.X258 -- wave X258: k-chromatic graphs with long odd cycles, without triangles, or critical (2026-10-29)

    A four-row wave under the prospective contract of meta/faithfulness_policy.json.  Rows: erdos:921 (the largest
    odd-girth bound f_k(n) of a k-chromatic graph on n vertices is of order n^(1/(k-2))), erdos:1013 (the least order
    h_3(k) of a triangle-free k-chromatic graph: h_3(k+1) / h_3(k) -> 1), erdos:917 (the largest edge count f_k(n) of
    an edge-critical k-chromatic graph, the three questions as asked) and erdos:744 (the least number f_k(n) of edges
    whose deletion makes a k-critical graph bipartite, as asked).  Shared vocabulary is reused: the chromatic number
    chi([set: G]) of coq-graph-theory, GTBase's [ucycle], [triangle_free], [edge_count], [del_edges] (deleting the
    edges inside a vertex set) and [bipartite_after_deletion] (GTBase.bipartitions), and Chromatic.conjectures.X219's
    [x219_subgraph_critical_for] (criticality for a subgraph-monotone property).  Local notions have no shared
    counterpart: odd girth above a bound, edge-criticality alone (X219's notion adds vertex deletions; XE1's
    [xe1_edge_critical_set] is about a set of edges, X6's notion is for hypergraphs) and the four relational numbers.
    Pinned statuses: 921 and 744 solved, 1013 and 917 open; literature lines are dated against the corpus pin
    (graph-conjectures b72c5857, 2026-09-23).  The sources are the Mac's deposit
    coordination/sources/x258-source-mac-20261029 (text line numbers below).  The grounding certificates are in
    grounding_X258.v. *)

From GTBase Require Import base common bipartitions.
From Chromatic.conjectures Require Import X219.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local x258 vocabulary ************************************************* *)

(** Every odd cycle of G has length greater than m (a [ucycle] of odd size; a one-vertex [ucycle] would be a loop, so
    odd cycles have length at least 3 and no size guard is needed). *)
Definition x258_odd_cycles_longer (G : sgraph) (m : nat) : Prop :=
  forall c : seq G, ucycle (--) c -> odd (size c) -> m < size c.

(** f = f_k(n) of erdos:921: there is a graph on n vertices with chromatic number k whose odd cycles are all longer
    than f, and no such graph has all its odd cycles longer than any m > f. *)
Definition x258_odd_girth_number (k n f : nat) : Prop :=
  (exists G : sgraph, [/\ #|G| = n, χ([set: G]) = k & x258_odd_cycles_longer G f]) /\
  forall (G : sgraph) (m : nat), #|G| = n -> χ([set: G]) = k -> x258_odd_cycles_longer G m -> m <= f.

(** n = h_3(k) of erdos:1013: the least order of a triangle-free graph with chromatic number k. *)
Definition x258_triangle_free_order (k n : nat) : Prop :=
  (exists G : sgraph, [/\ #|G| = n, triangle_free G & χ([set: G]) = k]) /\
  forall G : sgraph, triangle_free G -> χ([set: G]) = k -> n <= #|G|.

(** Deleting any edge uv (GTBase's [del_edges [set u; v]], the same edge deletion as X219's) brings the chromatic
    number below k; with chi = k this is erdos:917's "deleting any edge reduces the chromatic number". *)
Definition x258_edge_critical (G : sgraph) (k : nat) : Prop :=
  forall u v : G, u -- v -> χ([set: del_edges [set u; v]]) < k.

(** f = f_k(n) of erdos:917: the largest edge count of a graph on n vertices with chromatic number k that is
    edge-critical. *)
Definition x258_critical_edge_number (k n f : nat) : Prop :=
  (exists G : sgraph, [/\ #|G| = n, χ([set: G]) = k, x258_edge_critical G k & edge_count G = f]) /\
  forall G : sgraph, #|G| = n -> χ([set: G]) = k -> x258_edge_critical G k -> edge_count G <= f.

(** m = f_k(n) of erdos:744: the least m such that some graph on n vertices with chromatic number k, every proper
    subgraph of which has chromatic number below k (X219's criticality for the property chi < k), becomes bipartite
    after deleting a set of at most m pairs. *)
Definition x258_critical_bipartizing_number (k n m : nat) : Prop :=
  (exists G : sgraph,
     [/\ #|G| = n, χ([set: G]) = k, x219_subgraph_critical_for (fun H : sgraph => χ([set: H]) < k) G &
         exists S : {set {set G}}, #|S| <= m /\ bipartite_after_deletion S]) /\
  forall G : sgraph, #|G| = n -> χ([set: G]) = k ->
    x219_subgraph_critical_for (fun H : sgraph => χ([set: H]) < k) G ->
    forall S : {set {set G}}, bipartite_after_deletion S -> m <= #|S|.

(** ** X258 statements ******************************************************* *)

(** Corpus row: erdos:921
    Site: none
    Review: none
    English statement: (Erdos Problems #921, Erdos and Gallai)
      Let k >= 4 and let f_k(n) be the largest m such that there is a graph on n vertices with chromatic number k in
      which every odd cycle has length > m.  Is it true that f_k(n) asymp n^(1/(k-2))?
    Definitions: [x258_odd_girth_number k n f] - f = f_k(n) (this file); [x258_odd_cycles_longer G m] - every odd
      cycle of G has length greater than m (this file); chi([set: G]) - the chromatic number (coq-graph-theory).
    Notes: f_k(n) asymp n^(1/(k-2)) is encoded with natural constants: for every k >= 4 there are A, B and N such that
      n <= A f_k(n)^(k-2) and f_k(n)^(k-2) <= B n for every n >= N (a n^(1/d) <= f <= b n^(1/d) with reals a, b > 0 is
      the same up to A = ceil(a^-d), B = ceil(b^d)).  A, B depend on k, as in the sources (Er69b p.31: "for every k
      there is a G_n with chi(G_n) = k the smallest odd circuit of which has length greater than c_1 n^(1/(k-2)); but
      that there is a c_2 ...", Er69b.txt l.190-192, page scan Er69b-page5.png).  For n < k no graph has chromatic
      number k, the relation is empty and the clause is vacuous below N.  Literature status: proved before the pin
      (pinned status solved, "PROVED ... in the affirmative"; the page, erdos-921.txt l.34-38: Gallai f_4(n) >> n^(1/2),
      Erdos f_4(n) << n^(1/2), all k >= 4 by Kierstead, Szemeredi and Trotter).  Kierstead, Szemeredi and Trotter, On
      coloring graphs with locally small chromatic number, Combinatorica 4 (1984) 183-185 (author PDF, read from the
      page scans KST84-author-direct-page1.png and -page2.png), with their parameter d = k - 2: Theorem 1 at c = 2
      ("Erdos' conjecture is the special case c = 2, with c_k = 4k") gives chi(G) <= d + 1 when G has no odd cycle
      shorter than 4d n^(1/d), so f_k(n) < 4(k-2) n^(1/(k-2)); Example 3 (Gallai for d = 2, Lovasz and Schrijver in
      general) gives a graph on n vertices with chi(G) = d + 2 whose subgraphs of radius below n^(1/d) / 2 are
      bipartite, hence with no odd cycle shorter than n^(1/d).  Also f_k(n) <= f_k(n+1) for n >= k: an added isolated
      vertex keeps the chromatic number and the odd cycles; so the lower side for every large n needs the construction
      only along orders n_j with bounded ratios n_(j+1) / n_j.  The exponent k - 2 is a truncated subtraction, guarded
      by 4 <= k. *)
Definition chromatic_odd_girth_order_statement : Prop :=
  forall k : nat, 4 <= k -> exists A B N : nat, forall n f : nat, N <= n ->
    x258_odd_girth_number k n f -> n <= A * f ^ (k - 2) /\ f ^ (k - 2) <= B * n.

(** Corpus row: erdos:1013
    Site: none
    Review: none
    English statement: (Erdos Problems #1013, Erdos)
      Let h_3(k) be the minimal n such that there exists a triangle-free graph on n vertices with chromatic number k.
      Find an asymptotic for h_3(k), and also prove lim_{k -> oo} h_3(k+1) / h_3(k) = 1.
    Definitions: [x258_triangle_free_order k n] - n = h_3(k) (this file); [triangle_free G] - no three mutually
      adjacent vertices (GTBase.base); chi([set: G]) - the chromatic number (coq-graph-theory).
    Notes: the proof clause is encoded, as asked: h_3(k+1) / h_3(k) -> 1 is its upper half, "for every q >= 1,
      eventually q h_3(k+1) <= (q + 1) h_3(k)"; the lower half holds for every k, h_3(k) <= h_3(k+1)
      (grounding_X258's g258_order_mono: removing vertices one at a time lowers chi by at most one each time, so a
      triangle-free (k+1)-chromatic graph has a k-chromatic induced subgraph, triangle-free with it).  "Find an
      asymptotic" is not formalised.  Erdos, Unsolved problems in graph theory and combinatorial analysis (1971),
      item 6, pp.98-99 (Er71.txt l.70-80; page scan Er71-page3.png): g(3,n) is "the smallest integer for which there is
      a graph of g(3,n) vertices which contains no triangle and has chromatic number n", and "it might be of some
      interest to prove lim g(3,n+1)/g(3,n) = 1"; the page's h_3(k) is the same function.  Literature status: open at
      the pin (pinned status open).  The page (erdos-1013.txt l.35-39) cites Graver and Yackel, h_3(k) >>
      (log k / log log k) k^2 (not read), and (1/2 - o(1)) k^2 log k <= h_3(k) <= (1 + o(1)) k^2 log k from the bounds
      of erdos:1104 (Davies and Illingworth; Hefty, Horn, King and Pfender, both in the deposit); a factor 2 apart,
      these do not settle the ratio. *)
Definition triangle_free_chromatic_order_ratio_statement : Prop :=
  forall q : nat, 1 <= q -> exists K : nat, forall k a b : nat, K <= k ->
    x258_triangle_free_order k a -> x258_triangle_free_order k.+1 b -> q * b <= (q + 1) * a.

(** Corpus row: erdos:917
    Site: none
    Review: none
    English statement: (Erdos Problems #917, Erdos; Dirac's critical graphs)
      Let k >= 4 and f_k(n) be the largest number of edges in a graph on n vertices which has chromatic number k and
      is critical (i.e. deleting any edge reduces the chromatic number).  Is it true that f_k(n) >>_k n^2?  Is it true
      that f_6(n) ~ n^2/4?  More generally, is it true that, for k >= 6, f_k(n) ~ (1/2)(1 - 1/floor(k/3)) n^2?
    Definitions: [x258_critical_edge_number k n f] - f = f_k(n) (this file); [x258_edge_critical G k] - deleting any
      edge brings chi below k (this file); [edge_count G] - the number of edges (GTBase.common).
    Notes: the three asked clauses are encoded as stated, each with its own range: for k >= 4, f_k(n) >>_k n^2 ("there
      are C and N with n^2 <= C f_k(n) for n >= N"); f_6(n) ~ n^2 / 4 and, for k >= 6 and t = floor(k/3),
      f_k(n) ~ (t - 1) n^2 / (2 t), each as the two-sided "for every q >= 1, eventually q/(q+1) <= f_k(n) / g(n) <=
      (q+1)/q", cross-multiplied.  The second clause is the third at k = 6 (t = 2).  Criticality is the pinned one,
      as in Erdos, Some problems on chromatic graphs (1969), p.28 (Er69b.txt l.48-52; page scan Er69b-page2.png):
      "G. Dirac calls the k-chromatic graph G critical if for every edge R of G, chi(G - R) < chi(G)".  It allows
      isolated vertices: K_k with n - k isolated vertices qualifies, so f_k(n) exists for every n >= k (the relation
      is empty below k, vacuous below N).  Luo, Ma and Yang (arXiv:2301.01656v1, source.tex l.77) use k-critical,
      "every its proper subgraph is (k-1)-colorable", which excludes isolated vertices and has no graph on k + 1
      vertices (l.86); deleting the isolated vertices of an edge-critical graph leaves a k-critical one, so the
      pinned f_k(n) is the maximum of theirs over n' <= n, and lower bounds pass from theirs to the pinned one.
      Literature, clause by clause: (1) TRUE: Toft (1970) "proved that for every k >= 4, there exists a positive
      constant c_k such that f_k(n) >= c_k n^2 holds for all integers n >= k (except n = k+1)" (LMY l.86; the page,
      erdos-917.txt l.42-43).  (2) open: Dirac's f_6(4n+2) >= 4n^2 + 8n + 3 (the page l.36-38; Er69b p.28) against
      Stiebitz's f_k(n) < e(T_{k-2}(n)) (LMY l.114-116) and LMY's Theorem 1.1, f_k(n) <= e(T_{k-2}(n)) - c_k n^2 with
      c_k >= 1/(36(k-1)^2) (l.131-133); "It is also an open question if lim f_k(n)/n^2 exits for any k >= 4" (l.93).
      (3) FALSE for every k >= 7 with 3 not dividing k: Toft's constructions give infinitely many n with f_k(n) >=
      (1/2 - 3/(2k - delta_k)) n^2, delta_k = 0, 8/7, 44/23 for k = 0, 1, 2 mod 3 (LMY l.89-91); at k = 7 this is
      (4/15) n^2 > n^2 / 4, the clause's value.  The page attributes the same coefficients to Stiebitz [St87],
      written (1/2)(1 - 1/(floor(k/3) + delta_k)) with delta_k = 0, 1/7, 24/69, "which disproves Erdos' conjectured
      asympotic for k not = 0 (mod 3)" (l.44-46); Toft's and Stiebitz's papers were not read.  The row is FALSE at the
      pin (pinned status open; the page keeps the problem open for its other questions).  In the third clause
      k %/ 3 - 1 = t - 1 is a truncated subtraction, guarded by 6 <= k (t >= 2). *)
Definition critical_graph_edge_count_statement : Prop :=
  [/\ forall k : nat, 4 <= k -> exists C N : nat, forall n f : nat, N <= n ->
        x258_critical_edge_number k n f -> n ^ 2 <= C * f,
      forall q : nat, 1 <= q -> exists N : nat, forall n f : nat, N <= n ->
        x258_critical_edge_number 6 n f -> q * (4 * f) <= (q + 1) * n ^ 2 /\ q * n ^ 2 <= (q + 1) * (4 * f) &
      forall k q : nat, 6 <= k -> 1 <= q -> exists N : nat, forall n f : nat, N <= n ->
        x258_critical_edge_number k n f ->
        q * (2 * (k %/ 3) * f) <= (q + 1) * ((k %/ 3 - 1) * n ^ 2) /\
        q * ((k %/ 3 - 1) * n ^ 2) <= (q + 1) * (2 * (k %/ 3) * f)].

(** Corpus row: erdos:744
    Site: none
    Review: none
    English statement: (Erdos Problems #744, Erdos, Hajnal and Szemeredi)
      Let k be a large fixed constant.  Let f_k(n) be the minimal m such that there exists a graph G on n vertices with
      chromatic number k, such that every proper subgraph has chromatic number < k, and G can be made bipartite by
      deleting m edges.  Is it true that f_k(n) -> oo as n -> oo?  In particular, is it true that f_4(n) >> log n?
    Definitions: [x258_critical_bipartizing_number k n m] - m = f_k(n) (this file); [x219_subgraph_critical_for P G]
      - P fails on G and holds on every one-vertex and every one-edge deletion, here with P H := chi(H) < k
      (Chromatic.conjectures.X219; for a subgraph-monotone P, as X219 notes, exactly "every proper subgraph");
      [bipartite_after_deletion S] - a bipartition of G with the pairs of S deleted (GTBase.bipartitions).
    Notes: the two asked clauses are encoded as stated: for every sufficiently large k (the pinned "Let k be a large
      fixed constant": some K, every k >= K), f_k(n) -> oo, "for every M, eventually M <= f_k(n)"; and f_4(n) >> log n,
      read as "there are C and N with n <= 2^(C f_4(n)) for n >= N".  The second clause names k = 4 as printed; the
      status below is the same under the reading "every k >= 4".  S may hold non-edges and sets that are not pairs;
      they delete nothing, so the least #|S| is the least number of edges.  When no k-critical graph has n vertices
      (for instance n < k), the relation is empty; the clauses are asymptotic.  The page (erdos-744.txt
      l.36): "Odd cycles show that f_3(n) = 1" (g258_bipartizing_K3 is its n = 3 instance).  Literature status: refuted
      before the pin (pinned status solved, "DISPROVED ... in the negative"): "This conjecture was disproved by Rodl
      and Tuza [RoTu85], who proved that in fact f_k(n) = binomial(k-1, 2) (for all sufficiently large n)" (l.38-40),
      so f_k(n) is eventually constant for every k and f_4(n) = 3 for large n.  Rodl and Tuza, On color critical
      graphs, J. Combin. Theory Ser. B 38 (1985) 204-213, was not obtained (publisher HTTP 403; SOURCE.md), and the
      catalog formulation was not located in EHS82 (the page's source; Erdos, Hajnal and Szemeredi 1982, deposited):
      the reading rests on the page.  The row is FALSE at the pin, as pinned. *)
Definition critical_graph_bipartizing_edges_statement : Prop :=
  (exists K : nat, forall k : nat, K <= k -> forall M : nat, exists N : nat, forall n m : nat, N <= n ->
     x258_critical_bipartizing_number k n m -> M <= m) /\
  (exists C N : nat, forall n m : nat, N <= n -> x258_critical_bipartizing_number 4 n m -> n <= 2 ^ (C * m)).
