(** * Extremal.conjectures.X286 -- v2 rows: Erdos #615 (K_4 or a large independent set just below n^2 / 8 edges),
      Erdos #807 (the bipartition number of G(n, 1/2) against n - alpha) *)

From GTBase Require Import base finite_graph.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local x286 vocabulary ************************************************* *)

(** [x286_biclique_edges A B]: the edges of the complete bipartite graph between the vertex sets A and B of G, the
    pairs {a, b} with a in A and b in B.  With A and B disjoint and these pairs edges of G, it is the edge set of a
    complete bipartite subgraph of G (a biclique; Kratzke, Reznick and West, Trans. Amer. Math. Soc. (1988)
    637-653, printed p.637-638: the family of all K_(r,s)). *)
Definition x286_biclique_edges (G : sgraph) (A B : {set G}) : {set {set G}} :=
  [set [set a; b] | a in A, b in B].

(** [x286_biclique_partition G k]: the edges of G are partitioned by the edge sets of k complete bipartite subgraphs
    of G: k pairs (A_i, B_i) of disjoint vertex sets whose biclique edges are edges of G, pairwise edge disjoint, and
    covering E(G).  Vertex sets of distinct bicliques may overlap; only their edge sets are disjoint.  A pair with an
    empty side contributes no edge, so this holds for k exactly when it holds for some k' <= k with nonempty sides:
    it says tau(G) <= k, and tau(G) is the least such k (KRW88 p.637: "the minimum number of edge-disjoint subgraphs
    of G that belong to F and cover the edges of G"). *)
Definition x286_biclique_partition (G : sgraph) (k : nat) : bool :=
  [exists AB : {ffun 'I_k -> {set G} * {set G}},
    [&& [forall i, [disjoint (AB i).1 & (AB i).2] && (x286_biclique_edges (AB i).1 (AB i).2 \subset E(G))],
        [forall i, [forall j, (i != j) ==>
           [disjoint x286_biclique_edges (AB i).1 (AB i).2 & x286_biclique_edges (AB j).1 (AB j).2]]] &
        E(G) \subset \bigcup_i x286_biclique_edges (AB i).1 (AB i).2]].

(** ** X286 statements ******************************************************* *)

(** Corpus row: erdos:615
    Site: none
    Review: none
    English statement: (Erdos Problems #615; Erdos, Hajnal, Simonovits, Sos and Szemeredi)
      There is a constant c > 0 such that, for every sufficiently large n, every graph G with n vertices and at least
      (1/8 - c) n^2 edges contains a K_4 or an independent set of at least n / ln n vertices.
    Definitions: [has_subgraph G 'K_4] - G contains a copy of K_4 (GTBase common.v); [stable S] - no edge inside S
      (coq-graph-theory); [E(G)] - the edge set of G (GTBase common.v).
    Notes: the pinned statement is the erdosproblems.com text ("Does there exist some constant c > 0 such that if G
      is a graph with n vertices and >= (1/8 - c) n^2 edges then G must contain either a K_4 or an independent set on
      at least n / log n vertices?"); encoded as the affirmative answer.  It is Problem 4 of EHSSS93 (Combinatorica
      (1993) 31-56, printed p.54): "Is it true that for some c > 0, RT(n, K_4, n / log n) < (1/8 - c) n^2?", where
      RT(n, L, m) is the largest number of edges of an L-free graph on n vertices with alpha <= m (printed p.33,
      EHSSS93.txt l.112-116); Fox, Loh and Zhao (arXiv:1208.3276v3, main.tex l.134-136, Problem 1.4) restate it
      with alpha < m (l.95-97).  Both readings agree here: n / ln n is never an integer for n >= 2 (ln n is
      irrational).
      The constant: c = 1 / m.  (1/8 - 1/m) n^2 <= |E| is m n^2 <= 8 (m |E| + n^2); a claim for c holds for every
      smaller c, so some real c > 0 is some m; for m <= 8 the edge condition is empty, as for c >= 1/8.
      The logarithm is natural: EHSSS93 and the page give no base, Fox, Loh and Zhao take every logarithm to base e
      (l.302).  With the bound n / ln n and no free constant on that side the base matters, so it is stated, not
      assumed.  The bound is exact, with no rounding: for n >= 2, |S| >= n / ln n is e^n <= n^|S|, and (1 + 1/k)^k
      increases to e, so this is (k + 1)^(k n) <= k^(k n) n^|S| for every k >= 1.
      The order: RT is an asymptotic quantity and "sufficiently large n" is the only nontrivial reading.  Read for
      every n, the claim fails for every c at K_3 (3 >= (1/8 - c) 9 edges, no K_4, alpha = 1 < 3 / ln 3).  n0 makes it
      eventual, and n0 >= 2 can always be taken, so the excluded orders 0 and 1, where n / ln n is undefined, do not
      matter.
      Literature status: DISPROVED before the pin (pinned status solved, "DISPROVED ... in the negative").  Fox, Loh
      and Zhao, Theorem 1.10 (l.243-246): RT(n, K_4, m) >= (1/8 - o(1)) n^2 when
      m = n e^(-o((log n / log log n)^(1/2))), which includes m = n / ln n (ln ln n is o((ln n / ln ln n)^(1/2)));
      so for every c and all large n some K_4-free graph with at least (1/8 - c) n^2 edges has alpha < n / ln n.  Any
      fixed base, or a constant factor on n / ln n, changes m by a constant factor only, which the theorem still
      covers.  [Er91] (the page's other citation) was not obtained, only its bibliography entry; EHSSS93 and FLZ
      print the question. *)
Definition erdos_615_k4_or_large_independent_set_statement : Prop :=
  exists m n0 : nat, forall G : sgraph, n0 <= #|G| ->
    m * #|G| ^ 2 <= 8 * (m * #|E(G)| + #|G| ^ 2) ->
    has_subgraph G 'K_4 \/ exists2 S : {set G}, stable S &
      forall k : nat, 0 < k -> k.+1 ^ (k * #|G|) <= k ^ (k * #|G|) * #|G| ^ #|S|.

(** Corpus row: erdos:807
    Site: none
    Review: none
    English statement: (Erdos Problems #807; Erdos, reported by Kratzke, Reznick and West)
      The bipartition number tau(G) of a graph G is the smallest number of pairwise edge disjoint complete bipartite
      graphs whose union is G, and alpha(G) is its independence number.  If G is a random graph on n vertices with
      edge probability 1/2, then tau(G) = n - alpha(G) almost surely.
    Definitions: [x286_biclique_edges A B] - the pairs {a, b} with a in A and b in B, and [x286_biclique_partition G k]
      - E(G) is partitioned by the edge sets of k complete bipartite subgraphs of G (this file); [fg_labelled_sgraph
      E] - the graph on 'I_n whose edges are the 2-sets in E, [fg_gnp_weight 1 2 n] - the G(n, 1/2) weight (every
      labelled graph on n vertices has weight 1), [fg_whp] - with probability tending to 1 (GTBase finite_graph.v);
      α([set: G]) - the independence number of G, [E(G)] - the edge set (coq-graph-theory, GTBase common.v).
    Notes: the pinned statement is the erdosproblems.com text ("Is it true that, if G is a random graph on n vertices
      with edge probability 1/2, then tau(G) = n - alpha(G) almost surely?"); encoded as the affirmative answer.  KRW88
      (printed p.638) states it: "Erdos conjectured that tau(G) = n - alpha(G) for almost all graphs".  tau is KRW88's
      parameter for the family of all complete bipartite graphs (p.637-638): the bicliques are subgraphs of G, not
      necessarily induced, their vertex sets may overlap and their edge sets partition E(G) (also Alon, Bohman and
      Huang, arXiv:1409.6165v1, main.tex l.85-89).  The event says that tau(G) is exactly n - alpha(G): a partition
      into n - alpha(G) bicliques exists and none into fewer.  The first part always holds (stars at the vertices
      outside a largest independent set, KRW88 p.638; l.95-98 of 1409.6165v1), so the event is tau(G) >= n -
      alpha(G).  The subtraction n - alpha(G) is never truncated, since alpha(G) <= n.  "Almost surely" is with
      probability tending to 1 as n tends to infinity (Alon, arXiv:1402.6466v1, main.tex l.92-98), over the uniform
      measure on the labelled graphs on 'I_n, which is G(n, 1/2); fg_whp asks the event weight to be at least
      (1 - a / b) of the total weight eventually, for every 0 < a <= b.  On no vertex, or on the edgeless graph,
      tau = 0 = n - alpha.
      Literature status: DISPROVED before the pin (pinned status solved, "DISPROVED ... in the negative").  Alon
      (1402.6466v1, l.114-124) showed tau(G) <= n - alpha(G) - 1 whp for most n, and for the exceptional n (alpha
      concentrated on two values) tau(G) <= n - alpha(G) - 2 with probability bounded away from 0; Alon, Bohman and
      Huang (1409.6165v1, Theorem 1.1, l.139-146) prove tau(G) <= n - (1 + c) alpha(G) whp for an absolute c > 0, for
      all n.  As alpha(G) >= 1 once n >= 1, the event then fails whp, so the encoded statement is false. *)
Definition erdos_807_bipartition_number_random_graph_statement : Prop :=
  @fg_whp (fun n : nat => {set {set 'I_n}}) (fun n => @fg_gnp_weight 1 2 n)
    (fun n E => x286_biclique_partition (fg_labelled_sgraph E) (n - α([set: fg_labelled_sgraph E]))
       && [forall k : 'I_(n - α([set: fg_labelled_sgraph E])),
             ~~ x286_biclique_partition (fg_labelled_sgraph E) k]).
