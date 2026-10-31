(** * Hypergraph.conjectures.X267 -- v2 rows: the (6,3) problem, alpha-stable regular edge-colourable graphs *)

From GTBase Require Import base common edge_colourings.
From Hypergraph.foundations Require Import hypergraph.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** X267 statements *****************************************************)

(** Corpus row: erdos:716
    Site: none
    Review: none
    English statement: (Erdos Problems #716, a conjecture of Brown, Erdos and Sos [BES73])
      Let F be the family of all 3-uniform hypergraphs with 6 vertices and 3 3-edges.  Is it true that
      ex_3(n, F) = o(n^2)?
    Definitions: [hg_uniform E 3] - every hyperedge of E has exactly 3 vertices (Hypergraph.foundations.hypergraph);
      a 3-uniform hypergraph on n vertices is a set E of 3-subsets of 'I_n.
    Notes: encoded as its affirmative answer; pinned status solved (page label PROVED).  The page attributes the
      answer to Ruzsa and Szemeredi, Triple systems with no six points carrying three triangles, Combinatorics
      (Proc. Fifth Hungarian Colloq., Keszthely, 1976), Vol. II (1978), pp.939-945 (the page's RuSz78 record);
      that paper was not obtained, so this rests on the page, its LaTeX view and the bibliography records.
      ex_3(n, F) = o(n^2): for every eps > 0 some N such that every 3-uniform hypergraph on n >= N vertices
      containing no member of F has at most eps n^2 hyperedges.  eps = 1/p covers every real eps > 0, as a
      smaller eps asks for more.  A member of F inside E is three distinct hyperedges inside six vertices; once
      n >= 6 that is three distinct hyperedges spanning at most 6 vertices (a smaller span is padded with other
      vertices), so F-free is "every three distinct hyperedges span at least 7 vertices", and N >= 6 can always
      be taken.  Erdos Problems #1178 and #1157 are the generalisations the page names (other rows). *)
Definition six_three_hypergraph_statement : Prop :=
  forall p : nat, 1 <= p -> exists N : nat, forall (n : nat) (E : {set {set 'I_n}}),
    N <= n -> hg_uniform E 3 ->
    (forall e1 e2 e3 : {set 'I_n}, e1 \in E -> e2 \in E -> e3 \in E ->
       e1 != e2 -> e1 != e3 -> e2 != e3 -> 6 < #|e1 :|: e2 :|: e3|) ->
    p * #|E| <= n ^ 2.

(** Corpus row: arxiv:2505.05339#00
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/2505.05339__00/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/2505.05339__00.json
    English statement: (Clow, Haxell and Mohar, A Counterexample to a Conjecture of Lovasz, arXiv:2505.05339,
      Question 4.1)
      Do there exist infinitely many 3-edge colourable cubic graphs G such that for all edges (u, v), (x, y) in
      E(G), alpha(G) = alpha(G - {u, v, x, y})?
    Definitions: [regular G 3] - every vertex has exactly 3 neighbours (GTBase.base); [proper_edge_colouring col]
      - edges with a common end get different colours, read on the edges [set x; y] (GTBase.edge_colourings);
      [α(A)] - the independence number of the subgraph induced by A (upstream coq-graph-theory).
    Notes: encoded as its affirmative answer; pinned status solved.  Abiad, Garbe, Povill and Spiegel,
      arXiv:2506.21286v2 (PDF pp.2-7): Theorem 13 gives the equality for the generalized Petersen graphs
      GP(5k + 11, 2), k >= 0, which are cubic and 3-edge-colourable (Remark 11); with Lemma 7 this is their
      Theorem 2, and l.263-271 name Question 4.1 as answered.  "Infinitely many" is "of unbounded order", as
      there are finitely many graphs of each order: for every N some G with N <= |G|.  The edges carry no
      distinctness condition, so (x, y) = (u, v) is allowed; that changes nothing: alpha(G - S) is antitone in S
      and at most alpha(G), and a cubic graph with a vertex has at least 6 edges, so the ends of a repeated edge
      lie inside the ends of two distinct edges.  v2 (main.tex l.772-777, PDF p.13) prints the full equality;
      the pinned class note calling the statement truncated is stale. *)
Definition cubic_alpha_stable_statement : Prop :=
  forall N : nat, exists G : sgraph,
    [/\ N <= #|G|, regular G 3, (exists col : {set G} -> 'I_3, proper_edge_colouring col) &
      forall u v x y : G, u -- v -> x -- y -> α([set: G]) = α([set: G] :\: [set u; v; x; y])].

(** Corpus row: arxiv:2505.05339#01
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/2505.05339__01/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/2505.05339__01.json
    English statement: (Clow, Haxell and Mohar, A Counterexample to a Conjecture of Lovasz, arXiv:2505.05339,
      Question 4.2)
      Does there exist a d-regular d-edge colourable graph G where d >= 4 such that for all edges (u_1, v_1), ...,
      (u_(d-1), v_(d-1)) in E(G), alpha(G) = alpha(G - {u_1, ..., u_(d-1), v_1, ..., v_(d-1)})?
    Definitions: as for #00; the d - 1 edges are (u i, v i) for i in 'I_d.-1, and their ends are the images of u
      and v.
    Notes: encoded as its affirmative answer; pinned status solved.  Abiad, Garbe, Povill and Spiegel,
      arXiv:2506.21286v2, Theorem 3 (PDF p.3) and Section 4: quartic graphs whose line hypergraphs are
      counterexamples to Lovasz's conjecture for r = 4, the smallest on 70 vertices, verified computationally;
      l.263-271 name Question 4.2 as answered.  Such a line hypergraph is 4-partite, so G is 4-regular and
      4-edge-colourable (Remark 5), and its matchings avoiding three vertices are the independent sets of G
      avoiding the ends of three edges (Remark 6), which is the equality here (Lemma 7 and its converse).
      Repeated edges change nothing, as in #00: a d-regular graph with a vertex has at least d(d + 1)/2 >= d - 1
      edges.  0 < |G| is load-bearing: the empty graph is vacuously d-regular and d-edge-colourable and has no
      edge, so without it the row would hold trivially; the question's graph has a vertex.  d.-1 = d - 1 as
      4 <= d.  v2 (main.tex l.779-784, PDF p.13) prints the full equality; the pinned class note calling the
      statement truncated is stale. *)
Definition regular_alpha_stable_statement : Prop :=
  exists (d : nat) (G : sgraph),
    [/\ 4 <= d, 0 < #|G|, regular G d, (exists col : {set G} -> 'I_d, proper_edge_colouring col) &
      forall u v : 'I_d.-1 -> G, (forall i, u i -- v i) ->
        α([set: G]) = α([set: G] :\: ([set u i | i in 'I_d.-1] :|: [set v i | i in 'I_d.-1]))].
