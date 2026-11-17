(** * GTMisc.conjectures.X313 -- v2 row: the Szeged-Wiener difference over the non-complete blocks (Nadjafi-Arani,
      Khodashenas and Ashrafi) *)

From GTBase Require Export base.
From GTMisc.conjectures Require Import X156 X165.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** X313 helper ************************************************************ *)

(** [x313_noncomplete_blocks G]: the blocks of G that do not induce a complete graph. Blocks are X156's x156_blockb:
    the maximal non-empty vertex sets B such that G[B] is connected and stays connected after deleting any one vertex
    of B, the record's "maximal subgraph without a cut-vertex" (arXiv:1602.05184v1 l.134-136); completeness is
    coq-graph-theory's cliqueb. *)
Definition x313_noncomplete_blocks (G : sgraph) : {set {set G}} :=
  [set B : {set G} | x156_blockb B && ~~ cliqueb B].

(** ** X313 statement ********************************************************* *)

(** Corpus row: studies:std_nadjafi_arani_khodashenas_ashrafi_conjecture_sze
    Site: none
    Review: none
    English statement: (Nadjafi-Arani, Khodashenas and Ashrafi's conjecture, 2012; studies slice of the corpus, record
      arXiv:1602.05184, Conjecture 1) Let G be a connected graph and let B_1, ..., B_k be all its non-complete blocks
      of respective orders n_1, ..., n_k. Then eta(G) >= sum_{i=1}^k (2 n_i - 6), where eta(G) = Sz(G) - W(G) is the
      difference between the Szeged index and the Wiener index of G.
    Definitions: [connected [set: G]] - G is connected (coq-graph-theory); [x165_wiener_index G] - W(G), the sum of
      the distances d(a, b) over the unordered pairs {a, b} of vertices (graph-theory-misc X165.v: half the sum over
      ordered pairs of graph_dist, GTBase graph_metric.v, the shortest-path distance in a connected graph);
      [x165_szeged_index G] - Sz(G), the sum over the edges ab of n_ab(a) n_ab(b), where n_ab(a) is the number of
      vertices strictly closer to a than to b (X165.v: half the sum over ordered adjacent pairs of x165_closer_count);
      [x313_noncomplete_blocks G] - the set of the non-complete blocks of G (this file), so that k is its cardinality
      and n_i the cardinality of its i-th member.
    Notes: encoded without subtraction. Over the integers, eta(G) >= sum_i (2 n_i - 6) is
      W(G) + sum_i 2 n_i <= Sz(G) + 6 k, and every term of the latter is a natural number: no truncated subtraction
      (X165's x165_eta truncates Sz - W) and no appeal to Sz >= W. A block is "a maximal subgraph without a
      cut-vertex", "either a 2-connected subgraph, a single edge or an isolated vertex" (l.134-136); a single edge and
      an isolated vertex are complete, so the non-complete blocks are the 2-connected blocks that are not cliques
      (l.73's "maximal 2-connected subgraph" gives the same ones). The connectivity hypothesis is needed: graph_dist
      is #|G| between two components, and without the hypothesis the statement fails on two isolated vertices
      ([g313_swb_not_trivially_true] in grounding_X313.v). Status: solved in its own record (Theorem 2, l.87-89: a
      2-connected non-complete graph on n vertices has eta(G) >= 2n - 6; "As a consequence of Theorem 2 we obtain
      that Conjecture 1 is true", l.91; Corollary 3, l.92-95; v1 of 16 February 2016, the only version before the
      pin); the pinned status is open; a literature item after integration records it (statement read, proof not
      verified). Line numbers are those of the deposited text 1602.05184v1.txt. *)
Definition szeged_wiener_difference_noncomplete_blocks_statement : Prop :=
  forall G : sgraph,
    connected [set: G] ->
    x165_wiener_index G + \sum_(B in x313_noncomplete_blocks G) (2 * #|B|)
      <= x165_szeged_index G + 6 * #|x313_noncomplete_blocks G|.
