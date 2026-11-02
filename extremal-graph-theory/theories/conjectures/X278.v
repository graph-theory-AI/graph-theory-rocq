(** * Extremal.conjectures.X278 -- v2 rows: making an H-free graph k-colourable (cliques, odd wheels), Meshulam *)

From GTBase Require Import base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** X278 statements *****************************************************)

(** Corpus row: arxiv:2102.10220#00
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/2102.10220__00/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/2102.10220__00.json
    English statement: (Fox, Himwich and Mani, Making an H-free graph k-colorable, conjecture after Theorem 1.1)
      For each integer r >= 3 there is c_r such that for all positive integers n, k with n sufficiently large in
      terms of k, h(n, k, K_r) = Theta_r(n^2 / k^((r-1)/(r-2))), i.e., the upper bound
      h(n, k, K_r) <= c_r n^2 / k^((r-1)/(r-2)) is tight up to the constant factor c_r.
    Definitions: [has_subgraph G H] - G contains H as a subgraph: an injective map from H to G preserves
      adjacency (GTBase common.v); ['K_r] - the complete graph on r vertices (coq-graph-theory); [E(G)] - the edge
      set of G (GTBase common.v); [del_edge_set G F] - G - F, the edges of F removed and the vertices kept (GTBase
      common.v); [χ(A)] - the chromatic number of the subgraph induced on A (coq-graph-theory coloring.v).  As Fox,
      Himwich and Mani define them (arXiv:2102.10220v2, main.tex l.155, l.159): graphs are finite, undirected and
      simple; G is H-free if it does not contain H as a SUBGRAPH; h(G, k) is the least number of edges whose
      deletion leaves a k-colourable graph, and h(n, k, H) is the largest h(G, k) over the H-free graphs G on n
      vertices.
    Notes: encoded as stated, Theta_r as two clauses: the constants A (upper) and 1 / a (lower) are chosen before
      k, and the threshold n0 after k, so n0 may depend on r and k and the constants on r only.  h(n, k, K_r) <= U
      iff every K_r-free G on n vertices has a set F of at most U edges with chi(G - F) <= k, and h(n, k, K_r) >= L
      iff some K_r-free G on n vertices has |F| >= L for every such F.  The exponent (r - 1) / (r - 2) is cleared by
      raising both sides to the power r - 2; a real constant c gives the natural constants A = ceil(c) and
      a = ceil(1 / c).  Taking F inside E(G) changes neither h nor the clauses (other members only add to |F|).  The
      upper clause is Theorem 1.1 (l.171-173, for all positive n and k); the lower clause is the conjecture (l.176),
      which the paper proves for r = 3 (Theorem 1.4 at r = 1, l.193-195: odd girth larger than 3 is triangle-free,
      and its bound n^2 / k^2 is this one).  The threshold is needed: a graph on n <= k vertices is k-colourable, so
      h(n, k, K_r) = 0 there.  OPEN at the pin for r >= 4.  The exponents r - 2 and r - 1 are exact natural
      subtractions, guarded by 3 <= r. *)
Definition kr_free_k_colourable_deletion_sharp_statement : Prop :=
  forall r : nat, 3 <= r -> exists a A : nat, 0 < a /\ 0 < A /\
    forall k : nat, 0 < k -> exists n0 : nat, forall n : nat, n0 <= n ->
      (forall G : sgraph, #|G| = n -> ~ has_subgraph G ('K_r) ->
         exists F : {set {set G}},
           [/\ F \subset E(G), χ([set: del_edge_set G F]) <= k &
               #|F| ^ (r - 2) * k ^ (r - 1) <= (A * n ^ 2) ^ (r - 2)]) /\
      (exists G : sgraph,
         [/\ #|G| = n, ~ has_subgraph G ('K_r) &
             forall F : {set {set G}}, F \subset E(G) -> χ([set: del_edge_set G F]) <= k ->
               n ^ (2 * (r - 2)) <= (a * #|F|) ^ (r - 2) * k ^ (r - 1)]).

(** Corpus row: arxiv:2102.10220#01
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/2102.10220__01/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/2102.10220__01.json
    English statement: (Fox, Himwich and Mani, Making an H-free graph k-colorable, conjecture before Theorem 1.5)
      For each positive integer r, the bound h(n, k, W_(2r+1)) <= c_r n^2 / k^(2 - 1/(r+1)) is tight up to the
      constant factor c_r depending on r.
    Definitions: h(n, k, H), H-free (SUBGRAPH-free), [has_subgraph], [E(G)], [del_edge_set] and [χ] as for
      arxiv:2102.10220#00; [cycle_graph m] - the cycle on 'I_m, i adjacent to i + 1 mod m (GTBase base.v);
      [add_node G N] - G with one new vertex [None] adjacent to the vertices of N (coq-graph-theory).  The wheel
      W_l of the source (l.198) is the graph on l + 1 vertices formed by an l-cycle and a vertex adjacent to all of
      its vertices: here [add_node (cycle_graph (2 * r + 1)) [set: cycle_graph (2 * r + 1)]], whose rim has
      2r + 1 >= 3 vertices.
    Notes: encoded like arxiv:2102.10220#00, with the exponent 2 - 1/(r+1) = (2r + 1) / (r + 1) cleared by raising
      both sides to the power r + 1, and over the range of Theorem 1.5 (l.201-203: r >= 1, n >= k >= 2): k >= 2,
      and n >= k follows from the threshold n0, chosen after k.  The source states the bound, not the range of its
      tightness; "tight up to the constant factor" is read for n sufficiently large in terms of k, as in the
      odd-cycle result the record cites (Theorem 1.4, l.192-195), and the threshold is needed: on n = k vertices
      h = 0.  The constants depend on r only (l.199: "the constant factor which depends on the length of the
      wheel").  The upper clause is Theorem 1.5; the lower clause is the conjecture (l.199), OPEN at the pin.  The
      wheel is written out rather than named by a local helper; grounding_X278.v checks its order 2r + 2 and its
      hub. *)
Definition odd_wheel_free_k_colourable_deletion_sharp_statement : Prop :=
  forall r : nat, 1 <= r -> exists a A : nat, 0 < a /\ 0 < A /\
    forall k : nat, 2 <= k -> exists n0 : nat, forall n : nat, n0 <= n ->
      (forall G : sgraph, #|G| = n ->
         ~ has_subgraph G (add_node (cycle_graph (2 * r + 1)) [set: cycle_graph (2 * r + 1)]) ->
         exists F : {set {set G}},
           [/\ F \subset E(G), χ([set: del_edge_set G F]) <= k &
               #|F| ^ (r + 1) * k ^ (2 * r + 1) <= (A * n ^ 2) ^ (r + 1)]) /\
      (exists G : sgraph,
         [/\ #|G| = n, ~ has_subgraph G (add_node (cycle_graph (2 * r + 1)) [set: cycle_graph (2 * r + 1)]) &
             forall F : {set {set G}}, F \subset E(G) -> χ([set: del_edge_set G F]) <= k ->
               n ^ (2 * (r + 1)) <= (a * #|F|) ^ (r + 1) * k ^ (2 * r + 1)]).

(** Corpus row: studies:std_meshulam_s_conjecture_on_ruzsa_szemer_di_graphs
    Site: none
    Review: none
    English statement: (Meshulam; studies slice of the corpus, record arXiv:2001.00387)
      There are no (r,t)-Ruzsa-Szemeredi graphs with both rt = Theta(C(n,2)) and r >= n^Omega(1).
    Definitions: [E(G)] - the edge set of G (GTBase common.v); [matching M] - M is a set of edges of G, any two
      of them disjoint (coq-graph-theory connectivity.v); [\bigcup_(i < t) P i] - the union of the t parts.  As
      Alon and Shraibman define it (arXiv:2001.00387v1, main.tex l.128): a graph is an (r,t)-RS graph if its set of
      edges can be partitioned into t pairwise disjoint induced matchings, each of size r.  A matching is induced
      when no edge of G joins two of its edges (the last clause of the partition); matchings of different parts may
      share vertices.  n is the number of vertices of G.
    Notes: encoded as stated, the asymptotic "there are no" over constants: for every c = 1 / a and exponent
      1 / b, only finitely many orders carry an (r,t)-RS graph with r t >= n^2 / a and r >= n^(1/b), so some n0
      bounds them.  The upper half of Theta adds nothing: the parts partition E(G), so r t = |E(G)| <= C(n,2); and
      r t >= c C(n,2) for some c > 0 iff n^2 <= a r t for some a, since n^2 / 4 <= C(n,2) <= n^2 for n >= 2.  A
      reciprocal integer exponent loses nothing: r >= n^eps implies r >= n^(1/b) once 1 / b <= eps.  Meshulam's
      conjecture is quoted at l.140-141, after the definition (l.128) and the earlier construction of Birk, Linial
      and Meshulam (l.135-139).  FALSE at the pin (informal, not kernel-checked): the paper reports (l.124-127)
      that Alon, Moitra and Sudakov constructed (r,t)-RS graphs on n vertices with r = n^(1-o(1)) and
      r t = (1-o(1)) C(n,2), which "disproved Meshulam's conjecture in a strong form" (l.142-143); with a = 3 and
      b = 2 their graphs violate the body for infinitely many n, which already refutes it.  The pinned status open
      is for a separate literature item; the body keeps the historical statement. *)
Definition meshulam_ruzsa_szemeredi_statement : Prop :=
  forall a b : nat, 0 < a -> 0 < b -> exists n0 : nat,
    forall (G : sgraph) (r t : nat), n0 <= #|G| ->
      (exists P : 'I_t -> {set {set G}},
         [/\ \bigcup_(i < t) P i = E(G),
             forall i j : 'I_t, i != j -> [disjoint P i & P j],
             forall i : 'I_t, #|P i| = r,
             forall i : 'I_t, matching (P i) &
             forall (i : 'I_t) (e f : {set G}), e \in P i -> f \in P i -> e != f ->
               forall x y : G, x \in e -> y \in f -> ~~ (x -- y)]) ->
      ~ (#|G| ^ 2 <= a * (r * t) /\ #|G| <= r ^ b).
