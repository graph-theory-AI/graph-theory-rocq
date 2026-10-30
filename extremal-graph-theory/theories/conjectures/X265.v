(** * Extremal.conjectures.X265 -- v2 rows: balanced dense subgraphs, the deletion exponent for C_5-free graphs *)

From GTBase Require Import base common.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** X265 statements *****************************************************)

(** Corpus row: erdos:1077
    Site: none
    Review: none
    English statement: (Erdos Problems #1077, a question of Erdos and Simonovits [ErSi70])
      We call a graph D-balanced (or D-almost-regular) if the maximum degree is at most D times the minimum degree.
      Let eps, alpha > 0 and D and n be sufficiently large.  If G is a graph on n vertices with at least
      n^(1 + alpha) edges, then must G contain a D-balanced subgraph on m > n^(1 - alpha) vertices with at least
      eps m^(1 + alpha) edges?
    Definitions: [edge_count G] - the number of edges of G (GTBase.common); [min_degree H d] - d is the minimum
      degree of H, which needs a vertex (GTBase.base); [Delta H] - the maximum degree (GTBase.base);
      [has_subgraph G H] - H is a subgraph of G up to isomorphism, not necessarily induced (GTBase.common).
    Notes: encoded as stated; the row is FALSE at the pin, pinned status solved (answered negatively; page label
      DISPROVED).  The quantifiers follow the original, Erdos and Simonovits, Some extremal problems in graph theory
      (1970), printed pp.388-389: "for every eps and alpha if n > n0(eps, alpha) and d > d0(eps, alpha)", so eps is
      universal, not "some eps".  alpha = a/b and eps = r/p range over the positive rationals: a larger eps asks for
      more edges, so every real eps is covered; rational alpha restricts the real range (the row is not monotone in
      alpha), which is kept because the refuted instance below has alpha = 1/3.  Only alpha < 1 is stated: for
      alpha >= 1 no graph on n >= 1 vertices has n^(1 + alpha) >= n^2 > C(n, 2) edges, so those instances hold
      vacuously.  "D sufficiently large" is "some D", as a D-balanced graph is D'-balanced for every D' >= D (the
      original's d0 does not bound n0; by the same monotonicity that is equivalent).  The original's "d-regular"
      (d times the minimum degree bounds the maximum, d > 4, printed pp.379-380) is the page's D-balanced.  Cleared
      of roots, m > n^(1 - alpha) is n^(b - a) < m^b and e(H) >= eps m^(1 + alpha) is r^b m^(b + a) <= (p e(H))^b.
      The page says "at least" twice where the original has the strict e(G) > n^(1 + alpha) and
      e(H) > eps m^(1 + alpha); the page is encoded, and the refutation covers both.  Refutation (the page's
      discussion; checked, no kernel proof): for 0 < alpha < 1/2, K_(s, n - s) with s about 3 n^alpha has more
      than n^(1 + alpha) edges; a D-balanced subgraph H with an edge has minimum degree d >= 1, so its large-side
      vertices number at most e(H) / d <= D s, and m <= (D + 1) s < n^(1 - alpha) for large n; an edgeless H has
      no edge to count.  So the row fails at alpha = 1/3 for every eps and D.  Jiang and Longbrake,
      arXiv:2507.03261v2, Theorem 1.3: a 6-almost-regular subgraph with e(H) >= ((2^alpha - 1) / 48) m^(1 + alpha)
      and average degree at least d(G) / (12 log (2n / d(G))); the page's suggested corrected question
      (m >> n^alpha, some eps) is another row's matter.  The nat subtraction b - a is guarded by a < b. *)
Definition balanced_dense_subgraph_statement : Prop :=
  forall a b r p : nat, 0 < a < b -> 1 <= r -> 1 <= p -> exists D N : nat,
    forall G : sgraph, N <= #|G| -> #|G| ^ (b + a) <= edge_count G ^ b ->
      exists H : sgraph, [/\ has_subgraph G H, #|G| ^ (b - a) < #|H| ^ b,
        (exists d : nat, min_degree H d /\ Delta H <= D * d) &
        r ^ b * #|H| ^ (b + a) <= (p * edge_count H) ^ b].

(** Corpus row: arxiv:2004.10180#00
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/2004.10180__00/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/2004.10180__00.json
    English statement: (Conlon, Fox, Sudakov and Zhao, The regularity method for graphs with few 4-cycles,
      arXiv:2004.10180, after Corollary 1.4)
      Is the exponent 3/2 in the conclusion of Corollary 1.4 best possible?  (Corollary 1.4 states: every n-vertex
      C_5-free graph can be made triangle-free by deleting o(n^(3/2)) edges.)
    Definitions: [has_subgraph G (cycle_graph 5)] - G contains the 5-cycle as a subgraph, not necessarily induced
      (GTBase.common, GTBase.base); [del_edge_set G F] - G with the pairs of F deleted (GTBase.common);
      [triangle_free] (GTBase.base); [E(G)] - the edge set of G (upstream coq-graph-theory).
    Notes: encoded as its affirmative answer; the row is open at the pin.  v3 (2021-09-25, the last version before
      the pin) says after Corollary 1.4 "We do not know if the exponent 3/2 in Corollary 1.4 is best possible"
      (PDF p.3), and the remark of Section 7 (PDF p.17) adds that a matching lower bound needs a C_5-free union of
      n^(3/2 - o(1)) edge-disjoint triangles; Propositions 1.5 and 1.7 concern Corollary 1.3's hypothesis and the
      5-partite removal lemma and settle neither direction.  "Best possible" is read as: no smaller exponent
      works, i.e. for every delta > 0 the bound O(n^(3/2 - delta)) fails (the same as o(n^(3/2 - delta)) failing for
      every delta).  delta = 1/q: every real delta > 0 exceeds some 1/q, and failing at 1/q implies failing at
      delta.  So: for every q >= 1, C and N there is a C_5-free G on n >= N vertices such that every set F of
      edges of G whose deletion leaves G triangle-free has C n^(3q - 2) < |F|^(2q), that is
      |F| > C^(1/(2q)) n^(3/2 - 1/q), with C over all naturals standing for every real constant.  C_5-free means
      no C_5 subgraph, not merely no induced C_5.  The nat subtraction 3q - 2 is guarded by 1 <= q. *)
Definition c5_free_triangle_deletion_exponent_statement : Prop :=
  forall q C N : nat, 1 <= q -> exists G : sgraph,
    [/\ N <= #|G|, ~ has_subgraph G (cycle_graph 5) &
      forall F : {set {set G}}, F \subset E(G) -> triangle_free (del_edge_set G F) ->
        C * #|G| ^ (3 * q - 2) < #|F| ^ (2 * q)].
