(** * Extremal.conjectures.X247 -- wave X247: copies of C_4 above ex(n;C_4), the degree sum of a triangle above n^2/4 edges, the diameter of clique-free graphs of given minimum degree (2026-10-28)

    A three-row wave under the prospective contract of meta/faithfulness_policy.json.  Rows: erdos:60 (a graph on n
    vertices with more than ex(n;C_4) edges contains >> n^{1/2} copies of C_4), erdos:1033 (a graph on n vertices
    with more than n^2/4 edges has a triangle whose degrees sum to at least (2(sqrt 3 - 1) - o(1)) n) and erdos:612
    (Erdos, Pach, Pollack and Tuza: the diameter of a connected K_{2r}-free, resp. K_{2r+1}-free, graph of minimum
    degree d).  No local helper and no copied vocabulary: GTBase supplies [edge_count], [has_subgraph],
    [cycle_graph], [del_edge_set], 'K_n, [min_degree] and [graph_dist] (GTBase.graph_metric); [connected], N(x) and
    E(G) are upstream.  All three rows have pinned status "open"; their literature lines are dated against the corpus
    pin (graph-conjectures b72c5857, 2026-09-23).  The sources are the Mac's deposit
    coordination/sources/x247-source-mac-20261028.  The grounding certificates are in grounding_X247.v. *)

From GTBase Require Import base common graph_metric.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** X247 statements ******************************************************* *)

(** Corpus row: erdos:60
    Site: none
    Review: none
    English statement: (Erdos Problems #60, Erdos and Simonovits)
      There is a constant c > 0 such that every graph on n vertices with more than ex(n;C_4) edges contains at least
      c n^{1/2} copies of C_4.
    Definitions: [has_subgraph G H] - H is a (not necessarily induced) subgraph of G (GTBase.common); [cycle_graph 4]
      - the cycle C_4 (GTBase); [edge_count G] - the number of edges #|E(G)| (GTBase.common); [del_edge_set G
      (E(G) :\: F)] - the spanning subgraph of G with edge set F (GTBase).
    Notes: the pinned statement is the erdosproblems.com question ("Does every graph on n vertices with
      > ex(n;C_4) edges contain >> n^{1/2} many copies of C_4?"), encoded in its affirmative form.  "More than
      ex(n;C_4) edges" is written directly: more edges than every C_4-free graph on the same number of vertices (the
      maximum is attained), so no Turan-number predicate is needed.  A copy of C_4 is an ordinary (not necessarily
      induced) subgraph, as in He, Ma and Yang, arXiv:1912.00986v1, p.2 (h_F(n,t) = min #F(G) over |E(G)| =
      ex(n,F) + t, #F(G) the number of distinct copies of F); a copy is determined by its four edges, so the copies
      are counted as 4-edge sets F whose spanning subgraph contains C_4.  ">> n^{1/2}" is an absolute constant c
      ("h(n) >= c sqrt n for some constant c > 0", ibid. p.3): n <= (c |Fs|)^2 for every n, the constant absorbing
      small n; more edges than ex(n;C_4) + 1 only add copies, so "> ex" and "= ex + 1" agree.
      Literature status: open at the pin (pinned status open); He, Ma and Yang prove it for n = q^2 + q + 1 with
      q = 2^k, k >= 40 (Corollary 1.6, h(q^2 + q + 1) = q - 1).  [Er90] and [Er93, p.335] were not obtained. *)
Definition c4_copies_above_ex_statement : Prop :=
  exists c : nat, 1 <= c /\
    forall G : sgraph,
      (forall H : sgraph, #|H| = #|G| -> ~ has_subgraph H (cycle_graph 4) -> edge_count H < edge_count G) ->
      exists Fs : {set {set {set G}}},
        (forall F : {set {set G}}, F \in Fs ->
           [/\ F \subset E(G), #|F| = 4 & has_subgraph (del_edge_set G (E(G) :\: F)) (cycle_graph 4)]) /\
        #|G| <= (c * #|Fs|) ^ 2.

(** Corpus row: erdos:1033
    Site: none
    Review: none
    English statement: (Erdos Problems #1033, Bollobas and Erdos)
      Let h(n) be the largest number such that every graph on n vertices with more than n^2/4 edges contains a
      triangle whose vertices have degrees summing to at least h(n).  Then h(n) >= (2(sqrt 3 - 1) - o(1)) n.
    Definitions: [edge_count G] - #|E(G)| (GTBase.common); N(x) - the neighbourhood of x in G, so #|N(x)| is the
      degree of x in the host graph (upstream).
    Notes: the pinned statement is the erdosproblems.com text ("Let h(n) be such that every graph on n vertices with
      > n^2/4 many edges contains a triangle whose vertices have degrees summing to at least h(n).  Estimate h(n).  In
      particular, is it true that h(n) >= (2(sqrt 3 - 1) - o(1)) n?").  "Estimate h(n)" is not a proposition; the
      named sub-question is encoded in its affirmative form.  The degrees are those of the host graph, as in
      Bollobas and Nikiforov, arXiv:math/0410218v1, p.2 (the maximum degree sum of an r-clique of G).  o(1) is 1/q
      for every q >= 1, eventually in n: s >= (2(sqrt 3 - 1) - 1/q) n is q s + n + 2 q n >= 2 sqrt 3 q n, both sides
      nonnegative, squared (no real number, no subtraction).
      Literature status: open at the pin (pinned status open).  The live page records 2(sqrt 3 - 1) n + O(1) >= h(n)
      >= 21n/16: the upper bound is a construction (Erdos and Laskar [ErLa85], made explicit by Fan [Fa88]), so the
      question asks whether it is tight; the lower bound is Fan's.  [Er82e, p.71] prints the older form
      "v(x1) + v(x2) + v(x3) >= 3n/2" and says Edwards proved it; 3/2 exceeds 2(sqrt 3 - 1) ~ 1.464, so that
      statement conflicts with the upper bound above and is recorded here as a source discrepancy, not used.
      [Er93, p.344] was not obtained. *)
Definition triangle_degree_sum_above_quarter_statement : Prop :=
  forall q : nat, 1 <= q -> exists n0 : nat,
    forall G : sgraph, n0 <= #|G| -> #|G| ^ 2 < 4 * edge_count G ->
      exists x y z : G, [/\ x -- y, y -- z, x -- z &
        12 * q ^ 2 * #|G| ^ 2 <= (q * (#|N(x)| + #|N(y)| + #|N(z)|) + #|G| + 2 * q * #|G|) ^ 2].

(** Corpus row: erdos:612
    Site: none
    Review: none
    English statement: (Erdos Problems #612; Erdos, Pach, Pollack and Tuza, JCTB 47 (1989), Conjecture p.78-79)
      Let r, d >= 2 be fixed and let G be a connected graph with n vertices and minimum degree d.  If G contains no
      K_{2r} and (r-1)(3r+2) divides d, then diam G <= 2(r-1)(3r+2)/((2r^2-1) d) n + O(1); if G contains no
      K_{2r+1} and 3r-1 divides d, then diam G <= (3r-1)/(r d) n + O(1).
    Definitions: [min_degree G d] - the minimum degree of G is exactly d (GTBase.base); [graph_dist x y] - the
      distance of x and y, the least k with y in the k-ball of x (GTBase.graph_metric); [has_subgraph G 'K_m] - G
      contains K_m (GTBase.common); [connected [set: G]] - G is connected (upstream).
    Notes: the pinned statement is the erdosproblems.com text ("Show if that G contains no K_{2r} and (r-1)(3r+2) | d
      then D <= 2(r-1)(3r+2)/(2r^2-1) n/d + O(1), and if G contains no K_{2r+1} and 3r-1 | d then D <= (3r-1)/r
      n/d + O(1)"), encoded as the conjecture of EPPT89 (pp.78-79): "Let r, delta > 1 be fixed natural numbers", both
      parts, "while n -> +infinity", so the O(1) constant C depends on r and d (forall r d, exists C).  D, the
      largest distance, is at most the bound iff every distance is; the inequalities are multiplied through by
      (2r^2 - 1) d, resp. r d; for fixed r and d the finitely many small orders are absorbed in C, so the form for
      every n is the form "while n -> infinity".  r - 1, 2r^2 - 1 and 3r - 1 never truncate for r >= 2.  The case
      r = 1 of the second part (triangle-free graphs) is a theorem of EPPT89, outside the printed range.
      Literature status: FALSE at the pin (pinned status open): Czabarka, Singgih and Szekely, JCTB 151 (2021) 38-45,
      Theorem 3 (the publisher's abstract and theorem, read by the Mac; the live page: K_{2r}-free graphs of minimum
      degree d and diameter (6r-5) n / ((2r-1) d + 2r - 3) + O(1)) refute the first part for every r >= 2 at large
      admissible d: (6r-5)(2r^2-1) - 2(r-1)(3r+2)(2r-1) = 1 > 0, so their linear coefficient exceeds the conjectured
      one (for r = 2 once d > 16), which also refutes the form with C depending on d.  The live page also records
      Cambie and Jooken (K_4-free, d = 16, diameter >= 31n/216 + O(1)), not checked here.  The second part is open. *)
Definition clique_free_diameter_min_degree_statement : Prop :=
  forall r d : nat, 2 <= r -> 2 <= d -> exists C : nat,
    (forall G : sgraph, connected [set: G] -> min_degree G d ->
       ~ has_subgraph G 'K_(2 * r) -> ((r - 1) * (3 * r + 2)) %| d ->
       forall x y : G,
         (2 * r ^ 2 - 1) * d * graph_dist x y <= 2 * (r - 1) * (3 * r + 2) * #|G| + C * (2 * r ^ 2 - 1) * d) /\
    (forall G : sgraph, connected [set: G] -> min_degree G d ->
       ~ has_subgraph G 'K_(2 * r + 1) -> (3 * r - 1) %| d ->
       forall x y : G, r * d * graph_dist x y <= (3 * r - 1) * #|G| + C * r * d).
