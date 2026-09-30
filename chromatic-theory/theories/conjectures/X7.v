(** * Chromatic.conjectures.X7 -- v2 clean chromatic continuation

    A narrow X7 starter batch: five direct chromatic/list-colouring rows whose
    statements reuse the existing finite-graph surface from U4/XE1/XE2. *)

From GraphTheory Require Import minor.
From GTBase Require Export base.
From Chromatic.conjectures Require Import XE1 XE2.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X7 vocabulary *************************************************)

Definition x7_delete_edges_rel (G : sgraph) (F : {set {set G}}) : rel G :=
  fun x y => (x -- y) && ([set x; y] \notin F).

Lemma x7_delete_edges_sym (G : sgraph) (F : {set {set G}}) :
  symmetric (@x7_delete_edges_rel G F).
Proof.
move=> x y; rewrite /x7_delete_edges_rel.
rewrite sgP.
by rewrite setUC.
Qed.

Lemma x7_delete_edges_irrefl (G : sgraph) (F : {set {set G}}) :
  irreflexive (@x7_delete_edges_rel G F).
Proof. by move=> x; rewrite /x7_delete_edges_rel sg_irrefl. Qed.

Definition x7_delete_edges (G : sgraph) (F : {set {set G}}) : sgraph :=
  SGraph (@x7_delete_edges_sym G F) (@x7_delete_edges_irrefl G F).

Definition x7_no_critical_edge (G : sgraph) (k : nat) : Prop :=
  forall F : {set G},
    F \in @xe1_edge_set G ->
    χ([set: @x7_delete_edges G [set F]]) = k.

Definition x7_edge_deletion_preserves_chromatic
    (G : sgraph) (k r : nat) : Prop :=
  forall R : {set {set G}},
    R \subset @xe1_edge_set G ->
    #|R| <= r ->
    χ([set: @x7_delete_edges G R]) = k.

Definition x7_four_one_graph (G : sgraph) : Prop :=
  χ([set: G]) = 4 /\
  xe1_vertex_critical G 4 /\
  x7_no_critical_edge G 4.

(** ** X7 statements *******************************************************)

(** Corpus row: arxiv:1803.01051#01
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/1803.01051__01/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/1803.01051__01.json
    English statement: (Bonamy, Kelly, Nelson and Postle 2018, list-chromatic analogue of Reed's Conjecture 1.3, arXiv:1803.01051)
      Every finite simple graph G satisfies ch(G) <= ceiling of (Delta(G) + 1 + omega(G)) / 2, where
      ch(G) is the choice number, i.e. the list-chromatic number.
    Definitions: [is_choice_number G ch] - ch is the least k such that G is k-choosable (GTBase
      base/theories/base.v); [ceil_div a b] - ceiling of a/b with ceil_div a 0 = 0 (base.v); [Delta
      G] (base.v); omega is the coq-graph-theory clique number.
    Notes: The source states the bound for every graph of maximum degree at most Delta with no
      clique larger than omega; taking Delta and omega to be the actual invariants of G, as the Rocq
      body does, is the same statement since both sides are monotone in those parameters. Unlike
      U1's Reed row, the ceiling is expressed with [ceil_div] rather than in doubled form. *)
Definition list_reed_choice_number_statement : Prop :=
  forall (G : sgraph) (ch : nat),
    is_choice_number G ch ->
    ch <= ceil_div (Delta G + 1 + ω([set: G])) 2.

(** Corpus row: arxiv:2110.09403#00
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/2110.09403__00/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/2110.09403__00.json
    English statement: (Steiner 2021, Problem 1, arXiv:2110.09403)
      For every t >= 1 and every finite simple graph G having no complete graph on t vertices as a
      minor, the choice number of G is at most 2t.
    Definitions: [minor G H] - H is a minor of G (coq-graph-theory minor.v); [is_choice_number]
      (GTBase base/theories/base.v).
    Notes: The corpus row is a QUESTION, "Does every K_t-minor-free graph satisfy chi_l(G) <=
      2t?"; the Rocq body is its affirmative reading. The guard 1 <= t excludes the degenerate t =
      0, where no graph is K_0-minor-free. *)
Definition list_hadwiger_two_t_statement : Prop :=
  forall (t ch : nat) (G : sgraph),
    1 <= t ->
    ~ minor G ('K_t) ->
    is_choice_number G ch ->
    ch <= 2 * t.

(** Corpus row: arxiv:2310.12891#00
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/2310.12891__00/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/2310.12891__00.json
    English statement: (Martinsson and Steiner 2023, fixed-small-k open case of an Erdos problem, arXiv:2310.12891)
      For every k >= 4 and every r there exists a finite simple graph G with chromatic number
      exactly k, vertex-critical, i.e. deleting any single vertex lowers the chromatic number below
      k, and such that deleting any set of at most r edges leaves the chromatic number equal to k.
    Definitions: [xe1_vertex_critical G k] - for every vertex v, chi of the subgraph induced on
      the other vertices is less than k (XE1.v); [x7_delete_edges G R] - the graph with the edges in
      R removed, edges being 2-element vertex sets (this file);
      [x7_edge_deletion_preserves_chromatic G k r] - every set R of at most r edges satisfies chi(G
      - R) = k (this file); [xe1_edge_set G] - the set of edges of G as 2-element vertex sets
      (XE1.v).
    Notes: The corpus row is a QUESTION about fixed k and arbitrarily large r; the Rocq body is
      its affirmative reading with r universally quantified and G depending on both k and r. Corpus
      status: Skottova and Steiner 2025 settled the case k >= 5 affirmatively; the case k = 4
      remains open, so the statement as quantified over all k >= 4 is still open. *)
Definition fixed_k_vertex_critical_edge_robust_statement : Prop :=
  forall k r : nat, 4 <= k ->
    exists G : sgraph,
      χ([set: G]) = k /\
      xe1_vertex_critical G k /\
      x7_edge_deletion_preserves_chromatic G k r.

(** Corpus row: arxiv:2408.02400#00
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/2408.02400__00/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/2408.02400__00.json
    English statement: (Steiner 2024, Problem 1.5, arXiv:2408.02400)
      For every k >= 5 there exists a finite simple graph G with clique number less than 5,
      cochromatic number exactly k, and chromatic number exactly k + 3.
    Definitions: [xe2_cochromatic_number G k] - k is the least number of parts in a partition of
      the vertices into colour classes each of which is a clique or a stable set (XE2.v);
      [xe2_cochromatic_colouring G k] - such a partition with k parts exists (XE2.v);
      [xe1_stable_set] (XE1.v).
    Notes: The corpus row is a QUESTION; the Rocq body is its affirmative reading, with the gap
      chi - zeta = 3 written as the equality chi = k + 3 to avoid nat subtraction. *)
Definition cochromatic_gap_three_statement : Prop :=
  forall k : nat, 5 <= k ->
    exists G : sgraph,
      ω([set: G]) < 5 /\
      xe2_cochromatic_number G k /\
      χ([set: G]) = k + 3.

(** Corpus row: arxiv:2508.08703#00
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/2508.08703__00/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/2508.08703__00.json
    English statement: (Skottova and Steiner 2025, Problem 5.2, arXiv:2508.08703)
      There exists a 6-regular finite simple graph that is a (4,1)-graph, that is, it has chromatic
      number 4, deleting any single vertex lowers the chromatic number below 4, and deleting any
      single edge leaves the chromatic number equal to 4, so no edge is critical.
    Definitions: [x7_four_one_graph G] - chi(G) = 4, [xe1_vertex_critical G 4] and
      [x7_no_critical_edge G 4] (this file); [x7_no_critical_edge G k] - for every edge F, chi of G
      with that single edge deleted is still k (this file); [regular G 6] - every vertex has exactly
      6 neighbours (GTBase base/theories/base.v).
    Notes: The corpus row is a QUESTION, "Does there exist a 6-regular (4,1)-graph?"; the Rocq
      body is its affirmative reading. The definition of a (4,1)-graph is taken from the paper's
      context as recorded in the corpus row. *)
Definition six_regular_four_one_graph_statement : Prop :=
  exists G : sgraph,
    regular G 6 /\ x7_four_one_graph G.
