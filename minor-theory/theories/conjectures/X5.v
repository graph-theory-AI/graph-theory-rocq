(** * Minor.conjectures.X5 -- v2 milestone X5, clean minor-structural rows *)

From GraphTheory Require Import minor.
From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** X5 statements *******************************************************)

(** Corpus row: arxiv:1907.12999#00
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/1907.12999__00/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/1907.12999__00.json
    English statement: (Dvorak and Yepremyan 2019, "Independence number in triangle-free graphs
      avoiding a minor", Conjecture 1)
      For every positive integer t, every finite simple graph on n vertices that does not
      contain the complete graph on t+1 vertices as a minor has independence number at least
      n/t.
    Definitions: standard
    Notes: the conclusion is stated division-free as n <= t * alpha(G), which over the naturals
      is equivalent to alpha(G) >= n/t.  [minor G H] is the library order, "G contains H as a
      minor".  No nonemptiness guard is needed: for n = 0 the conclusion 0 <= t * alpha(G)
      holds. *)
Definition hadwiger_independence_minor_statement : Prop :=
  forall (t n : nat) (G : sgraph),
    0 < t -> #|G| = n -> ~ minor G 'K_(t.+1) ->
    n <= t * α(G).

(** Corpus row: arxiv:2204.10119#00
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/2204.10119__00/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/2204.10119__00.json
    English statement: (Chudnovsky, Scott, Seymour and Spirkl 2022, "Bipartite graphs with no K_6 minor", Conjecture 1.3)
      Every nonempty 6-regular finite simple graph contains the complete graph on 6 vertices as
      a minor.
    Definitions: standard
    Notes: "non-null" is the guard [0 < #|G|], required for soundness because the empty graph is
      vacuously 6-regular yet has no K_6 minor.  [regular G 6] (GTBase) says every vertex has
      degree exactly 6. *)
Definition six_regular_has_k6_minor_statement : Prop :=
  forall G : sgraph,
    0 < #|G| -> regular G 6 -> minor G 'K_6.

(** Corpus row: arxiv:2204.10119#01
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/2204.10119__01/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/2204.10119__01.json
    English statement: (Chudnovsky, Scott, Seymour and Spirkl 2022, "Bipartite graphs with no K_6 minor", informal conjecture
      stated immediately after Conjecture 1.3)
      Every nonempty finite simple graph with minimum degree at least six and maximum degree at
      most eight contains the complete graph on 6 vertices as a minor.
    Definitions: standard
    Notes: minimum degree at least six is [forall v, 6 <= #|N(v)|]; maximum degree at most eight
      is [Delta G <= 8] (GTBase).  The [0 < #|G|] guard rules out the vacuously qualifying empty
      graph.  This belief is stronger than Conjecture 1.3 of the same paper (the previous
      row). *)
Definition min_degree_six_max_degree_eight_k6_minor_statement : Prop :=
  forall G : sgraph,
    0 < #|G| ->
    (forall v : G, 6 <= #|N(v)|) ->
    Delta G <= 8 ->
    minor G 'K_6.

(** Corpus row: arxiv:2204.10119#02
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/2204.10119__02/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/2204.10119__02.json
    English statement: (Chudnovsky, Scott, Seymour and Spirkl 2022, "Bipartite graphs with no K_6 minor", open question raised
      immediately after Theorem 1.6)
      Every nonempty bipartite finite simple graph with minimum degree at least five contains
      the complete graph on 6 vertices as a minor - that is, whether "six" can be replaced by
      "five" in the paper's Theorem 1.6.
    Definitions: standard
    Notes: [bipartite G] (GTBase) is the existence of a two-colouring of the vertices under
      which adjacent vertices receive different colours.  The [0 < #|G|] guard rules out the
      vacuously qualifying empty graph.  The row records an open question, so the affirmative
      reading is formalised. *)
Definition bipartite_min_degree_five_k6_minor_statement : Prop :=
  forall G : sgraph,
    0 < #|G| -> bipartite G ->
    (forall v : G, 5 <= #|N(v)|) ->
    minor G 'K_6.

(** Corpus row: arxiv:2204.10119#03
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/2204.10119__03/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/2204.10119__03.json
    English statement: (Chudnovsky, Scott, Seymour and Spirkl 2022, "Bipartite graphs with no K_6 minor", informal conjecture)
      Every nonempty bipartite finite simple graph with average degree at least five and maximum
      degree at most six contains the complete graph on 5 vertices as a minor.
    Definitions: standard
    Notes: [average_degree_geq G 5 1] (GTBase) unfolds to 5 * #|G| <= 1 * (sum of the degrees),
      i.e. average degree at least 5.  The [0 < #|G|] guard rules out the empty graph, which
      satisfies the degree hypothesis vacuously.  The authors state this as a suggestion they
      have not verified. *)
Definition bipartite_average_degree_five_max_six_k5_minor_statement : Prop :=
  forall G : sgraph,
    0 < #|G| -> bipartite G ->
    average_degree_geq G 5 1 ->
    Delta G <= 6 ->
    minor G 'K_5.

(** Corpus row: studies:std_clique_minor_conjecture_for_bounded_independence
    Site: none
    Review: none
    English statement: (attributed in the source paper to its reference [28]; "clique minor
      conjecture for bounded independence number")
      For every r at least 1, every finite simple graph on n vertices whose independence number
      is at most r contains, as a minor, the complete graph on the ceiling of n/r vertices.
    Definitions: standard
    Notes: "a clique minor of order n/r" is given its strongest integral reading, the ceiling
      [ceil_div n r] (GTBase).  No nonemptiness guard is needed: at n = 0 the conclusion asks
      for a K_0 minor, which every graph has. *)
Definition bounded_independence_clique_minor_statement : Prop :=
  forall (r n : nat) (G : sgraph),
    0 < r -> #|G| = n -> α(G) <= r ->
    minor G 'K_(ceil_div n r).
