(** * Extremal.conjectures.X13 -- v2 induced-subgraph rows *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X13 vocabulary ************************************************)

Definition x13_min_degree_at_least (G : sgraph) (d : nat) : Prop :=
  forall v : G, d <= #|N(v)|.

Definition x13_unbounded (f : nat -> nat) : Prop :=
  forall b : nat, exists d0 : nat, forall d : nat, d0 <= d -> b <= f d.

Definition x13_complete_subgraph_size_at_least (G : sgraph) (m : nat) : Prop :=
  exists S : {set G}, m <= #|S| /\ clique S.

Definition x13_induced_min_degree_at_least
    (G : sgraph) (S : {set G}) (d : nat) : Prop :=
  forall v : induced S, d <= #|N(v)|.

Definition x13_bipartite_induced_min_degree_at_least
    (G : sgraph) (d : nat) : Prop :=
  exists S : {set G},
    S != set0 /\
    bipartite (induced S) /\
    x13_induced_min_degree_at_least S d.

(** Corpus row: arxiv:1802.03727#01
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/1802.03727__01/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/1802.03727__01.json
    English statement: (Esperet, Kang, Thomasse 2018, arXiv:1802.03727 Conjecture 1.4)
      There are functions x2 and x3 from naturals to naturals, both positive everywhere and
      both tending to infinity, such that for every d > 0 and every non-empty graph G of
      minimum degree at least d, either G has a clique on at least x2(d) vertices, or G has a
      non-empty induced subgraph that is bipartite and has minimum degree at least x3(d).
    Definitions: [x13_min_degree_at_least G d] - every vertex has at least d neighbours (X13.v);
      [x13_unbounded f] - for every bound b there is d0 with b <= f d for all d >= d0, i.e.
      f tends to infinity (X13.v); [x13_complete_subgraph_size_at_least G m] - some clique has
      at least m vertices (X13.v); [x13_induced_min_degree_at_least G S d] - every vertex of the
      subgraph induced on S has at least d neighbours THERE (X13.v);
      [x13_bipartite_induced_min_degree_at_least G d] - some non-empty S induces a bipartite
      graph of minimum degree at least d (X13.v); [bipartite], [induced], [clique] - GTBase /
      coq-graph-theory.
    Notes: the corpus records this row as PARTIAL: Kwan, Sudakov and Tran (Combinatorica 2020,
      arXiv:1810.12144) proved the K_t-free case, confirming Conjecture 1.3 of the source paper,
      but the general dichotomy is open. The guards 0 < d and 0 < |V(G)| and the positivity of
      x2 and x3 are added so that the two disjuncts are non-degenerate (the empty induced
      subgraph would otherwise satisfy the second one vacuously). *)
Definition min_degree_forces_large_clique_or_bipartite_induced_statement : Prop :=
  exists x2 x3 : nat -> nat,
    x13_unbounded x2 /\ x13_unbounded x3 /\
    (forall d : nat, 0 < x2 d /\ 0 < x3 d) /\
    forall (d : nat) (G : sgraph),
      0 < d -> 0 < #|G| ->
      x13_min_degree_at_least G d ->
      x13_complete_subgraph_size_at_least G (x2 d) \/
      x13_bipartite_induced_min_degree_at_least G (x3 d).

(** Corpus row: arxiv:1802.03727#03
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/1802.03727__03/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/1802.03727__03.json
    English statement: (Esperet, Kang, Thomasse 2018, arXiv:1802.03727 Conjecture 1.6)
      There are thresholds d0 > 0 and g0 > 0 such that every non-empty graph of girth at least
      g0 and minimum degree at least d0 has a non-empty induced subgraph that is bipartite and
      has minimum degree at least 3.
    Definitions: [x13_min_degree_at_least G d] - every vertex has at least d neighbours (X13.v);
      [x13_bipartite_induced_min_degree_at_least G d] - some non-empty vertex set induces a
      bipartite graph of minimum degree at least d (X13.v); [girth_geq G g] - every cycle of G
      has length at least g (GTBase); [bipartite], [induced] - GTBase / coq-graph-theory.
    Notes: the non-emptiness guards 0 < |V(G)| and S != set0 keep the conclusion from being
      satisfied vacuously by the empty induced subgraph. *)
Definition large_girth_min_degree_bipartite_induced_statement : Prop :=
  exists d0 g0 : nat,
    0 < d0 /\ 0 < g0 /\
    forall G : sgraph,
      0 < #|G| ->
      girth_geq G g0 ->
      x13_min_degree_at_least G d0 ->
      x13_bipartite_induced_min_degree_at_least G 3.
