(** * Packing.conjectures.X15 -- v2 fair matching representation rows *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X15 vocabulary ************************************************)

Definition x15_edge_set (G : sgraph) : {set {set G}} :=
  [set e : {set G} |
      [exists x : G, [exists y : G, (x -- y) && (e == [set x; y])]]].

Definition x15_matching (G : sgraph) (M : {set {set G}}) : Prop :=
  M \subset x15_edge_set G /\
  forall v : G, #|[set e in M | v \in e]| <= 1.

Definition x15_edge_partition
    (G : sgraph) (m : nat) (E : 'I_m -> {set {set G}}) : Prop :=
  (forall e : {set G},
      (e \in x15_edge_set G) = [exists i : 'I_m, e \in E i]) /\
  forall i j : 'I_m, i != j -> [disjoint E i & E j].

Definition x15_edge_family
    (G : sgraph) (m : nat) (E : 'I_m -> {set {set G}}) : Prop :=
  forall i : 'I_m, E i \subset x15_edge_set G.

(** ** X15 statements ******************************************************)

(** Corpus row: arxiv:1611.03196#02
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/1611.03196__02/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/1611.03196__02.json
    English statement: (Aharoni, Alon, Berger, Chudnovsky, Kotlar, Loebl, Ziv 2016,
      "Conjecture 1.14")
      For every m, every simple graph H and every family E_0, ..., E_{m-1} of sets of
      edges of H that partitions the edge set of H, there is a matching M of H such
      that for every i, the number of edges of M inside E_i is at least the floor of
      |E_i| divided by Delta(H) + 2.
    Definitions: [x15_edge_set G] — the two-element vertex sets {x, y} with x -- y
      (this file); [x15_matching M] — M is a set of edges of G in which every vertex
      lies in at most one member (this file); [x15_edge_partition E] — an edge belongs
      to the edge set of G exactly when it belongs to some part, and distinct parts are
      disjoint (this file); [Delta] — maximum degree (GTBase base).
    Notes: REFUTED (branch fair-matching-edge-part of this repository, file
      theories/applications/fair_matching_edge_partition_disproved.v): the graph 5 K_4
      (five disjoint copies of K_4, on 'I_20) with six classes of five edges each is a
      counterexample, so the conjecture is false. The parts are indexed by 'I_m, so
      m = 0 forces the graph to be edgeless; the bound uses MathComp floor division. *)
Definition fair_matching_edge_partition_statement : Prop :=
  forall (m : nat) (H : sgraph) (E : 'I_m -> {set {set H}}),
    x15_edge_partition E ->
    exists M : {set {set H}},
      x15_matching M /\
      forall i : 'I_m,
        (#|E i| %/ (Delta H + 2) <= #|M :&: E i|)%N.

(** Corpus row: arxiv:1611.03196#03
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/1611.03196__03/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/1611.03196__03.json
    English statement: (Aharoni, Alon, Berger, Chudnovsky, Kotlar, Loebl, Ziv 2016,
      "Conjecture 1.15")
      For every m there is a constant c such that for every bipartite simple graph G of
      positive maximum degree and every family E_0, ..., E_{m-1} of sets of edges of G
      (not required to be a partition), there is a matching S of G with
      floor(|E(G)| / Delta(G)) <= |S| + c and, for every i, the number of edges of S
      inside E_i at most the ceiling of |E_i| divided by Delta(G).
    Definitions: [x15_edge_set G] — the two-element vertex sets {x, y} with x -- y
      (this file); [x15_matching S] — a set of edges in which every vertex lies at most
      once (this file); [x15_edge_family E] — every part is a set of edges of G (this
      file); [bipartite], [Delta], [ceil_div a b] = (a+b-1) %/ b (GTBase base).
    Notes: PROVED in this development — theories/foundations/fair_matching.v derives it
      with the explicit constant c(m) = 12m + 14. The size bound |S| >= |E(G)|/Delta(G)
      - c is rendered over naturals as floor(|E(G)|/Delta(G)) <= |S| + c, avoiding
      truncated subtraction; the guard 0 < Delta(G) excludes the edgeless graph, where
      division by Delta(G) = 0 is degenerate. *)
Definition bipartite_matching_underrepresentation_statement : Prop :=
  forall m : nat, exists c : nat,
    forall (G : sgraph) (E : 'I_m -> {set {set G}}),
      bipartite G ->
      0 < Delta G ->
      x15_edge_family E ->
      exists S : {set {set G}},
        x15_matching S /\
        (#|x15_edge_set G| %/ Delta G <= #|S| + c)%N /\
        forall i : 'I_m,
          #|S :&: E i| <= ceil_div #|E i| (Delta G).

(** No corpus row: LLM-proof variant of bipartite_matching_underrepresentation_statement (arxiv:1611.03196#03) with an explicit constant; see https://github.com/graph-theory-AI/Graph-Theory-LLM-Proofs/blob/main/attacks/1611.03196__03/output.md *)
Definition bipartite_matching_underrepresentation_llm_statement : Prop :=
  forall m : nat, exists c : nat,
    c <= 32 * (m + 1)^3 /\
    forall (G : sgraph) (E : 'I_m -> {set {set G}}),
      bipartite G ->
      0 < Delta G ->
      x15_edge_family E ->
      exists S : {set {set G}},
        x15_matching S /\
        (#|x15_edge_set G| %/ Delta G <= #|S| + c)%N /\
        forall i : 'I_m,
          #|S :&: E i| <= ceil_div #|E i| (Delta G).


(** the constant of the first version of foundations/fair_matching.v: one
    halving per pair along a binary mixing tree, then a trimming phase *)
(** No corpus row: LLM-proof variant of bipartite_matching_underrepresentation_statement (arxiv:1611.03196#03) with an explicit constant; see https://github.com/graph-theory-AI/Graph-Theory-LLM-Proofs/blob/main/attacks/1611.03196__03/output.md *)
Definition bipartite_matching_underrepresentation_llm2_statement : Prop :=
  forall m : nat, exists c : nat,
    c <= (m + 1)^2 * (16*m + 29) /\
    forall (G : sgraph) (E : 'I_m -> {set {set G}}),
      bipartite G ->
      0 < Delta G ->
      x15_edge_family E ->
      exists S : {set {set G}},
        x15_matching S /\
        (#|sg_edge_set G| %/ Delta G <= #|S| + c)%N /\
        forall i : 'I_m,
          #|S :&: E i| <= ceil_div #|E i| (Delta G).

(** what is proved in foundations/fair_matching.v: the constant of the
    synchronized-rounds proof, linear in m — one exact halving per round of a
    balanced mixing of the colour classes, all the pairs of a round split by a
    single necklace splitting.  The three statements above are corollaries. *)
(** No corpus row: LLM-proof variant of bipartite_matching_underrepresentation_statement (arxiv:1611.03196#03) with an explicit constant; see https://github.com/graph-theory-AI/Graph-Theory-LLM-Proofs/blob/main/attacks/1611.03196__03/output.md *)
Definition bipartite_matching_underrepresentation_llm3_statement : Prop :=
  forall m : nat, exists c : nat,
    c <= 12 * m + 14 /\
    forall (G : sgraph) (E : 'I_m -> {set {set G}}),
      bipartite G ->
      0 < Delta G ->
      x15_edge_family E ->
      exists S : {set {set G}},
        x15_matching S /\
        (#|sg_edge_set G| %/ Delta G <= #|S| + c)%N /\
        forall i : 'I_m,
          #|S :&: E i| <= ceil_div #|E i| (Delta G).
