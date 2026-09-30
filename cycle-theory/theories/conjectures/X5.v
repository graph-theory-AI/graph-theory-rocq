(** * Cycle.conjectures.X5 -- v2 milestone X5, clean simple-cycle rows *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local simple-graph cycle vocabulary *********************************)

Definition x5_edge_count (G : sgraph) : nat :=
  #|[set p : G * G |
      (p.1 -- p.2) && ((enum_rank p.1) < (enum_rank p.2))%N]|.

Definition x5_vertices_of_seq (G : sgraph) (c : seq G) : {set G} :=
  [set v : G | v \in c].

Definition x5_cycle_family_disjoint
    (G : sgraph) (k : nat) (cs : 'I_k -> seq G) : Prop :=
  forall i j : 'I_k, i != j ->
    [disjoint x5_vertices_of_seq (cs i) & x5_vertices_of_seq (cs j)].

(** ** X5 statements *******************************************************)

(** Corpus row: erdos:64
    Site: none
    Review: none
    English statement: (Erdos problem #64)
      Every simple graph with at least one vertex in which every vertex has at least three
      neighbours contains a cycle whose length is a power of two with exponent at least 2,
      that is, there are a natural number k at least 2 and a cycle with exactly 2 to the
      power k vertices.
    Definitions: standard: [ucycle] (MathComp path.v), [N(v)] - the open neighbourhood
      (coq-graph-theory sgraph, re-exported by base/theories/base.v).
    Notes: the Rocq body says "some cycle has length 2^k for some k >= 2", which is the
      source's "a cycle of length 2^k for some k >= 2". Cycles are [ucycle] sequences;
      since the length is at least 4 the degenerate short [ucycle] artefacts cannot
      satisfy it. The guard [0 < #|G|] excludes the empty graph, where the
      minimum-degree hypothesis holds vacuously. The corpus row has no site or review
      page. *)
Definition min_degree_three_power_two_cycle_statement : Prop :=
  forall G : sgraph,
    0 < #|G| ->
    (forall v : G, 3 <= #|N(v)|) ->
    exists (k : nat) (c : seq G),
      2 <= k /\ ucycle (--) c /\ size c = 2 ^ k.

(** Corpus row: erdos:577
    Site: none
    Review: none
    English statement: (Erdos problem #577)
      For every natural number k and every simple graph G with exactly 4k vertices in which
      every vertex has at least 2k neighbours, there are k cycles, indexed by the integers
      below k, each of length exactly 4, whose vertex sets are pairwise disjoint.
    Definitions: [x5_vertices_of_seq c] - the set of vertices occurring in the sequence c
      (X5.v); [x5_cycle_family_disjoint cs] - the vertex sets of the cycles cs i are
      pairwise disjoint (X5.v); [ucycle] (MathComp path.v); [N(v)] (coq-graph-theory
      sgraph).
    Notes: the corpus records this row as SOLVED; the Rocq statement is the assertion
      itself, not a proof. The family of cycles is indexed by a finite ordinal type, which
      makes "k vertex-disjoint 4-cycles" precise, including k = 0. The corpus row has no
      site or review page. *)
Definition min_degree_half_disjoint_four_cycles_statement : Prop :=
  forall (k : nat) (G : sgraph),
    #|G| = 4 * k ->
    (forall v : G, 2 * k <= #|N(v)|) ->
    exists cs : 'I_k -> seq G,
      (forall i : 'I_k, ucycle (--) (cs i) /\ size (cs i) = 4) /\
      x5_cycle_family_disjoint cs.

(** Corpus row: erdos:916
    Site: none
    Review: none
    English statement: (Erdos problem #916)
      For every natural number n at least 2 and every simple graph G with exactly n
      vertices and exactly 2n-2 edges there are a cycle c through more than two vertices
      and a vertex v not on c such that v has at least three neighbours among the vertices
      of c.
    Definitions: [x5_edge_count G] - the number of edges, counted as ordered adjacent pairs
      whose first component has the smaller enumeration rank (X5.v);
      [x5_vertices_of_seq c] - the vertices occurring in c (X5.v); [ucycle] (MathComp
      path.v); [N(v)] (coq-graph-theory sgraph).
    Notes: the corpus records this row as SOLVED; the Rocq statement is the assertion
      itself. The edge count is defined through enumeration ranks to pick one
      representative per unordered adjacent pair. The edge count is written [2 * n - 2]
      with truncated natural subtraction, harmless because n is at least 2. The corpus
      row has no site or review page. *)
Definition cycle_with_external_three_neighbours_statement : Prop :=
  forall (n : nat) (G : sgraph),
    2 <= n ->
    #|G| = n ->
    x5_edge_count G = 2 * n - 2 ->
    exists (c : seq G) (v : G),
      ucycle (--) c /\
      2 < size c /\
      v \notin c /\
      3 <= #|N(v) :&: x5_vertices_of_seq c|.
