(** * Cycle.conjectures.X9 -- v2 clean cycle rows *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X9 vocabulary *************************************************)

Definition x9_edge_set (G : sgraph) : {set {set G}} :=
  [set e : {set G} |
      [exists x : G, [exists y : G, (x -- y) && (e == [set x; y])]]].

Definition x9_cycle_edges (G : sgraph) (c : seq G) : seq {set G} :=
  map (fun p : G * G => [set p.1; p.2]) (zip c (rot 1 c)).

Definition x9_genuine_cycle (G : sgraph) (c : seq G) : Prop :=
  ucycle (--) c /\ 2 < size c.

Definition x9_colour_classes_large
    (G : sgraph) (n r : nat) (col : {set G} -> 'I_n) : Prop :=
  forall i : 'I_n, r <= #|[set e in x9_edge_set G | col e == i]|.

Definition x9_cycle_incident_edges_properly_coloured
    (G : sgraph) (n : nat) (col : {set G} -> 'I_n) (c : seq G) : Prop :=
  forall e f : {set G},
    e \in @x9_cycle_edges G c ->
    f \in @x9_cycle_edges G c ->
    e != f ->
    ~~ [disjoint e & f] ->
    col e != col f.

Definition x9_consecutive_in_cycle (G : sgraph) (c : seq G) (u v : G) : bool :=
  ((u, v) \in zip c (rot 1 c)) || ((v, u) \in zip c (rot 1 c)).

Definition x9_cycle_chord_count (G : sgraph) (c : seq G) : nat :=
  #|[set p : G * G |
      [&& p.1 \in c, p.2 \in c, (enum_rank p.1 < enum_rank p.2)%N,
          p.1 -- p.2 & ~~ x9_consecutive_in_cycle c p.1 p.2]]|.

(** ** X9 statements *******************************************************)

(** Corpus row: arxiv:1806.00825#00
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/1806.00825__00/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/1806.00825__00.json
    English statement: (DeVos, Drescher, Funk, Gonzalez Hermosillo de la Maza, Guo, Huynh,
      Mohar, Montejano 2020, "Conjecture 4" of "Short rainbow cycles in graphs and
      matroids")
      For all positive natural numbers n and r, every simple graph G on exactly n vertices
      and every colouring of its vertex pairs with n colours such that each colour class
      contains at least r edges, there is a cycle c through more than two vertices whose
      length is at most the ceiling of n/r and such that any two distinct edges of c that
      share a vertex receive different colours.
    Definitions: [x9_edge_set G] - the two-element vertex sets that are edges (X9.v);
      [x9_cycle_edges c] - the list of consecutive-pair edges of c (X9.v);
      [x9_genuine_cycle c] - c is a [ucycle] of length more than two (X9.v);
      [x9_colour_classes_large G n r col] - each of the n colour classes has at least r
      edges (X9.v); [x9_cycle_incident_edges_properly_coloured col c] - distinct edges of c
      that meet receive distinct colours (X9.v); [ceil_div] (base/theories/base.v);
      [ucycle] (MathComp path.v).
    Notes: this is the paper's weakening of Aharoni's rainbow conjecture, the rainbow
      condition on the whole cycle being replaced by a proper-colouring condition on
      incident pairs; the neighbouring row in X10.v carries the rainbow version. *)
Definition proper_edge_coloured_short_cycle_statement : Prop :=
  forall (n r : nat) (G : sgraph) (col : {set G} -> 'I_n),
    0 < n -> 0 < r -> #|G| = n ->
    @x9_colour_classes_large G n r col ->
    exists c : seq G,
      @x9_genuine_cycle G c /\
      size c <= ceil_div n r /\
      @x9_cycle_incident_edges_properly_coloured G n col c.

(** Corpus row: arxiv:2502.04726#03
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/2502.04726__03/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/2502.04726__03.json
    English statement: (Dvorak, Martins, Thomasse, Trotignon 2025, "Question 4.3" of
      "Lollipops, dense cycles and chords")
      There are positive natural numbers p and q such that every simple graph with at least
      one vertex in which every vertex has at least three neighbours contains a cycle c
      through more than two vertices with q times the number of chords of c at least p
      times the length of c; that is, the number of chords is at least the constant p/q
      times the length.
    Definitions: [x9_genuine_cycle c] - c is a [ucycle] of length more than two (X9.v);
      [x9_consecutive_in_cycle c u v] - u and v are consecutive along c in either order
      (X9.v); [x9_cycle_chord_count c] - the number of adjacent pairs of vertices of c,
      counted once per unordered pair via enumeration ranks, that are not consecutive along
      c (X9.v); [N(v)] (coq-graph-theory sgraph).
    Notes: the real constant c > 0 of the source is encoded as a ratio of two positive
      natural numbers p/q, existentially quantified, and the inequality is cross-multiplied
      over the naturals to stay axiom-free. The corpus status is PARTIAL: an
      almost-linear bound is known, the linear one asked here is open. *)
Definition min_degree_three_linearly_many_chords_cycle_statement : Prop :=
  exists cnum cden : nat,
    0 < cnum /\ 0 < cden /\
    forall G : sgraph,
      0 < #|G| ->
      (forall v : G, 3 <= #|N(v)|) ->
      exists c : seq G,
        @x9_genuine_cycle G c /\
        cden * @x9_cycle_chord_count G c >= cnum * size c.
