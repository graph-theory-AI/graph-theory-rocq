(** * Extremal.conjectures.X280 -- v2 rows: pure pairs with a linear side (Possibility 1.6), Erdos #805 at (log n)^3 *)

From GTBase Require Import base set_pairs.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local x280 vocabulary ************************************************* *)

(** [x280_congestion_at_most H q]: the congestion of H is at most 1 / q.  Scott, Seymour and Spirkl (arXiv:2201.04062v2,
    main.tex l.139-144) define the congestion of a graph H with an edge as the maximum of 1 - (|J| - 1) / |E(J)| over
    the subgraphs J of H with at least one edge, and as zero when H has no edge.  A subgraph J is a vertex set S with a
    set F of edges of H inside S; then 1 - (|S| - 1) / |F| <= 1 / q is q |F| <= q (|S| - 1) + |F|, which keeps a
    negative left side (forests) without truncating it.  An edgeless H satisfies the condition vacuously (congestion
    zero).  The subtraction |S| - 1 is exact, guarded by the edge of F inside S (|S| >= 2). *)
Definition x280_congestion_at_most (H : sgraph) (q : nat) : Prop :=
  forall (S : {set H}) (F : {set {set H}}),
    F \subset E(H) -> (forall e : {set H}, e \in F -> e \subset S) -> 0 < #|F| ->
      q * #|F| <= q * (#|S| - 1) + #|F|.

(** ** X280 statements ******************************************************* *)

(** Corpus row: arxiv:2201.04062#00
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/2201.04062__00/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/2201.04062__00.json
    English statement: (Scott, Seymour and Spirkl, Pure pairs. VIII. Excluding a sparse graph, Possibility 1.6)
      For all c > 0, there exists xi > 0 with the following property.  For every graph H with congestion at most xi,
      there exists eps > 0 such that for every graph G with |G| > 1 that is H-free and complement-H-free, there is a
      pure pair A, B in G with |A| >= eps |G| and |B| >= eps |G|^(1-c).
    Definitions: [x280_congestion_at_most H q] - the congestion of H is at most 1 / q (this file); [induced_free G H] -
      no induced subgraph of G is isomorphic to H (GTBase common.v); [compl H] - the complement of H
      (coq-graph-theory); [complete_between A B] - every vertex of A adjacent to every vertex of B, and
      [anticomplete A B] - A, B disjoint with no edge between them (GTBase set_pairs.v).  As the source defines them
      (arXiv:2201.04062v2, main.tex l.86-94): graphs are finite and simple; a pure pair is a pair A, B of disjoint
      vertex sets that are complete or anticomplete; G contains H if some induced subgraph of G is isomorphic to H,
      and is H-free otherwise.
    Notes: encoded as the affirmative answer to the question (the corpus precedent for question rows); the authors
      write "We were unable to decide this" (l.204), so it is OPEN at the pin.  The quantifiers keep the source's
      order c, xi, H, eps, G (l.198-203), with c = 1 / k, xi = 1 / q and eps = 1 / m for positive integers:
      restricting to reciprocals loses nothing, since a smaller c only strengthens |B| >= eps |G|^(1-c) when
      |G| > 1, and a smaller xi or eps only weakens the property.  |A| >= |G| / m is |G| <= m |A|, and
      |B| >= |G|^(1 - 1/k) / m is |G|^(k-1) <= (m |B|)^k.  For H = K_0, K_1, K_2 or the complement of K_2, no G with
      |G| > 1 is both H-free and complement-H-free (every graph contains K_0, every graph with a vertex contains K_1,
      and every graph on two or more vertices contains K_2 or its complement), so those H hold vacuously, as in the
      source, whose H ranges over every graph; the grounding instance is H on three vertices with one edge, for which
      such G exist (K_2).  Possibility 1.6 asks for
      Theorem 1.4 (l.159-164, both sides of size eps |G|^(1-c) under congestion at most c / (9 + 15 c)) with one side
      linear, as Theorem 1.3 (l.118-123) gives under large branch-length; Theorem 1.5 (l.168-173) shows congestion
      must be small.  Pure pairs IX and X (the Mac's deposit) do not settle it.  The exponent k - 1 is an exact
      natural subtraction, guarded by 0 < k. *)
Definition pure_pairs_linear_side_small_congestion_statement : Prop :=
  forall k : nat, 0 < k -> exists q : nat, 0 < q /\
    forall H : sgraph, x280_congestion_at_most H q -> exists m : nat, 0 < m /\
      forall G : sgraph, 1 < #|G| -> induced_free G H -> induced_free G (compl H) ->
        exists A B : {set G},
          [/\ [disjoint A & B], complete_between A B || anticomplete A B,
              #|G| <= m * #|A| & #|G| ^ (k - 1) <= (m * #|B|) ^ k].

(** Corpus row: erdos:805
    Site: none
    Review: none
    English statement: (Erdos Problems #805, Erdos and Hajnal)
      For which functions g(n) with n > g(n) >= (log n)^2 is there a graph on n vertices in which every induced
      subgraph on g(n) vertices contains a clique of size >= log n and an independent set of size >= log n?  In
      particular, is there such a graph for g(n) = (log n)^3?
    Definitions: [cliqueb K] - K is a clique, and [stable I] - no edge inside I (coq-graph-theory).
    Notes: the specific question is encoded, in affirmative form, for every sufficiently large n (as erdos:1182 in
      X241 and erdos:1033 in X247): eventually a graph on n vertices exists in which every vertex set S with
      |S| >= (log_2 n)^3 contains a clique K and an independent set I with |K|, |I| >= log_2 n.  "For which g(n)" is
      not formalized.  The page gives no base or rounding; the row follows Alon, Bucic and Sudakov (arXiv:2004.04718v2,
      source.tex l.164: "This question remains open"; l.189: logarithms in base 2, "any set of at least m vertices
      contains a clique and an independent set of size at least r", m and r not necessarily integers).  With the
      coefficient fixed at 1 the base matters (Alon and Sudakov, arXiv:0706.4099v1 l.113-130, use natural logarithms
      and omit rounding), so it is stated, not assumed.  Both thresholds are exact: |K| >= log_2 n is n <= 2^|K|, and
      |S| >= (log_2 n)^3 holds iff every rational a / b < log_2 n (that is 2^a < n^b) has a^3 <= |S| b^3.  Sets of at
      least g(n) vertices are the page's subgraphs on g(n) vertices, the property being monotone.  "A graph on n
      vertices" is read for all large n, as the 2020 paper's Theorem 1.1 (l.167-169) states its bound for every n;
      reading it along infinitely many n would weaken it.  Erdos and Hajnal thought the answer is no (the page);
      Alon and Sudakov proved there is no such graph with g(n) = c (log n)^3 / log log n for some c > 0, and Alon,
      Bucic and Sudakov construct one with g(n) <= 2^(2^((log log n)^(1/2 + o(1)))).  Both bounds are asymptotic and
      hold in either base, so the question is OPEN at the pin in either reading. *)
Definition erdos_805_log_cubed_window_statement : Prop :=
  exists n0 : nat, forall n : nat, n0 <= n -> exists G : sgraph, #|G| = n /\
    forall S : {set G}, (forall a b : nat, 0 < b -> 2 ^ a < n ^ b -> a ^ 3 <= #|S| * b ^ 3) ->
      exists K I : {set G},
        [/\ K \subset S, I \subset S, cliqueb K, stable I & (n <= 2 ^ #|K|) && (n <= 2 ^ #|I|)].
