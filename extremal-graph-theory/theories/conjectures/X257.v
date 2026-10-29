(** * Extremal.conjectures.X257 -- wave X257: graphs whose every edge lies in a triangle, the edge thresholds e(n,r) and the forced book sizes f_c(n) (2026-10-29)

    A two-row wave under the prospective contract of meta/faithfulness_policy.json.  Rows: erdos:600 (the increments
    and ratios of the thresholds e(n,r), as asked) and erdos:80 (a polynomial lower bound for the forced book size
    f_c(n), as asked).  Both are item 11 of Erdos, Some problems on finite and infinite graphs, Contemp. Math. 65 (1987)
    223-228, a problem of Erdos and Rothschild.  Shared vocabulary is reused: "an edge in at least r triangles" is read
    through Extremal.conjectures.X230's [x230_book_at_most G b] (every edge has at most b common neighbours) and the
    edge count is GTBase's [edge_count].  Two local notions have no shared counterpart: the forcing threshold e(n,r)
    and the forced book size f_c(n) at c = 1/p.  Both rows have pinned status "open"; literature lines are dated
    against the corpus pin (graph-conjectures b72c5857, 2026-09-23).  The sources are the Mac's deposit
    coordination/sources/x257-source-mac-20261029 (text line numbers below).  The grounding certificates are in
    grounding_X257.v. *)

From Extremal.conjectures Require Import X230.
From GTBase Require Import base common.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local x257 vocabulary ************************************************* *)

(** m edges force an edge in r triangles on n vertices: every graph on n vertices with at least m edges, each edge in a
    triangle (its ends have a common neighbour), has no bound b below r on the number of triangles at an edge (X230's
    [x230_book_at_most G b]); for r >= 1 this says that some edge lies in at least r triangles. *)
Definition x257_triangle_forcing (n r m : nat) : Prop :=
  forall G : sgraph, #|G| = n -> m <= edge_count G ->
    (forall x y : G, x -- y -> 0 < #|[set z | x -- z & y -- z]|) ->
    forall b : nat, x230_book_at_most G b -> r <= b.

(** e = e(n,r): the least such m. *)
Definition x257_triangle_forcing_number (n r e : nat) : Prop :=
  x257_triangle_forcing n r e /\ forall m : nat, x257_triangle_forcing n r m -> e <= m.

(** Every graph on n vertices with at least n^2 / p edges (c = 1/p), each edge in a triangle, contains a book of size m:
    an edge in at least m triangles, read as for [x257_triangle_forcing]. *)
Definition x257_book_forced (n p m : nat) : Prop :=
  forall G : sgraph, #|G| = n -> n ^ 2 <= p * edge_count G ->
    (forall x y : G, x -- y -> 0 < #|[set z | x -- z & y -- z]|) ->
    forall b : nat, x230_book_at_most G b -> m <= b.

(** f = f_c(n) with c = 1/p: the largest such m. *)
Definition x257_book_number (n p f : nat) : Prop :=
  x257_book_forced n p f /\ forall m : nat, x257_book_forced n p m -> m <= f.

(** ** X257 statements ******************************************************* *)

(** Corpus row: erdos:600
    Site: none
    Review: none
    English statement: (Erdos Problems #600, Erdos and Rothschild)
      Let e(n,r) be minimal such that every graph on n vertices with at least e(n,r) edges, each edge contained in at
      least one triangle, must have an edge contained in at least r triangles.  Let r >= 2.  Is it true that
      e(n,r+1) - e(n,r) -> oo as n -> oo?  Is it true that e(n,r+1) / e(n,r) -> 1 as n -> oo?
    Definitions: [x257_triangle_forcing_number n r e] - e = e(n,r), the least m such that every graph on n vertices
      with at least m edges, each in a triangle, has an edge in at least r triangles (this file);
      [x230_book_at_most G b] - every edge of G has at most b common neighbours, i.e. lies in at most b triangles
      (Extremal.conjectures.X230); [edge_count G] - the number of edges (GTBase.common).
    Notes: the two asked clauses are encoded in their affirmative form, as the corpus's open questions and as Erdos
      expects them ("Probably e(n;r+1) - e(n;r) -> oo.  But perhaps e(n;r+1)/e(n;r) -> 1", Er87 p.227), for every
      r >= 2, the pinned range (Er87 states none): e(n,r+1) - e(n,r) -> oo is "for every M, eventually
      e(n,r) + M <= e(n,r+1)", and e(n,r+1) / e(n,r) -> 1 is its upper half, "for every q >= 1, eventually
      q e(n,r+1) <= (q + 1) e(n,r)"; the lower half holds automatically, as e(n,r) <= e(n,r+1) (grounding_X257's
      g257_number_mono).  e(n,r) is a threshold, the least m in the pinned "at least m edges" (a property monotone in
      m), and it exists for every n and r: C(n,2) + 1 edges force everything vacuously (g257_forcing_vacuous), so the
      relation is never empty.  Erdos, Some problems on finite and infinite graphs, Contemp. Math. 65 (1987),
      item 11, pp.226-227 (read from the page scans Er87-page4.png and Er87-page5.png; Er87.txt l.214-251 is their
      OCR), defines e(n,r) as the smallest integer such that every G(n;e(n,r)), a graph with n vertices and exactly
      e(n,r) edges, each edge in a triangle, has an edge in at least r triangles.  The two readings differ: taken
      literally, the exact-edge property holds vacuously at one edge (a graph with exactly one edge has it in no
      triangle, g257_exact_one), so its least value would be at most 1 for all n and r, against Er87's own bound
      c n r_3(n) < e(n;2) (p.227); the pinned threshold at m is the exact-edge property at every count e >= m
      (g257_forcing_exact).  The pinned text is encoded.  Literature (no answer to either clause): Ruzsa and
      Szemeredi, c n r_3(n) < e(n;2) = o(n^2), and e(n;r) = o(n^2) for every r (Er87 p.227; the page cites [RuSz78],
      erdos-600.txt l.30-32; not read). *)
Definition triangle_covered_book_threshold_increments_statement : Prop :=
  forall r : nat, 2 <= r ->
    (forall M : nat, exists N : nat, forall n a b : nat, N <= n ->
       x257_triangle_forcing_number n r a -> x257_triangle_forcing_number n r.+1 b -> M + a <= b) /\
    (forall q : nat, 1 <= q -> exists N : nat, forall n a b : nat, N <= n ->
       x257_triangle_forcing_number n r a -> x257_triangle_forcing_number n r.+1 b -> q * b <= (q + 1) * a).

(** Corpus row: erdos:80
    Site: none
    Review: none
    English statement: (Erdos Problems #80, Erdos and Rothschild)
      Let c > 0 and let f_c(n) be the maximal m such that every graph G with n vertices and at least c n^2 edges, where
      each edge is contained in at least one triangle, must contain a book of size m, that is, an edge shared by at
      least m different triangles.  Estimate f_c(n).  In particular, is it true that f_c(n) > n^eps for some eps > 0?
      Or f_c(n) >> log n?
    Definitions: [x257_book_number n p f] - f = f_c(n) for c = 1/p, the largest m such that every graph on n vertices
      with at least n^2 / p edges, each in a triangle, has an edge in at least m triangles (this file);
      [x230_book_at_most G b] - every edge of G has at most b common neighbours, i.e. lies in at most b triangles
      (Extremal.conjectures.X230); [edge_count G] - the number of edges (GTBase.common).
    Notes: the main question is encoded as stated: for every c > 0 there are eps > 0 and N with f_c(n) > n^eps for
      every n >= N.  eps may depend on c, the order of Fox and Loh's abstract: "Erdos asked in 1987 to determine
      whether for every c > 0 there is eps > 0 such that h(n,c) > n^eps for all sufficiently large n"
      (1106.0290v2-src/source.tex l.56-58); their introduction states the uniform order (l.106-108), and both orders
      are refuted.  eps = 1/q (every eps > 0 exceeds some 1/q), so f_c(n) > n^eps is n < f_c(n)^q.  c = 1/p covers every
      real c > 0: f_c(n) only grows with c (a larger c admits fewer graphs, so more m are forced), so the clause for c
      follows from the clause for any 1/p <= c, and the values 1/p are among the c.  The fallback "Or f_c(n) >> log n"
      (Er87: "or at least f(n;c) > log n") is named here and not encoded, the convention for a main question with a
      fallback; the main form implies it, with log n read as n <= 2^(C f_c(n)) (grounding_X257's g257_poly_log), and
      it is open at the pin, which is why the row stays open.  "Estimate f_c(n)" is not formalised.  Small n: when no
      graph on n vertices meets the hypotheses (n = 1 or 2, and every n >= 1 when p <= 2, as C(n,2) < n^2 / 2), every
      m is forced, f_c(n) does not exist and the relation is empty (g257_book_empty_1 at n = 1); the clause is
      asymptotic, so this is vacuous below N.  Erdos, Some problems on finite and infinite graphs, Contemp. Math. 65
      (1987), item 11, p.226 (page scan Er87-page4.png) defines f(n;c) over graphs G(n;e) with e >= c n^2, every edge in
      a triangle, and prints "smallest" where the largest such integer is meant (taken literally it is trivial); Fox
      and Loh's h(n,c) is "the largest integer" (l.78-81).  The row is FALSE at the pin: Fox and Loh, On a problem of
      Erdos and Rothschild on edges in triangles, arXiv:1106.0290v2 (Combinatorica (2012) 619-628), Theorem 1.1
      (l.116-123): for all sufficiently large n there are n-vertex graphs with (n^2 / 4)(1 - e^{-(log n)^{1/6}}) edges,
      every edge in a triangle and no edge in more than n^{14 / log log n} triangles.  At c = 1/5 they qualify for
      large n, so f_{1/5}(n) <= n^{14 / log log n} and n < f_{1/5}(n)^q fails for every q: "This gives a negative
      answer to the question of Erdos" (l.59-60).  The page agrees, "disproving the first conjecture of Erdos"
      (erdos-80.txt l.39-41); Fox and Loh's lower bound is exponential in log* n (l.159-166). *)
Definition triangle_covered_dense_book_polynomial_statement : Prop :=
  forall p : nat, 1 <= p -> exists q N : nat, 1 <= q /\
    forall n f : nat, N <= n -> x257_book_number n p f -> n < f ^ q.
