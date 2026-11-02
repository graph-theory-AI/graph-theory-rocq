(** * Extremal.conjectures.X282 -- v2 rows: the two-colour list Ramsey number of K_r, Erdos #79, k-connected graphs
      of prescribed Ramsey growth *)

From GTBase Require Import base.
From Extremal.conjectures Require Import X235 XE1.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local x282 vocabulary ************************************************* *)

(** [x282_ramsey_size_linear G]: G is Ramsey size-linear.  Erdos, Faudree, Rousseau and Schelp, as Wigderson states it
    (arXiv:2409.05931v2, revised.tex l.62): r(G, H) <= C_G e(H) for every graph H with no isolated vertices, where
    C_G > 0 depends only on G; r(G, H) is the least N such that every two-colouring of E(K_N) has a copy of G in the
    first colour or of H in the second (l.60), here [xe1_graph_ramsey_number G H R] (Extremal.conjectures.XE1); "no
    isolated vertices" is [min_degree_at_least H 1] (GTBase base.v).  A natural C is no loss (take the ceiling of
    C_G).  The graph H with no vertex has no isolated vertex and no edge; its Ramsey number is 0
    (it is a copy in every host, of order 0 included), so it adds no condition, as under the convention that H is
    nonempty. *)
Definition x282_ramsey_size_linear (G : sgraph) : Prop :=
  exists C : nat, forall (H : sgraph) (R : nat),
    min_degree_at_least H 1 -> xe1_graph_ramsey_number G H R -> R <= C * #|E(H)|.

(** ** X282 statements ******************************************************* *)

(** Corpus row: arxiv:1902.07018#01
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/1902.07018__01/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/1902.07018__01.json
    English statement: (Alon, Bucic, Kalvari, Kuperwasser and Szabo, "List Ramsey numbers", arXiv:1902.07018v2, the
      open question on cliques)
      For every r >= 4, the two-colour list Ramsey number of K_r equals its two-colour Ramsey number:
      R_l(K_r, 2) = R(K_r, 2).  Since R_l(K_r, 2) <= R(K_r, 2) always holds, this says: if some two-colouring of the
      edges of K_n has no monochromatic K_r, then for every assignment of two-element lists of colours to the edges
      of K_n, some colouring of each edge from its own list has no monochromatic K_r.
    Definitions: [lr_nat_valid_lists 2 L] - L gives each edge of K_n the same duplicate-free list of two natural
      colours in both orientations; [lr_nat_admissible L phi] - phi is a symmetric colouring of the edges choosing
      from the lists; [lr_color_graph phi c] - the graph on the vertices of K_n of the edges of colour c
      (Extremal.conjectures.X235); [has_subgraph G ('K_r)] - G contains a copy of K_r (GTBase common.v).  As the
      source defines them (source.tex l.197-205, l.245-249, l.265-274): colours are natural numbers; an L-colouring
      picks each colour from its list; a k-colouring is the L-colouring with every list equal to [k]; R(G, k) is the
      least n such that every k-colouring of E(K_n) has a monochromatic copy of G; R_l(G, k) is the least n such
      that SOME assignment of k-element lists to E(K_n) makes EVERY L-colouring contain one.
    Notes: encoded as the affirmative answer (the corpus precedent for question rows): "for r > 3 we cannot even
      decide the equality of the two Ramsey numbers of K_r when k = 2" (l.417-419), after R_l(K_3, 2) = 6 = R(K_3, 2)
      (l.417), hence the guard 3 < r.  R_l(G, k) <= R(G, k) (l.280) is the case of the constant lists [k]; only the
      open half R(K_r, 2) <= R_l(K_r, 2) is stated, through the orders below the thresholds: an order n with a
      2-colouring (lists {1, 2}) avoiding a monochromatic K_r, that is n < R(K_r, 2), has for every valid 2-list
      assignment an avoiding L-colouring, that is n < R_l(K_r, 2).  Over every n this is exactly the equality, and
      no Ramsey number is named.  A monochromatic copy of K_r is a copy of K_r in one colour class.  Only the edges of
      K_n carry lists; the diagonal values of L and phi play no role.  Literature status: OPEN at the pin (the pinned
      review found no later decision, and the Mac's bounded search of the deposit found none before the pin).  The
      sibling row arxiv:1902.07018#00 is the star question of l.296-356 (Chromatic X219). *)
Definition list_ramsey_two_colour_clique_equality_statement : Prop :=
  forall r n : nat, 3 < r ->
    (exists phi : 'I_n -> 'I_n -> nat,
       lr_nat_admissible (fun _ _ => [:: 1; 2]) phi /\
       forall c : nat, ~ has_subgraph (lr_color_graph phi c) ('K_r)) ->
    forall L : 'I_n -> 'I_n -> seq nat, lr_nat_valid_lists 2 L ->
      exists phi : 'I_n -> 'I_n -> nat,
        lr_nat_admissible L phi /\ forall c : nat, ~ has_subgraph (lr_color_graph phi c) ('K_r).

(** Corpus row: erdos:79
    Site: none
    Review: none
    English statement: (Erdos Problems #79; Erdos, Faudree, Rousseau and Schelp)
      There are infinitely many graphs G which are not Ramsey size-linear, but every proper subgraph of which is
      Ramsey size-linear, where G is Ramsey size-linear if r(G, H) <= C m for some constant C depending only on G
      and all graphs H with m edges and no isolated vertices.
    Definitions: [x282_ramsey_size_linear G] - G is Ramsey size-linear (this file); [has_subgraph G H] - G
      contains a copy of H (GTBase common.v); [E(H)] - the edge set of H (GTBase common.v).
    Notes: the pinned statement is the erdosproblems.com text ("Are there infinitely many graphs G which are not
      Ramsey size linear but such that all of its subgraphs are?"); encoded as the affirmative answer.  "All of its
      subgraphs" are the proper subgraphs, as Wigderson's theorem states it (arXiv:2409.05931v2, revised.tex
      l.65-66: every proper subgraph G' of G).  A copy H of a subgraph of G has |H| <= |G| and |E(H)| <= |E(G)|, with
      both equal exactly when H is G itself, so |H| + |E(H)| < |G| + |E(G)| is properness.  "Infinitely many" is read
      as unbounded order: there are finitely many graphs on each number of vertices, so an infinite family has members
      of every large order, and graphs of distinct orders are distinct.  Literature status: PROVED before the pin by
      Wigderson (arXiv:2409.05931, v1 2024-09-09, v2 2025-05-05; l.65-66 and the proof l.84-90), non-constructively;
      K_4 is the only explicit example (erdosproblems.com #79, "proved" in the teorth/erdosproblems mirror 10fb9c15).
      [EFRS93] itself was not obtained. *)
Definition erdos_79_minimal_non_ramsey_size_linear_statement : Prop :=
  forall N : nat, exists G : sgraph,
    [/\ N <= #|G|, ~ x282_ramsey_size_linear G &
        forall H : sgraph, has_subgraph G H -> #|H| + #|E(H)| < #|G| + #|E(G)| ->
          x282_ramsey_size_linear H].

(** Corpus row: studies:std_pavez_sign_piga_sanhueza_matamala_conjecture_on
    Site: none
    Review: none
    English statement: (Pavez-Signe, Piga and Sanhueza-Matamala, "Ramsey numbers with prescribed rate of growth",
      arXiv:2209.05455v3, Conjecture 16)
      For every k >= 2 and every function f : N -> N with n <= f(n) <= R(K_n), there is a sequence of graphs (G_n)
      with |V(G_n)| = n such that R(G_n) = Theta(f(n)) and G_n is k-connected for all n sufficiently large.
    Definitions: [xe1_diagonal_ramsey_number G R] - R = R(G), the least N such that every graph on N vertices or its
      complement contains G (Extremal.conjectures.XE1); [k_connected G k] - G has more than k vertices and stays
      connected after deleting any fewer than k vertices (GTBase base.v); ['K_n] - the complete graph on n vertices.
      As the source defines R (main.tex l.139-140): the least n such that every 2-colouring of E(K_n) contains a
      monochromatic copy of G.
    Notes: the pinned statement is the studies record (source arXiv:2311.01887v1, Ahme and Scott, main.tex l.38-40,
      quoting Conjecture 16); the original (2209.05455v3 main.tex l.486-489) asks k-connectivity only "for all n
      sufficiently large", read here with the Theta bounds from one threshold n0 on: a G_n below n0 is unconstrained
      (Theta is asymptotic; every R(G_n) and f(n) is positive for n >= 1, so finitely many orders do not matter), and
      no k-connected graph has n <= k vertices.  Theta(f(n)) is R(G_n) <= a f(n) and f(n) <= b R(G_n) for natural
      a and b.  The hypothesis is pointwise and f need not be monotone (the printed conjecture, not the abstract's
      non-decreasing f).  At n = 0 it forces f(0) = 0 (R(K_0) = 0), which no order n >= n0 uses (every n0
      exceeds k).  The conclusion asserts that R(G_n) exists.  Literature status: pinned open, but PROVED before the
      pin by Ahme and Scott (arXiv:2311.01887v1, 2023-11-03, Theorem 3, main.tex l.44-47, with a constant C_k
      independent of f, and f(n) <= R(G_n); the proof works at a fixed large n, l.106).  Lancelot's literature item
      lit22 records the status. *)
Definition k_connected_ramsey_growth_statement : Prop :=
  forall k : nat, 2 <= k -> forall f : nat -> nat,
    (forall n R : nat, xe1_diagonal_ramsey_number ('K_n) R -> n <= f n <= R) ->
    exists a b n0 : nat, forall n : nat, n0 <= n ->
      exists G : sgraph,
        [/\ #|G| = n, k_connected G k &
            exists2 R : nat, xe1_diagonal_ramsey_number G R & (f n <= b * R) && (R <= a * f n)].
