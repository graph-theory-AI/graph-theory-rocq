(** * Extremal.conjectures.X255 -- wave X255: the ratio R(3,3,n) / R(3,n), size Ramsey numbers of paths and cycles, monochromatic K_t tilings (2026-10-28)

    A three-row wave under the prospective contract of meta/faithfulness_policy.json.  Rows: erdos:553 (R(3,3,n) / R(3,n)
    -> oo), erdos:720 (the size Ramsey numbers of paths and cycles, as asked) and erdos:1015 (the leftover f(t) of a
    tiling of a two-coloured K_n by monochromatic K_t, as asked).  Shared vocabulary is reused: two-colour graph Ramsey
    and size Ramsey numbers are Extremal.conjectures.XE1's [xe1_graph_ramsey_number H K R] and
    [xe1_size_ramsey_number H K m]; [mono_copy F col c] is Extremal.foundations.edge_colourings'; GTBase supplies
    'K_n, [ordinal_path] and [cycle_graph].  Two local notions have no shared counterpart: the three-colour asymmetric
    Ramsey number R(3,3,n) (XE1's is two-colour and X195's symmetric) and the tiling leftover f(t).  All three rows have
    pinned status "solved"; literature lines are dated against the corpus pin (graph-conjectures b72c5857,
    2026-09-23).  The sources are the Mac's deposit coordination/sources/x255-source-mac-20261028 (text line numbers
    below).  The grounding certificates are in grounding_X255.v. *)

From Extremal.foundations Require Import edge_colourings.
From Extremal.conjectures Require Import XE1.
From GTBase Require Import base common path_graphs.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local x255 vocabulary ************************************************* *)

(** K_m ARROWS (K_3, K_3, K_n): every colouring of the edges of K_m with the three colours 0, 1, 2 has a monochromatic
    triangle in colour 0 or in colour 1, or a monochromatic K_n in colour 2 (the asymmetric multicolour Ramsey
    property, Alon-Rodl-arodl4.txt l.27-29). *)
Definition x255_arrows_33n (n m : nat) : Prop :=
  forall col : {set 'K_m} -> 'I_3,
    [\/ mono_copy 'K_3 col (@Ordinal 3 0 isT), mono_copy 'K_3 col (@Ordinal 3 1 isT)
      | mono_copy 'K_n col (@Ordinal 3 2 isT)].

(** R = R(3,3,n): the smallest m with the arrow property above. *)
Definition x255_ramsey_33n (n R : nat) : Prop :=
  x255_arrows_33n n R /\ forall R' : nat, x255_arrows_33n n R' -> R <= R'.

(** r vertices may remain over when tiling a large two-coloured K_n by monochromatic K_t: for some n0, every colouring
    of the pairs of 'I_n with n >= n0 admits pairwise disjoint t-sets, each monochromatic in a colour of its own (all
    its pairs have one colour), covering all but at most r vertices. *)
Definition x255_mono_tiling_leftover (t r : nat) : Prop :=
  exists n0 : nat, forall (n : nat) (col : {set 'I_n} -> bool), n0 <= n ->
    exists P : {set {set 'I_n}},
      [/\ (forall S : {set 'I_n}, S \in P -> #|S| = t /\
             exists b : bool, forall x y : 'I_n, x \in S -> y \in S -> x != y -> col [set x; y] = b),
          (forall S S' : {set 'I_n}, S \in P -> S' \in P -> S != S' -> [disjoint S & S']) &
          n <= #|cover P| + r].

(** f = f(t): the smallest such r. *)
Definition x255_mono_tiling_number (t f : nat) : Prop :=
  x255_mono_tiling_leftover t f /\ forall r : nat, x255_mono_tiling_leftover t r -> f <= r.

(** ** X255 statements ******************************************************* *)

(** Corpus row: erdos:553
    Site: none
    Review: none
    English statement: (Erdos Problems #553, Erdos and Sos)
      Let R(3,3,n) denote the smallest integer m such that if we 3-colour the edges of K_m then there is either a
      monochromatic triangle in one of the first two colours or a monochromatic K_n in the third colour.  Define R(3,n)
      similarly but with two colours.  Show that R(3,3,n)/R(3,n) -> oo as n -> oo.
    Definitions: [x255_ramsey_33n n R] - R = R(3,3,n) (this file); [xe1_graph_ramsey_number 'K_3 'K_n R] - R = R(3,n),
      the least R such that every graph on R vertices contains a triangle or its complement contains K_n
      (Extremal.conjectures.XE1); [mono_copy F col c] - an injective adjacency-preserving map of F into the host whose
      image edges all have colour c (Extremal.foundations.edge_colourings).
    Notes: the ratio tends to infinity: for every C, eventually C R(3,n) <= R(3,3,n) (a natural C suffices).  Literature
      status: proved before the pin (pinned status solved, "PROVED ... in the affirmative").  Alon and Rodl, Sharp
      bounds for some multicolor Ramsey numbers, Combinatorica (2005) 125-141 (author version, Alon-Rodl-arodl4.txt):
      Conjecture 1.1 (Erdos and Sos, l.53-57) is this row, and "we show that r(K3, K3, Km) = Theta(m^3 poly log m), thus
      solving, in a strong form, the above mentioned conjecture" (l.60-61; abstract l.18-19).  R(3,n) =
      Theta(n^2 / log n) is cited from Alon and Rodl's text (l.47-48: Kim with Ajtai, Komlos and Szemeredi), and the
      page cites Shearer [Sh83] for R(3,n) << n^2 / log n (erdos-553.txt l.169); Kim, AKS and Shearer were not read. *)
Definition multicolour_triangle_clique_ramsey_ratio_statement : Prop :=
  forall C : nat, exists N : nat, forall n a b : nat, N <= n ->
    x255_ramsey_33n n a -> xe1_graph_ramsey_number 'K_3 'K_n b -> C * b <= a.

(** Corpus row: erdos:720
    Site: none
    Review: none
    English statement: (Erdos Problems #720, Erdos, Faudree, Rousseau and Schelp)
      Let R^(G) denote the size Ramsey number, the minimal number of edges m such that there is a graph H with m edges
      such that in any 2-colouring of the edges of H there is a monochromatic copy of G.  Is it true that, if P_n is
      the path of length n, then R^(P_n)/n -> oo and R^(P_n)/n^2 -> 0?  Is it true that, if C_n is the cycle with n
      edges, then R^(C_n) = o(n^2)?
    Definitions: [xe1_size_ramsey_number H K m] - m = R^(H, K), the least edge count of a graph whose every red/blue
      edge colouring has a red H or a blue K (Extremal.conjectures.XE1; here H = K); [ordinal_path n.+1] - the path
      0 - 1 - ... - n on n + 1 vertices, so with n edges: the path of length n (GTBase.path_graphs); [cycle_graph n] -
      i adjacent to i + 1 mod n on 'I_n (GTBase.base): the cycle with n edges for n >= 3, while cycle_graph 0 is empty,
      cycle_graph 1 one vertex and cycle_graph 2 one edge, below the asymptotic range of the third clause.
    Notes: the three asked clauses are encoded as stated: R^(P_n) / n -> oo (for every M, eventually M n <= R^(P_n)),
      R^(P_n) / n^2 -> 0 and R^(C_n) / n^2 -> 0 (for every q >= 1, eventually q R^ <= n^2).  The row is FALSE at the
      pin: the first clause is refuted.  The page: "Answered by Beck [Be83b], who proved that in fact R^(P_n) << n and
      R^(C_n) << n" (erdos-720.txt l.174).  Beck, On size Ramsey number of paths, trees and circuits. II (in
      Mathematics of Ramsey Theory, PDF p.48, printed p.34, read from the page scan) restates his 1983 bound (1):
      R^(P_n) < 900 n for every sufficiently large n, "where P_n denotes the path of length n" (Part I, J. Graph Theory
      (1983) 115-129, was not obtainable).  The second clause follows from that bound and the third from Javadi,
      Khoeini, Omidi and Pokrovskiy, On the size-Ramsey number of cycles (accepted manuscript,
      Javadi-et-al-cycles-2019.txt): "for sufficiently large n we have R^_2(C_n) <= 10^5 x cn" (abstract l.25-26), with
      Haxell, Kohayakawa and Luczak's linear bound cited at l.19-20 (not read); that paper's P_n has n vertices
      (l.68-69), Beck's and the row's n edges.  The pinned prize "PROVED ... in the affirmative" disagrees with the
      refuted first clause (CORPUS_FEEDBACK). *)
Definition path_cycle_size_ramsey_growth_statement : Prop :=
  [/\ (forall M : nat, exists N : nat, forall n m : nat, N <= n ->
         xe1_size_ramsey_number (ordinal_path n.+1) (ordinal_path n.+1) m -> M * n <= m),
      (forall q : nat, 1 <= q -> exists N : nat, forall n m : nat, N <= n ->
         xe1_size_ramsey_number (ordinal_path n.+1) (ordinal_path n.+1) m -> q * m <= n ^ 2) &
      (forall q : nat, 1 <= q -> exists N : nat, forall n m : nat, N <= n ->
         xe1_size_ramsey_number (cycle_graph n) (cycle_graph n) m -> q * m <= n ^ 2)].

(** Corpus row: erdos:1015
    Site: none
    Review: none
    English statement: (Erdos Problems #1015, Erdos; a question of Moon)
      Let f(t) be minimal such that, in any two-colouring of the edges of K_n, the edges can be partitioned into vertex
      disjoint monochromatic copies of K_t (not necessarily the same colour) with at most f(t) vertices remaining.
      Estimate f(t).  In particular, is it true that f(t)^{1/t} -> 1?  Is it true that f(t) << t?
    Definitions: [x255_mono_tiling_number t f] - f = f(t), the least r such that for all large n every two-colouring
      of the pairs of K_n has vertex-disjoint monochromatic t-sets, each in its own colour, leaving at most r
      vertices uncovered (this file).
    Notes: the two named questions are encoded as stated; "Estimate f(t)" is not formalised.  f(t)^{1/t} -> 1 is its
      upper half, for every q >= 1 eventually f(t) <= (1 + 1/q)^t, cleared of denominators: the lower half holds
      automatically, as f(t) >= 1 for t >= 2 (grounding_X255's g255_tiling_pos: n = n0 t + 1 is not a multiple of t).
      f(t) << t is f(t) <= C t for all t.  "The edges can be partitioned" is read as the vertex tiling the rest of
      the sentence describes, as in the sources: Erdos, Some unsolved problems in graph theory and combinatorial
      analysis (1971), p.100, item 9 (read from the page scan; Er71.txt l.139-146 is its OCR): Moon's triangles,
      "different triangles can have different colours", and f(l) counts the vertex-disjoint monochromatic K_l's missing
      from [n/l], "Ramsey's theorem implies f(l) < 4^l but it seems certain that f(l)^{1/l} -> 1 and perhaps
      f(l) < c l, or f(l) is bounded"; this file counts leftover VERTICES, as the pinned text (n minus t times the
      number of tiles, so t times Erdos's count plus a remainder below t; both answers are the same under either
      count), and Burr, Erdos and Spencer, Ramsey theorems for multiple copies of graphs, Trans. AMS 209 (1975) 87-99,
      section 5, p.94 (read from the page scan): f(n, k) is the least number of vertices left over, "the K_k may be
      different colors.  We are interested in k fixed, n large."  f(t) is taken over all large n, as the page reads the
      question ("Presumably Erdos intended to only ask this question for n sufficiently large depending on t",
      erdos-1015.txt l.173): over every n both questions fail trivially, since n = R(t,t) - 1 with a colouring without
      monochromatic K_t leaves every vertex over (a remark of the Mac's deposit, SOURCE.md).  The row is FALSE at the pin
      (pinned status solved, "resolved in some other way"): BES Theorem 6 (p.94), for fixed k and all large n,
      f(n, k) = r(k, k-1) - 1 + rem(n - r(k, k-1) + 1, k), and its construction leaves r(k, k-1) - 1 vertices over for
      every n >= r(k, k-1) - 1, so f(t) >= r(t, t-1) - 1 >= R(t-1, t-1) - 1 >= 2^((t-1)/2) - 1 (Erdos's lower bound,
      as Javadi-et-al-cycles-2019.txt l.55-56 states it): f(t)^{1/t} does not tend to 1 and f(t) << t fails.  The
      page's formula R(t, t-1) + x(t, n) (l.175) drops the "- 1" of Theorem 6 (CORPUS_FEEDBACK). *)
Definition monochromatic_clique_tiling_leftover_statement : Prop :=
  (forall q : nat, 1 <= q -> exists t0 : nat, forall t f : nat, t0 <= t ->
     x255_mono_tiling_number t f -> q ^ t * f <= (q + 1) ^ t) /\
  (exists C : nat, forall t f : nat, x255_mono_tiling_number t f -> f <= C * t).
