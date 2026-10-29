(** * Extremal.conjectures.X259 -- wave X259: anti-Ramsey numbers of cycles and paths, and the strong chromatic number of odd cycles (2026-10-29)

    A two-row wave under the prospective contract of meta/faithfulness_policy.json.  Rows: erdos:1105 (the anti-Ramsey
    numbers AR(n, C_k) and AR(n, P_k), both asked clauses) and erdos:809 (the strong chromatic number
    chi_S(n, n^2/4 + 1, C_(2k+1)), as asked).  No shared rainbow notion exists: Extremal.foundations.edge_colourings
    has monochromatic copies, colour classes and proper colourings, and the X3, X10, X14, X24 and X83 rainbow helpers
    concern paths, cycles or holes given as vertex sequences.  The wave therefore defines one local family on the
    shape of edge_colourings' [mono_copy]: a rainbow copy, the anti-Ramsey number and the strong chromatic number.
    GTBase's [cycle_graph k] (the cycle on 'I_k) and [ordinal_path k] (the path on 'I_k) are C_k and P_k, and
    [edge_count] counts edges.  Literature lines are dated against the corpus pin (graph-conjectures b72c5857,
    2026-09-23).  The sources are the Mac's deposit coordination/sources/x259-source-mac-20261029 (text line numbers
    below).  The grounding certificates are in grounding_X259.v. *)


From GTBase Require Import base common path_graphs.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local x259 vocabulary ************************************************* *)

(** F has a rainbow copy in the edge colouring [col] of the host: an injective adjacency-preserving map (a
    not-necessarily-induced copy, as [mono_copy]) whose image edges get pairwise distinct colours.  As in
    edge_colourings, a colouring is a total map on vertex sets of which only the values on edges are read. *)
Definition x259_rainbow_copy (Host F : sgraph) (C : eqType) (col : {set Host} -> C) : Prop :=
  exists emb : F -> Host,
    [/\ injective emb, forall x y : F, x -- y -> emb x -- emb y &
        forall x y u v : F, x -- y -> u -- v -> [set x; y] != [set u; v] ->
          col [set emb x; emb y] != col [set emb u; emb v]].

(** Some colouring of the edges of K_n uses exactly r colours (counted on the edges) and has no rainbow copy of F. *)
Definition x259_rainbow_free_colours (n : nat) (F : sgraph) (r : nat) : Prop :=
  exists col : {set 'K_n} -> nat,
    size (undup [seq col e | e <- enum E('K_n)]) = r /\ ~ x259_rainbow_copy F col.

(** a = AR(n, F): the largest such r. *)
Definition x259_anti_ramsey_number (n : nat) (F : sgraph) (a : nat) : Prop :=
  x259_rainbow_free_colours n F a /\ forall r : nat, x259_rainbow_free_colours n F r -> r <= a.

(** Some graph with n vertices and e edges has a colouring of its edges with (at most) r colours, a map into 'I_r, in
    which every copy of F is rainbow. *)
Definition x259_rainbow_forcing_colouring (n e : nat) (F : sgraph) (r : nat) : Prop :=
  exists H : sgraph, [/\ #|H| = n, edge_count H = e &
    exists col : {set H} -> 'I_r,
      forall emb : F -> H, injective emb -> (forall x y : F, x -- y -> emb x -- emb y) ->
        forall x y u v : F, x -- y -> u -- v -> [set x; y] != [set u; v] ->
          col [set emb x; emb y] != col [set emb u; emb v]].

(** s = chi_S(n, e, F): the least such r. *)
Definition x259_strong_chromatic_number (n e : nat) (F : sgraph) (s : nat) : Prop :=
  x259_rainbow_forcing_colouring n e F s /\ forall r : nat, x259_rainbow_forcing_colouring n e F r -> s <= r.

(** ** X259 statements ******************************************************* *)


(** Corpus row: erdos:1105
    Site: none
    Review: none
    English statement: (Erdos Problems #1105, Erdos, Simonovits and Sos)
      The anti-Ramsey number AR(n,G) is the maximum possible number of colours in which the edges of K_n can be
      coloured without creating a rainbow copy of G (i.e. one in which all edges have different colours).  Let C_k be
      the cycle on k vertices.  Is it true that AR(n,C_k) = ((k-2)/2 + 1/(k-1)) n + O(1)?  Let P_k be the path on k
      vertices and l = floor((k-1)/2).  If n >= k >= 5 then is AR(n,P_k) equal to
      max(binom(k-2,2) + 1, binom(l-1,2) + (l-1)(n-l+1) + eps) where eps = 1 if k is odd and eps = 2 otherwise?
    Definitions: [x259_anti_ramsey_number n F a] - a = AR(n,F), the largest number of colours, counted on the edges, of
      an edge colouring of K_n with no rainbow copy of F (this file); [x259_rainbow_copy F col] - an injective
      adjacency-preserving image of F whose edges have pairwise distinct colours (this file); [cycle_graph k] - C_k,
      the cycle on 'I_k (GTBase.base); [ordinal_path k] - P_k, the path on 'I_k, with k vertices (GTBase.path_graphs).
    Notes: both asked clauses are encoded, in their affirmative form, as both are proved.  The cycle clause, for each
      k >= 3 (C and N may depend on k: k is fixed in O(1)), multiplied by 2(k-1):
      |2(k-1) AR(n,C_k) - ((k-2)(k-1) + 2) n| <= C for n >= N.  The path clause is the printed maximum, with l the
      natural division (k-1) %/ 2.  Conventions as the sources: AR(n,G) is the maximum number of colours with no
      rainbow (totally multicoloured, TMC) copy, and P_k and C_k have k vertices (Erdos, Simonovits and Sos, Anti-Ramsey
      theorems (1975), p.633, ESS75.txt l.28 and l.45-49; Yuan, source.tex l.54).  A copy is a subgraph, not
      necessarily induced.  Cycles: Montellano-Ballesteros and Neumann-Lara, An anti-Ramsey theorem on cycles, Graphs
      Combin. (2005) 343-354, give an exact formula, "which implies in particular" the asked asymptotic
      (erdos-1105.txt l.43-44).  Their abstract (MoNe05.publisher.txt l.37-65; only the publisher preview was
      obtained, and its displayed formula is missing from the text) determines h(n,p), the least number of colours
      forcing a rainbow C_p, for n >= p >= 3, with the conjectured equality of Erdos, Simonovits and Sos as a corollary
      (Conjecture 1, ESS75.txt l.146-148).  AR(n,C_p) = h(n,p) - 1 (merging two colour classes creates no rainbow
      copy), so the one-colour difference is absorbed by C.  ESS75 proves k = 3, AR(n,C_3) = n - 1
      (erdos-1105.txt l.34-35).  Paths: Yuan, The anti-Ramsey number for paths, arXiv:2102.00807v3, Theorem 1
      (source.tex l.69-75), proves the printed formula for every n >= k >= 5; the page reports it as announced
      (l.39-40).  Simonovits and Sos, On restricted colourings of K_n, Combinatorica (1984) 101-110, Theorem B
      (SiSo84.txt l.77), had proved it for n >= c k^2 (erdos-1105.txt l.37-38).  Smallest case n = k = 5:
      max(4, 5) = 5.  The subtractions k - 1, k - 2, (k - 1) %/ 2 - 1 and n - (k - 1) %/ 2
      are not truncated: 3 <= k guards the cycle clause and 5 <= k <= n the path clause. *)
Definition anti_ramsey_cycles_paths_statement : Prop :=
  (forall k : nat, 3 <= k -> exists C N : nat, forall n a : nat, N <= n ->
     x259_anti_ramsey_number n (cycle_graph k) a ->
     2 * (k - 1) * a <= ((k - 2) * (k - 1) + 2) * n + C /\
     ((k - 2) * (k - 1) + 2) * n <= 2 * (k - 1) * a + C) /\
  (forall n k a : nat, 5 <= k -> k <= n -> x259_anti_ramsey_number n (ordinal_path k) a ->
     a = maxn ('C(k - 2, 2) + 1)
              ('C((k - 1) %/ 2 - 1, 2) + ((k - 1) %/ 2 - 1) * (n - (k - 1) %/ 2 + 1) + (if odd k then 1 else 2))).

(** Corpus row: erdos:809
    Site: none
    Review: none
    English statement: (Erdos Problems #809, Burr, Erdos, Graham and Sos)
      Define the anti-Ramsey number chi_S(n,e,G) as the smallest r such that there is a graph with n vertices and e
      edges with an r-colouring of its edges in which every copy of G has entirely distinct edge colours.  Is it true
      that, for all k >= 3, chi_S(n, floor(n^2/4) + 1, C_(2k+1)) ~ n^2/8?
    Definitions: [x259_strong_chromatic_number n e F s] - s = chi_S(n,e,F), the least r such that some graph with n
      vertices and exactly e edges has an edge colouring into 'I_r in which every copy of F is rainbow (this file);
      [x259_rainbow_forcing_colouring n e F r] - some such graph and colouring exist for r (this file);
      [cycle_graph k] - C_k, the cycle on 'I_k (GTBase.base); [edge_count G] - the number of edges (GTBase.common).
    Notes: encoded as asked, in its affirmative form: for every k >= 3 and every q >= 1, eventually
      q/(q+1) <= 8 chi_S / n^2 <= (q+1)/q, cross-multiplied (no reals); floor(n^2/4) is n^2 %/ 4.  The definition is
      Burr, Erdos, Graham and Sos's: Maximal antiramsey graphs and the strong chromatic number, J. Graph Theory 13
      (1989) 263-282, p.264: chi_S(n,e,L) is the minimum of chi_S(G(n,e),L) over all graphs G(n,e) with n vertices
      and e edges, "the smallest number r such that there exists a G(n,e) that has an edge-coloring in r colors such
      that every L in G is TMC" (BEGS89-renyi.txt l.68-71).  So it ranges over SOME graph with exactly e edges; a
      copy is a subgraph, not necessarily induced (l.61); no properness is required.  A colouring into 'I_r uses at
      most r colours, and the least such r is the least number of colours used exactly.  Every colouring has at least
      one value, so chi_S >= 1, and chi_S = 1 when no copy exists (BEGS89 l.73-74).  The question is BEGS89's after
      Theorem 5.1, p.270: "It may in fact be true that for all odd k >= 7, if e = t_2(n) + 1, then chi_S(n,e,C_k) =
      (1 + o(1))(n^2/8)" (l.359-361), with t_2(n) = floor(n^2/4).  Status: open at the pin for the asked range
      k >= 3.  Bucic, Chen and Ma, arXiv:2603.18952v1 (19 March 2026, before the pin), Conjecture 1.1
      (main.tex l.215-218), prove it for every k >= 4 (Theorem 1.2, l.220-225: for floor(n^2/4) + 1 <= e <= C(n,2),
      f(n,e,C_(2k+1)) = e/2 + (n/2) sqrt(e - n^2/4) + o(n^2), which is n^2/8 + o(n^2) at e = floor(n^2/4) + 1).
      k = 3 (C_7) remains open: "we crucially used the assumption that k >= 4", and the first case is "the main
      bottleneck in resolving the k = 3 case" (l.707-708); the page says the same (erdos-809.txt l.36-38).  Their
      f(n,e,H) takes graphs with AT LEAST e edges (l.196); it equals chi_S on the valid range e <= C(n,2), as a
      colouring of a graph with more edges restricts to a spanning subgraph with exactly e edges, keeping every copy
      rainbow.  For C_3 the value is 3 (erdos-809.txt l.39), and grounding_X259 proves it at n = 3
      (g259_chiS_3_3_C3, non-vacuous).  Its hyp_inhabited value chi_S(3,3,C_7) = 1 holds vacuously in the copies: K_3,
      the only graph with 3 vertices and 3 edges, has no copy of C_7. *)
Definition strong_chromatic_odd_cycles_statement : Prop :=
  forall k q : nat, 3 <= k -> 1 <= q -> exists N : nat, forall n s : nat, N <= n ->
    x259_strong_chromatic_number n (n ^ 2 %/ 4 + 1) (cycle_graph (2 * k + 1)) s ->
    q * (8 * s) <= (q + 1) * n ^ 2 /\ q * n ^ 2 <= (q + 1) * (8 * s).
