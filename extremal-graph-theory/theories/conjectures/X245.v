(** * Extremal.conjectures.X245 -- wave X245: counting H-free graphs, spanning cubes in random graphs, non-isomorphic induced subgraphs of Ramsey graphs (2026-10-27)

    A three-row wave under the prospective contract of meta/faithfulness_policy.json.  Rows: erdos:59 (the number of
    labelled H-free graphs against 2^{(1+o(1)) ex(n;H)}), erdos:578 (G(2^d, 1/2) contains a spanning Q_d almost
    surely) and erdos:1036 (2^{Omega(n)} pairwise non-isomorphic induced subgraphs of a graph with no clique or
    independent set on c log n vertices).  No local helper and no copied vocabulary: Turan numbers are
    Extremal.conjectures.D2tur's [is_turan_number n Fam m]; GTBase supplies [has_subgraph], 'K_n, [del_edge_set]
    and [product_hypercube] (GTBase.hypercubes); [cliqueb], [stable], [induced] and the isomorphism type G ≃ H are
    upstream (non-isomorphism written ~ inhabited (induced A ≃ induced B), GTBase.common's idiom).  A labelled graph
    on 'I_n is given by its edge set F, a set of pairs of 'I_n, as the spanning subgraph
    [del_edge_set 'K_n (E('K_n) :\: F)] of K_n.  All three rows have pinned status "solved"; their literature lines
    are dated against the corpus pin (graph-conjectures b72c5857, 2026-09-23).  The grounding certificates are in
    grounding_X245.v. *)

From Extremal.conjectures Require Import D2tur.
(* GTBase last: its canonical [edge_count] must shadow D2tur's eta-alias of the same name. *)
From GTBase Require Import base common hypercubes.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** X245 statements ******************************************************* *)

(** Corpus row: erdos:59
    Site: none
    Review: none
    English statement: (Erdos Problems #59)
      For every graph H that contains a cycle, the number of (labelled) graphs on n vertices which do not contain H
      is at most 2^{(1+o(1)) ex(n;H)}: for every eps > 0, if n is large enough, at most 2^{(1+eps) ex(n;H)}.
    Definitions: [is_turan_number n Fam m] - m = ex(n; Fam), an attained maximum over n-vertex graphs with no member
      of Fam as a subgraph (Extremal.conjectures.D2tur; here Fam is the single graph H); [del_edge_set 'K_n
      (E('K_n) :\: F)] - the graph on 'I_n with edge set F (GTBase); [has_subgraph G H] - H is a (not necessarily
      induced) subgraph of G (GTBase.common); [cycle_graph k] - the cycle C_k, k >= 3 (GTBase).
    Notes: the pinned statement is the erdosproblems.com question ("Is it true that the number of graphs on n
      vertices which do not contain G is <= 2^{(1+o(1)) ex(n;G)}?"); the affirmative form is stated, for every graph
      H that contains a cycle (a subgraph C_k, k >= 3), the setting of the literature: Morris and Saxton state the
      conjecture (Erdos; Erdos, Frankl and Rodl) "for every graph H that contains a cycle" (paper.tex l.221).  For a
      forest the bound fails for a degenerate reason the question does not intend: for H = P_3 the H-free graphs are
      the matchings, ex(n; P_3) = n/2 for even n, and the (n - 1)!! perfect matchings alone exceed 2^{2 ex} = 2^n once
      n >= 18 (Arthur, A3 design read (211)).  Graphs on n vertices are labelled (edge sets F on 'I_n, the counting
      convention of the literature); a bound on their number is a bound on the size of every family Fs of H-free
      edge sets; eps = 1/q and #|Fs| <= 2^{(1 + 1/q) m} is raised to the q-th power.
      Literature status: FALSE BEFORE the corpus pin (pinned status "solved"): Morris and Saxton, "The number of
      C_{2l}-free graphs", arXiv:1309.2927v3 (v1 2013-09-11, v3 2015-11-11), Proposition 1.4 (paper.tex l.227-231):
      "There exists a constant c > 0 such that there are at least 2^{(1 + c) ex(n,C_6)} C_6-free graphs on n vertices
      for infinitely many values of n" (labelled graphs), so the row fails at H = C_6; the weaker bound
      2^{O(ex(n;H))} is not contradicted and not asked.  The mirror (10fb9c15) lists "disproved (Lean)"
      (2026-08-24). *)
Definition turan_exponent_free_graph_count_statement : Prop :=
  forall (H : sgraph) (q : nat), 1 <= q -> (exists k : nat, 3 <= k /\ has_subgraph H (cycle_graph k)) ->
    exists n0 : nat,
    forall n m : nat, n0 <= n -> is_turan_number n (fun _ : 'I_1 => H) m ->
      forall Fs : {set {set {set 'I_n}}},
        (forall F : {set {set 'I_n}}, F \in Fs ->
           F \subset E('K_n) /\ ~ has_subgraph (del_edge_set 'K_n (E('K_n) :\: F)) H) ->
        #|Fs| ^ q <= 2 ^ ((q + 1) * m).

(** Corpus row: erdos:578
    Site: none
    Review: none
    English statement: (Erdos Problems #578, Erdos and Bollobas)
      If G is a random graph on 2^d vertices, each edge present independently with probability 1/2, then G almost
      surely contains a copy of Q_d: the proportion of the labelled graphs on 2^d vertices that contain Q_d tends to
      1 as d tends to infinity.
    Definitions: [product_hypercube d] - Q_d (GTBase.hypercubes); [del_edge_set 'K_N (E('K_N) :\: F)] - the graph
      on 'I_N with edge set F (GTBase); [has_subgraph G H] - H is a (not necessarily induced) subgraph of G
      (GTBase.common).
    Notes: the pinned statement is the erdosproblems.com text ("If G is a random graph on 2^d vertices, including
      each edge with probability 1/2, then G almost surely contains a copy of Q_d").  G(N, 1/2) is the uniform
      distribution on the 2^{#|E(K_N)|} labelled graphs on 'I_N, so "almost surely" is: for every q, eventually a
      family Fs of edge sets each containing Q_d has at least (1 - 1/q) 2^{#|E(K_N)|} members, written
      q 2^E <= q |Fs| + 2^E (no subtraction).  A copy is a subgraph (the cube is spanning, 2^d vertices).
      Literature status: PROVED BEFORE the corpus pin (pinned status "solved"): Riordan, "Spanning subgraphs of
      random graphs", Combin. Probab. Comput. 9 (2000) 125-148, abstract (publisher page; the Mac's read limit: the
      abstract only): "Let G_p be a random graph on 2^d vertices where edges are selected independently with a fixed
      probability p > 1/4 ... as d -> infinity, G_p almost surely has a spanning subgraph isomorphic to" Q_d.  The
      mirror (10fb9c15) lists "proved". *)
Definition random_graph_spanning_hypercube_statement : Prop :=
  forall q : nat, 1 <= q -> exists d0 : nat, forall d : nat, d0 <= d ->
    exists Fs : {set {set {set 'I_(2 ^ d)}}},
      (forall F : {set {set 'I_(2 ^ d)}}, F \in Fs ->
         F \subset E('K_(2 ^ d)) /\
         has_subgraph (del_edge_set 'K_(2 ^ d) (E('K_(2 ^ d)) :\: F)) (product_hypercube d)) /\
      q * 2 ^ #|E('K_(2 ^ d))| <= q * #|Fs| + 2 ^ #|E('K_(2 ^ d))|.

(** Corpus row: erdos:1036
    Site: none
    Review: none
    English statement: (Erdos Problems #1036, Erdos and Renyi)
      For every c > 0 there is c' > 0 such that every graph on n vertices with no complete or empty induced subgraph
      on more than c log n vertices has at least 2^{c' n} induced subgraphs which are pairwise non-isomorphic.
    Definitions: [cliqueb S] - S is a clique, [stable S] - no two vertices of S are adjacent, [induced A] - the
      subgraph induced by A, G ≃ H - graph isomorphism (upstream); [~ inhabited (induced A ≃ induced B)] - the
      induced subgraphs on A and B are not isomorphic (GTBase.common's idiom).
    Notes: the pinned statement is the erdosproblems.com question ("Let G be a graph on n vertices which does not
      contain a trivial (empty or complete) graph on more than c log n vertices.  Must G contain at least
      2^{Omega_c(n)} many induced subgraphs which are not pairwise isomorphic?"); the affirmative form is stated.
      The hypothesis is written as X243's erdos:88 / 636 / 637: every clique or independent set S has
      2^{|S|} < n^C (|S| < C log_2 n); "more than c log n" against "< C log_2 n" is a change of the constant and of
      the base, absorbed since c ranges over all positive reals.  2^{n/p} <= |F| is raised to the p-th power; no
      "n large" is added: for small n, p >= n works with F = {set0, [set: G]}.
      Literature status: PROVED BEFORE the corpus pin (pinned status "solved"): Shelah, "Erdos and Renyi
      conjecture", J. Combin. Theory Ser. A 82 (1998) 179-185 (arXiv:math/9707226v1, 1997-07-15): the abstract and
      the introduction's (V) (p.179): "for every c_1 > 0 for some c_2 > 0 for n large enough for every graph G_n with
      n points, Rm(G_n) < c_1 (log n) implies I(G_n) >= 2^{c_2 n}" (Rm = the largest complete or edgeless set,
      I = the number of induced subgraphs up to isomorphism, logarithms to base 2, p.180).  Printed discrepancy,
      stated and not corrected: the paper's Theorem (2) (p.180), in the published text and in the author's version,
      reads "if G is a graph with n edges"; the encoding follows the abstract, the introduction's (V) and the row
      text, which all speak of n vertices (points).  The mirror (10fb9c15) lists "proved (Lean)" (2026-01-20). *)
Definition ramsey_graph_many_nonisomorphic_induced_subgraphs_statement : Prop :=
  forall C : nat, exists p : nat, 1 <= p /\
    forall G : sgraph,
      (forall S : {set G}, cliqueb S || stable S -> 2 ^ #|S| < #|G| ^ C) ->
      exists F : {set {set G}},
        (forall A B : {set G}, A \in F -> B \in F -> A != B -> ~ inhabited (induced A ≃ induced B)) /\
        2 ^ #|G| <= #|F| ^ p.
