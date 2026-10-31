(** * Chromatic.conjectures.X272 -- wave X272: a fractional 19/7 bound for subcubic triangle-free graphs avoiding
    four obstructions, the 2-colouring number of planar graphs, and Thomassen's exponentially-many-3-colourings
    conjecture (2026-10-31)

    A three-row wave under the prospective contract of meta/faithfulness_policy.json.  Rows: arxiv:2204.12683#00
    (Conjecture 1.6 of Dvorak, Lidicky and Postle: every subcubic triangle-free graph avoiding F14(1), F14(2), F11
    and F22 as subgraphs is fractionally 19/7-colourable),
    studies:std_kierstead_et_al_question_on_the_2_coloring_numbe (is the 2-colouring number of every planar graph at
    most 8?) and studies:std_thomassen_s_conjecture_exponentially_many_3_colo (some beta > 0 such that every
    triangle-free planar graph has at least 2^(beta |V(G)|) 3-colourings).
    Shared vocabulary: GTBase's [subcubic], [triangle_free], [wagner_planar] (base.v), [has_subgraph] (common.v),
    [fg_mk_sgraph] (finite_graph.v) and [proper_colouring] (colourings.v); Chromatic X130's [x130_frac_chi_le], used
    unchanged; coq-graph-theory's neighbourhoods.
    Local helpers: the four obstructions ([x272_f14a], [x272_f14b], [x272_f11], [x272_f22]) and the 2-colouring
    number bound ([x272_col2_le]).
    Pinned statuses: all three open; literature lines are dated against the corpus pin (graph-conjectures b72c5857,
    2026-09-23).  The sources are the Mac's deposits coordination/sources/x270-source-mac-20261031 (2204.12683v3) and
    x272-source-mac-20261031 (the other rows; TeX and text line numbers below).  The grounding certificates are in
    grounding_X272.v. *)

From GTBase Require Import base common colourings.
From Chromatic.conjectures Require Import X130.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** X272 vocabulary ********************************************************* *)

(** The obstruction F14(1) of arXiv:2204.12683v3 (aic-elevenfour.tex l.392-405, Figure fig-forb): the generalized
    Petersen graph GP(7, 2).  Vertices x_i = i and y_i = 7 + i (i < 7): the outer cycle x_i x_(i+1), the spokes x_i
    y_i and the inner cycle y_i y_(i+2), indices mod 7.  Cubic and triangle-free, with alpha = 5 (chi_f = 14/5,
    l.260-261). *)
Definition x272_f14a : sgraph :=
  fg_mk_sgraph (fun i j : 'I_14 => (val i, val j) \in
    [:: (0, 1); (1, 2); (2, 3); (3, 4); (4, 5); (5, 6); (6, 0);
        (0, 7); (1, 8); (2, 9); (3, 10); (4, 11); (5, 12); (6, 13);
        (7, 9); (9, 11); (11, 13); (13, 8); (8, 10); (10, 12); (12, 7)]).

(** The obstruction F14(2) (aic-elevenfour.tex l.407-431, Figure fig-forb): the 8-cycle x_0 ... x_7 (x_i = i) with
    z_1, z_2, z_3 = 8, 9, 10 and w_1, w_2, w_3 = 11, 12, 13; edges x_0 z_1, z_1 z_2, z_2 w_2, w_2 w_1, w_1 x_7, x_2
    z_2, w_2 x_5, z_3 x_1, z_3 w_1, z_3 x_4, w_3 x_6, w_3 z_1, w_3 x_3.  Cubic and triangle-free, with alpha = 5. *)
Definition x272_f14b : sgraph :=
  fg_mk_sgraph (fun i j : 'I_14 => (val i, val j) \in
    [:: (0, 1); (1, 2); (2, 3); (3, 4); (4, 5); (5, 6); (6, 7); (7, 0);
        (0, 8); (8, 9); (9, 12); (12, 11); (11, 7); (2, 9); (12, 5);
        (10, 1); (10, 11); (10, 4); (13, 6); (13, 8); (13, 3)]).

(** The obstruction F11 (aic-elevenfour.tex l.467-484, Figure fig-forb2): x_0 ... x_3 = 0 ... 3, y_0 ... y_3 = 4 ...
    7, x_l = 8, x_r = 9, y_t = 10; the 10-cycle x_l x_0 x_1 y_2 y_3 x_r x_3 x_2 y_1 y_0, the path x_l y_t x_r and the
    chords x_1 y_1, x_2 y_2, x_0 x_3, y_0 y_3.  Subcubic (y_t has degree 2) and triangle-free, with alpha = 4 (chi_f
    = 11/4). *)
Definition x272_f11 : sgraph :=
  fg_mk_sgraph (fun i j : 'I_11 => (val i, val j) \in
    [:: (8, 0); (0, 1); (1, 6); (6, 7); (7, 9); (9, 3); (3, 2); (2, 5); (5, 4); (4, 8);
        (8, 10); (10, 9); (1, 5); (2, 6); (0, 3); (4, 7)]).

(** The obstruction F22 (aic-elevenfour.tex l.439-464, Figure fig-forb2): x_i = i, y_i = 5 + i, z_i = 10 + i,
    w_i = 15 + i (i < 5), z = 20, w = 21; the paths x_i y_i z_i w_i, the edges x_i x_(i+1), z_i y_(i+1), w_i w_(i+1)
    (i < 4), the path y_0 z w w_0, and the three edges of the stubs the figure labels 1, 2 and 3 (w_4 x_0, z_4 z,
    x_4 w).  Cubic and triangle-free, with alpha = 8 (chi_f = 11/4). *)
Definition x272_f22 : sgraph :=
  fg_mk_sgraph (fun i j : 'I_22 => (val i, val j) \in
    [:: (0, 5); (1, 6); (2, 7); (3, 8); (4, 9);
        (5, 10); (6, 11); (7, 12); (8, 13); (9, 14);
        (10, 15); (11, 16); (12, 17); (13, 18); (14, 19);
        (0, 1); (1, 2); (2, 3); (3, 4);
        (10, 6); (11, 7); (12, 8); (13, 9);
        (15, 16); (16, 17); (17, 18); (18, 19);
        (5, 20); (20, 21); (21, 15);
        (19, 0); (14, 20); (4, 21)]).

(** The 2-colouring number at most k (Kierstead, Mohar, Spacapan, Yang and Zhu, the 2009 preprint, p.2; Dvorak,
    Kaiser and Kral', arXiv:1506.01412v3, twocol.tex l.57-71).  A linear ordering of V(G) is given by an injective
    rank rk. L(v) is the set of the vertices u before v that are adjacent to v or have a common neighbour w after v
    (the paths of length at most 2 from v whose interior is after v), and col_2(G) = 1 + min over orderings of max
    |L(v)|.  So col_2(G) <= k iff some ordering has |L(v)| + 1 <= k at every vertex v, for every non-empty G.  On
    the empty graph the helper holds for every k, 0 included (no vertex to bound), while 1 + max would give 1; no
    instance with k >= 1, such as the statement's k = 8, distinguishes the two. *)
Definition x272_col2_le (G : sgraph) (k : nat) : Prop :=
  exists rk : G -> nat, injective rk /\
    forall v : G,
      #|[set u : G | (rk u < rk v) && (u -- v || [exists w : G, [&& rk v < rk w, u -- w & w -- v]])]|.+1 <= k.

(** ** X272 statements ********************************************************* *)

(** Corpus row: arxiv:2204.12683#00
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/2204.12683__00/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/2204.12683__00.json
    English statement: (Dvorak, Lidicky and Postle, Fractional coloring of subcubic triangle-free graphs,
      arXiv:2204.12683, Conjecture 1.6)
      Every subcubic triangle-free graph avoiding F14(1), F14(2), F11, and F22 as subgraphs is fractionally
      19/7-colorable.
    Definitions: [subcubic G] - every vertex has at most three neighbours (GTBase base.v); [triangle_free G] - no
      three mutually adjacent vertices (GTBase base.v); [has_subgraph G F] - an injective adjacency-preserving map
      from F into G, a copy of F as a subgraph, not necessarily induced (GTBase common.v); [x272_f14a], [x272_f14b],
      [x272_f11], [x272_f22] - the four obstructions (this file); [x130_frac_chi_le G p q] - some (a:b)-fold
      colouring of G with 0 < b and a q <= p b (Chromatic X130.v).
    Notes: encoded as stated; pinned status open.  The conjecture is aic-elevenfour.tex l.269-272
      (arXiv:2204.12683v3, 28 March 2025, the last version before the pin; text l.135-136): "avoiding ... as
      subgraphs", so no subgraph of G is isomorphic to any of the four, not Theorem 1.4's weaker "no component
      isomorphic to".  The four graphs are transcribed from the TikZ of Figures fig-forb (l.392-434) and fig-forb2
      (l.437-533); the helpers' comments give the vertex numbering.  Their invariants match the paper (l.259-261):
      F14(1), F14(2) and F22 are cubic, F11 is subcubic, all four are triangle-free, and n / alpha is 14/5, 14/5,
      11/4 and 11/4, above 19/7 each.  Fractional 19/7-colourability is the paper's second condition (l.191-193:
      positive a, b with a / b <= 19/7 and b-subsets of {1, ..., a} disjoint on edges); with b > 0 a vertex forces a
      > 0, and the empty graph has a (1:1)-fold colouring. The same source proves 11/4 when only F14(1) and F14(2)
      are excluded as components (Theorem 1.4, l.254-258). *)
Definition dvorak_lidicky_postle_obstructions_fractional_nineteen_sevenths_statement : Prop :=
  forall G : sgraph, subcubic G -> triangle_free G ->
    ~ has_subgraph G x272_f14a -> ~ has_subgraph G x272_f14b -> ~ has_subgraph G x272_f11 ->
    ~ has_subgraph G x272_f22 -> x130_frac_chi_le G 19 7.

(** Corpus row: studies:std_kierstead_et_al_question_on_the_2_coloring_numbe
    Site: none
    Review: none
    English statement: (Kierstead et al., question on the 2-coloring number, studies slice of the corpus)
      Is the two-coloring number of all planar graphs bounded by 8?
    Definitions: [wagner_planar G] - G has neither K_5 nor K_(3,3) as a minor, which by Wagner's theorem is planarity
      (GTBase base.v); [x272_col2_le G k] - the 2-colouring number of G is at most k (this file).
    Notes: encoded as its affirmative answer; pinned status open, but TRUE at the pin.  Kierstead, Mohar, Spacapan,
      Yang and Zhu (The two-coloring number and degenerate colorings of planar graphs, preprint 2009, in the deposit)
      define k-reachability on p.2 (text l.80-90: x before y, an xy-path of length at most k whose interior is after
      y) and col_k = 1 + min over orderings of the maximum number of vertices k-reachable from one vertex; their
      Question 1 (p.4, text l.189) asks whether col_2(G) <= 8 for every planar G.  Dvorak, Kaiser and Kral'
      (arXiv:1506.01412v3, 21 June 2018, twocol.tex l.57-71 the same definition, l.84-86 Theorem 1) prove "The
      two-coloring number of any planar graph is at most 8", which answers it; the status correction is a separate
      corpus item.  A path of length 2 has one interior vertex, so 2-reachability is adjacency or a common neighbour
      after v, the helper's set. *)
Definition planar_two_colouring_number_at_most_eight_statement : Prop :=
  forall G : sgraph, wagner_planar G -> x272_col2_le G 8.

(** Corpus row: studies:std_thomassen_s_conjecture_exponentially_many_3_colo
    Site: none
    Review: none
    English statement: (Thomassen 2007, studies slice of the corpus)
      There exists a positive real number beta such that every triangle-free planar graph G has at least
      2^(beta |V(G)|) different 3-colorings.
    Definitions: [wagner_planar G] - G has neither K_5 nor K_(3,3) as a minor (GTBase base.v); [triangle_free G] - no
      three mutually adjacent vertices (GTBase base.v); [proper_colouring f] - adjacent vertices get different
      colours (GTBase colourings.v); #|[set f : {ffun G -> 'I_3} | proper_colouring f]| - the number of proper
      colourings of G with the three labelled colours of 'I_3.
    Notes: encoded as stated; pinned status open, but FALSE at the pin.  The statement is Conjecture 1 of Dvorak and
      Sereni (arXiv:1702.00588v2, 19 September 2017, main.tex l.99-105), Thomassen's 2007 Conjecture 2.1(b) in their
      formulation; their colourings are labelled.  Dvorak and Postle (arXiv:2108.12669v1, 28 August 2021, bebound.tex
      l.60-63 Theorem 1) give, for infinitely many n, an n-vertex triangle-free planar graph with at most
      64^(n^(log_(9/2) 3)) < 64^(n^0.731) 3-colourings, and l.56-57 record that Thomassen had already disproved the
      conjecture (at most 2^(15 n / log_2 n), his 2021 manuscript in the deposit).  The status correction is a
      separate corpus item.  A real beta > 0 is equivalent to a rational p / q with p, q >= 1 (a smaller positive
      rational exists and the bound is monotone in beta), so the body reads 2^(p n) <= N^q for the count N; the empty
      graph has one colouring and 2^0 = 1, a true instance.  The records 2408.04618 and 2505.08634 attached to this
      row concern another conjecture of Thomassen's (Hamiltonicity), not this one. *)
Definition thomassen_triangle_free_planar_exponentially_many_three_colourings_statement : Prop :=
  exists p q : nat, [/\ 0 < p, 0 < q &
    forall G : sgraph, wagner_planar G -> triangle_free G ->
      2 ^ (p * #|G|) <= #|[set f : {ffun G -> 'I_3} | proper_colouring f]| ^ q].
