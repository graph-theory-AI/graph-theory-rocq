(** * Chromatic.conjectures.X256 -- wave X256: Kempe changes (polynomial length on degenerate graphs, the
    Las Vergnas-Meyniel colour classes, a linear palette for K_t-minor-free graphs, Mohar's two conjectures, Vizing's
    question) (2026-10-28)

    A six-row wave under the prospective contract of meta/faithfulness_policy.json (hard lint, classified local
    helpers, grounding certificates, an independent verifier).  Rows: arxiv:2112.02313#00 (polynomial-length Kempe
    sequences in (k-1)-degenerate graphs), studies:std_las_vergnas_meyniel_conjecture_a_kempe_equivalen (Las Vergnas
    and Meyniel's Conjecture A'), arxiv:2103.10684#01 (a linear palette for graphs with no K_t-minor),
    studies:std_mohar_s_conjecture_kempe_equivalence_of_k_colour (Mohar, k-regular graphs),
    studies:std_mohar_s_conjecture_kempe_equivalence_of_2_edge_c (Mohar, (Delta + 2)-edge-colourings) and
    studies:std_vizing_s_edge_colouring_kempe_equivalence_questi (Vizing's question, a synonym of X213's bm-060
    statement).  Shared vocabulary is reused: [proper_colouring] (GTBase.colourings), [k_degenerate], [regular] and
    [Delta] (GTBase.base), [minor] and [clique] (the library, via GTBase), and X213's edge-colouring Kempe vocabulary
    ([x213_proper_edge_colouring], [x213_kempe_reach], [vizing_kempe_interchange_statement]).  X162's vertex Kempe
    step is NOT reused: its audit (meta/STATEMENT_IMPROVEMENTS.md, arxiv:1510.06964#00) found that it accepts any
    connected two-coloured set rather than a whole Kempe chain, which makes every recolouring reachable; the local
    [x256_kempe_chain] is a whole chain.  The sources are the Mac's deposit
    coordination/sources/x256-source-mac-20261028 (versioned e-prints, TeX line numbers below); the grounding
    certificates are in grounding_X256.v. *)

From GTBase Require Export base.
From GTBase Require Import colourings.
From Chromatic.conjectures Require Import X213.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local x256 vocabulary ************************************************* *)

(** A KEMPE CHAIN (arXiv:2112.02313v1, TeX l.156-157; arXiv:1510.06964v3, l.67): [S] is an (a, b)-component of the
    vertex colouring [col], a connected component of the subgraph induced by the vertices coloured a or b.  Encoded as
    a nonempty connected set of vertices coloured a or b that contains every neighbour coloured a or b of each of its
    vertices. *)
Definition x256_kempe_chain (G : sgraph) (k : nat) (col : G -> 'I_k) (a b : 'I_k) (S : {set G}) : Prop :=
  [/\ S != set0, connected S,
      forall v : G, v \in S -> (col v == a) || (col v == b) &
      forall u v : G, u \in S -> u -- v -> (col v == a) || (col v == b) -> v \in S].

(** A KEMPE CHANGE (arXiv:2112.02313v1, l.157-158): [col'] exchanges two distinct colours a and b on one Kempe chain
    of [col] and agrees with [col] elsewhere. *)
Definition x256_kempe_change (G : sgraph) (k : nat) (col col' : G -> 'I_k) : Prop :=
  exists (a b : 'I_k) (S : {set G}),
    [/\ a != b, x256_kempe_chain col a b S &
        forall v : G, col' v = if v \in S then (if col v == a then b else a) else col v].

(** [col'] is reached from [col] by AT MOST [n] Kempe changes; colourings are compared pointwise, so the number of
    changes, not the presentation of the functions, is what is bounded.  Two colourings are Kempe equivalent when
    some [n] works. *)
Fixpoint x256_kempe_reach_le (G : sgraph) (k n : nat) (col col' : G -> 'I_k) {struct n} : Prop :=
  match n with
  | 0 => col =1 col'
  | n'.+1 => col =1 col' \/ exists c : G -> 'I_k, x256_kempe_change col c /\ x256_kempe_reach_le n' c col'
  end.

(** ** Statements ************************************************************ *)

(** Corpus row: arxiv:2112.02313#00
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/2112.02313__00/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/2112.02313__00.json
    English statement: (Bonamy, Delecroix and Legrand-Duchesne, Kempe changes in degenerate graphs)
      Can any two k-colorings of a (k-1)-degenerate graph on n vertices always be connected by a sequence of Kempe
      changes whose length is polynomial in n?
    Definitions: [k_degenerate G d] - every nonempty vertex set has a vertex with at most d neighbours inside it
      (GTBase.base); [proper_colouring col] - adjacent vertices get distinct colours (GTBase.colourings);
      [x256_kempe_reach_le n col col'] - col' is reached from col by at most n Kempe changes (this file).
    Notes: affirmative form.  The polynomial may depend on k: the source asks for bounds "similar" to Bousquet and
      Heinrich's O(n^(d+3)) for d-degenerate graphs, whose exponent grows with d (TeX l.209-219: "even a
      polynomial upper-bound on the number of changes would be highly interesting"), and its abstract asks "whether it
      can be turned polynomial" (l.142-143); so for every k there are c and d, not one pair for all k.  A polynomial
      p(n) is at most c * n^d for n >= 1 (c the sum of the absolute values of its coefficients), and the empty graph
      needs no change.  k = 0 asks nothing: no nonempty graph has a colouring into 'I_0 (k - 1 truncates to 0 there,
      and 0-degenerate means edgeless).  Las Vergnas and Meyniel's lemma (l.196-199, k >= d + 1) makes the
      colourings Kempe equivalent, with possibly exponential sequences; the paper's polynomial bounds assume more
      (treewidth, maximum average degree, maximum degree, l.292-338).  Literature status: open at the pin (pinned
      status open). *)
Definition degenerate_kempe_polynomial_length_statement : Prop :=
  forall k : nat, exists c d : nat, forall (G : sgraph) (col1 col2 : G -> 'I_k),
    k_degenerate G (k - 1) -> proper_colouring col1 -> proper_colouring col2 ->
    x256_kempe_reach_le (c * #|G| ^ d) col1 col2.

(** Corpus row: studies:std_las_vergnas_meyniel_conjecture_a_kempe_equivalen
    Site: none
    Review: none
    English statement: (Las Vergnas and Meyniel, "Las Vergnas-Meyniel conjecture A (Kempe equivalence of colorings)")
      For every t and every graph with no K_t-minor, every equivalence class of t-colourings contains some
      (t-1)-colouring.
    Definitions: [minor G H] - H is a minor of G (the library, via GTBase); 'K_t - the complete graph on t vertices;
      [proper_colouring col] (GTBase.colourings); [x256_kempe_reach_le n col col'] (this file).
    Notes: the pinned text is Las Vergnas and Meyniel's Conjecture A', not their Conjecture A (arXiv:2103.10684v2, TeX
      l.154-156 for A, "all the t-colourings ... form a single equivalence class"; l.160-162 for A', this text), though
      the row's slug and title say conjecture A (CORPUS_FEEDBACK).  An equivalence class is a Kempe class, and a
      (t-1)-colouring in it is a member that is proper and uses at most t - 1 of the t colours (the source's colourings
      are proper, l.146).  t = 0 asks nothing: every graph has a K_0 minor.  Literature status: DISPROVED before the
      pin in the row's own record (pinned status open; CORPUS_FEEDBACK): "Here, we disprove both Conjectures A and A'"
      (l.164), by Theorem 1.3 (l.166-168) and the frozen colourings of l.170: a graph with no K_t-minor (so no K_s-minor
      for s >= t) with an s-colouring, s = (3/2 - eps) t, in which every two colour classes induce a connected subgraph,
      so a Kempe change only exchanges two whole classes and every member of its class uses all s colours.  Encoded as
      stated; the row is false at the pin. *)
Definition las_vergnas_meyniel_kempe_class_fewer_colours_statement : Prop :=
  forall (t : nat) (G : sgraph) (col : G -> 'I_t),
    ~ minor G ('K_t) -> proper_colouring col ->
    exists (n : nat) (col' : G -> 'I_t),
      [/\ x256_kempe_reach_le n col col', proper_colouring col' & #|[set col' v | v in G]| < t].

(** Corpus row: arxiv:2103.10684#01
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/2103.10684__01/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/2103.10684__01.json
    English statement: (Bonamy, Heinrich, Legrand-Duchesne and Narboni, On a recolouring version of Hadwiger's
      conjecture, Question 1.7)
      Is there a constant c' such that for every t, all the c'.t-colourings of a graph with no K_t-minor form a
      single equivalence class?
    Definitions: [minor G H], 'K_t, [proper_colouring col] and [x256_kempe_reach_le n col col'] as in the row above.
    Notes: affirmative form, with c' a positive integer c and exactly c t colours.  The source leaves c' real
      ("c' >= 3/2", TeX l.191) and the number of colours unrounded (as in its Theorem 1.3, l.166-168).  Every reading
      is equivalent for a positive constant: an integer c' with c' t colours, a real or rational c' with ceil(c' t) or
      floor(c' t) colours, or every number k >= c' t of colours.  Every k >= c t gives k = c t, and an integer is real.
      Conversely, let a real c' > 0 work with p(t) colours, p(t) = ceil(c' t) or floor(c' t).  For G with no
      K_t-minor and m <= u - t, the join G + K_m of G with a new m-clique has no K_u-minor, so its p(u)-colourings form
      one class.  In each of them the clique takes m distinct colours and G the other p(u) - m.  Along a sequence of
      Kempe changes of G + K_m, keep a bijection from the colours off the clique to a fixed set of p(u) - m colours,
      and when a change exchanges a clique colour a with an off-clique colour b, give a the old index of b: a change on
      two off-clique colours is then a Kempe change of G in the fixed palette, a change on a clique colour and an
      off-clique one is the identity there, and a change on two clique colours leaves G alone.  So any two
      (p(u) - m)-colourings of G are joined by Kempe changes of G up to a permutation of the palette, and a permutation
      is a product of transpositions, each made by the changes on all (a, b)-chains: the (p(u) - m)-colourings of G
      form one class.  The numbers p(u) - (u - t), ..., p(u) form overlapping windows for u >= t + ceil(c'), which
      cover every k >= p(t + ceil(c')) <= C t with C = ceil(c') (ceil(c') + 1), for t >= 1 (t = 0 asks nothing:
      every graph has a K_0 minor).  So the threshold reading with the integer C holds.  No monotonicity in the
      number of colours is used (Kempe equivalence is not known to be monotone).  c = 0 is excluded: an empty palette
      would make the claim vacuous, and the source's c' is at least 3/2.  Literature status: open at the pin (pinned
      status open).  Theorem 1.3 gives c' >= 3/2 (l.191); the known upper bound is not linear: graphs with no
      K_t-minor are O(t sqrt(log t))-degenerate, and all k-colourings of a d-degenerate graph are Kempe equivalent
      for k > d (l.203-207). *)
Definition minor_free_linear_palette_kempe_class_statement : Prop :=
  exists c : nat, 0 < c /\
    forall (t : nat) (G : sgraph) (col1 col2 : G -> 'I_(c * t)),
      ~ minor G ('K_t) -> proper_colouring col1 -> proper_colouring col2 ->
      exists n : nat, x256_kempe_reach_le n col1 col2.

(** Corpus row: studies:std_mohar_s_conjecture_kempe_equivalence_of_k_colour
    Site: none
    Review: none
    English statement: (Mohar, "Mohar's Conjecture (Kempe equivalence of k-colourings of k-regular graphs)")
      For k >= 3, all k-colourings of a k-regular graph that is not complete are Kempe equivalent.
    Definitions: [regular G k] - every vertex has exactly k neighbours (GTBase.base); [clique S] - any two distinct
      vertices of S are adjacent (the library), so "not complete" is ~ clique [set: G]; [proper_colouring col] and
      [x256_kempe_reach_le n col col'] as above.
    Notes: graphs may be disconnected, as stated.  The sources treat connected graphs, other graphs
      "componentwise" (arXiv:1510.06964v3, TeX l.134): a Kempe chain lies in one component.  A k-regular graph with a
      K_(k+1) component has no k-colouring, so it satisfies the statement vacuously.  The pinned sentence is the
      abstract of Feghali, Johnson and Paulusma (arXiv:1503.03430v2, kempecubic.tex l.53).  Literature status: FALSE
      as stated at the pin (pinned status open; CORPUS_FEEDBACK): for k = 3 the triangular prism (two triangles joined
      by a perfect matching) is 3-regular and not complete, and its 3-colourings form two Kempe classes (van den
      Heuvel; FJP Lemma 1, l.176-177, with l.174: the three two-coloured subgraphs are connected, so the classes are
      the two colourings up to permutation).  FJP's Theorem 1 (l.98-100) gives one class for every other cubic graph
      but K_4, and Bonamy, Bousquet, Feghali and Johnson (arXiv:1510.06964v3, Theorem 1, l.130-132) for every
      connected non-complete k-regular graph with k >= 4; l.79 recalls the prism counterexample.  Encoded as stated;
      the row is false at the pin (it holds for k >= 4). *)
Definition mohar_regular_kempe_class_statement : Prop :=
  forall (k : nat) (G : sgraph) (col1 col2 : G -> 'I_k),
    3 <= k -> regular G k -> ~ clique [set: G] ->
    proper_colouring col1 -> proper_colouring col2 ->
    exists n : nat, x256_kempe_reach_le n col1 col2.

(** Corpus row: studies:std_mohar_s_conjecture_kempe_equivalence_of_2_edge_c
    Site: none
    Review: none
    English statement: (Mohar, "Mohar's Conjecture (Kempe equivalence of (Delta+2)-edge-colourings)")
      For every simple graph G, all (Delta(G) + 2)-edge-colourings are Kempe-equivalent.
    Definitions: [Delta G] - the maximum degree, 0 for the empty graph (GTBase.base); [x213_proper_edge_colouring col]
      - a symmetric map G -> G -> 'I_k giving distinct colours to two edges at a vertex (Chromatic.conjectures.X213);
      [x213_kempe_reach n col col'] - col' is reached from col by at most n Kempe changes, each exchanging two colours
      on a union of two-coloured edge components (X213; a union of chains is a composition of single-chain changes).
    Notes: an X213 colouring also assigns values to non-adjacent pairs, which no Kempe change moves, so Kempe
      equivalence is reaching a colouring that agrees with col2 on the edges.  One direction suffices: every pair is
      quantified.  The colourings use colours from {1, ..., Delta(G) + 2}, as arXiv:2107.07900v1 defines
      Kempe-equivalence (TeX l.181).  Literature status: solved before the pin (pinned status open; CORPUS_FEEDBACK).
      By Vizing, chi'(G) <= Delta(G) + 1.  If chi'(G) = Delta(G) + 1 then Delta(G) + 2 = chi'(G) + 1, and Narboni
      (arXiv:2302.12914v1, intro.tex l.42-44) proves that all (chi'(G) + 1)-edge-colourings are Kempe-equivalent; if
      chi'(G) = Delta(G) then Delta(G) + 2 = chi'(G) + 2, Mohar's theorem (as cited in 2107.07900v1, l.190-192, and
      2302.12914v1, l.36-38; Mohar's paper was not read). *)
Definition mohar_max_degree_plus_two_edge_kempe_statement : Prop :=
  forall (G : sgraph) (col1 col2 : G -> G -> 'I_(Delta G + 2)),
    x213_proper_edge_colouring col1 -> x213_proper_edge_colouring col2 ->
    exists (n : nat) (col : G -> G -> 'I_(Delta G + 2)),
      x213_kempe_reach n col1 col /\ forall u v : G, u -- v -> col u v = col2 u v.

(** Corpus row: studies:std_vizing_s_edge_colouring_kempe_equivalence_questi
    Site: none
    Review: none
    English statement: (Vizing, "Vizing's edge-colouring Kempe-equivalence question")
      For every simple graph G, for any integer k > chi'(G), for any k-edge-colouring alpha, is there a
      chi'(G)-edge-colouring that can be reached from alpha through a series of Kempe changes?
    Definitions: [vizing_kempe_interchange_statement] - X213's bm-060 statement: from every proper k-edge-colouring and
      for every m <= k for which G is m-edge-colourable, Kempe changes reach a proper edge colouring using at most m
      colours (Chromatic.conjectures.X213).
    Notes: a SYNONYM of X213's statement of the same question (bm:bm-060; arXiv:2107.07900v1, Question 1.3, TeX
      l.174-176, is this text).  This row implies X213's: given m <= k with G m-edge-colourable, chi'(G) <= m; if
      k > chi'(G) the reached chi'(G)-edge-colouring uses chi'(G) <= m colours, and if k = chi'(G) then m = k and alpha
      itself uses at most k colours, with no change.  X213's implies this row: take m = chi'(G) <= k; the reached
      proper colouring uses at most chi'(G) colours on the edges, hence exactly chi'(G): a chi'(G)-edge-colouring in
      alpha's palette.  Literature status: solved before the pin (pinned status open; CORPUS_FEEDBACK), as X213's
      Notes record (Narboni, arXiv:2302.12914v1, intro.tex l.42-50). *)
Definition vizing_kempe_optimal_colouring_question_statement : Prop :=
  vizing_kempe_interchange_statement.
