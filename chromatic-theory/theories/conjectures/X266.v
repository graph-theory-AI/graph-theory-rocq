(** * Chromatic.conjectures.X266 -- wave X266: clustered colourings of strong products, and the Hall ratio with
    degree-weighted independence (2026-10-30)

    A three-row wave under the prospective contract of meta/faithfulness_policy.json.  Rows: arxiv:2407.21360#00
    (Conjecture 7: for every c >= 2, products H boxtimes P of a graph of bounded treewidth and a path whose
    c-colourings all have clustering Omega(N^(c/(c^2-c+1))), N the order of the product), arxiv:2407.21360#01
    (Conjecture 8: products of two graphs of bounded treewidth whose 3-colourings all have clustering
    Omega(N^(4/7))) and arxiv:1812.07327#01 (Problem 5: graphs of bounded Hall ratio and arbitrarily large fractional
    chromatic number in which every subgraph H has an independent set of degree weight at least |E(H)| / c).
    Shared vocabulary: X264's strong product [x264_strong_product], GTBase's [clustered_colouring] (surface.v),
    [tree_bag_decomposition] (bag_decompositions.v), [ordinal_path] (path_graphs.v) and [has_subgraph] (common.v),
    X130's [x130_frac_chi_le], and coq-graph-theory's independence number, stable sets, neighbourhoods and edge sets.
    Local helpers: treewidth at most t ([x266_treewidth_at_most]) and the Hall ratio at most p / q
    ([x266_hall_ratio_le]).
    Pinned statuses: 2407.21360#00 partial, #01 open, 1812.07327#01 solved; literature lines are dated against the
    corpus pin (graph-conjectures b72c5857, 2026-09-23).  The sources are the Mac's deposit
    coordination/sources/x266-source-mac-20261030 (TeX line numbers below).  The grounding certificates are in
    grounding_X266.v. *)

From GTBase Require Import base common bag_decompositions path_graphs.
From Chromatic.conjectures Require Import X130 X264.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** X266 vocabulary ********************************************************* *)

(** G has treewidth at most t (Campbell et al., arXiv:2407.21360v1, Clustered_Colouring_of_Graph_Products.tex
    l.267-275): some tree-decomposition of G, here a GTBase [tree_bag_decomposition] over a tree T, has all bags of
    at most t + 1 vertices, i.e. width at most t.  Minor-theory's [x27_treewidth_at_most] is the same notion over its
    own decomposition copy, in a package chromatic-theory does not import. *)
Definition x266_treewidth_at_most (G : sgraph) (t : nat) : Prop :=
  exists (T : sgraph) (bag : T -> {set G}),
    tree_bag_decomposition bag /\ forall i : T, #|bag i| <= t.+1.

(** The Hall ratio of G is at most p / q (Dvorak, Ossona de Mendez and Wu, arXiv:1812.07327v2, no1sub.tex l.92-95:
    rho(G) is the maximum of |V(H)| / alpha(H) over all subgraphs H of G), cross-multiplied. *)
Definition x266_hall_ratio_le (G : sgraph) (p q : nat) : Prop :=
  forall H : sgraph, has_subgraph G H -> q * #|H| <= p * α([set: H]).

(** ** X266 statements ********************************************************* *)

(** Corpus row: arxiv:2407.21360#00
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/2407.21360__00/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/2407.21360__00.json
    English statement: (Campbell, Gollin, Hendrey, Lesgourgues, Mohar, Tamitegama, Tan and Wood, Conjecture 7 of
      arXiv:2407.21360v1)
      For any fixed integer c >= 2, there exists an integer t such that for infinitely many graphs H with treewidth
      t and paths P, every c-colouring of H boxtimes P has clustering Omega(|V(H boxtimes P)|^(c/(c^2-c+1))).
    Definitions: [x266_treewidth_at_most H t] - some tree-decomposition of H has all bags of at most t + 1 vertices
      (this file); [x264_strong_product H P] - the strong product H boxtimes P (Chromatic.conjectures.X264);
      [ordinal_path n] - the path P_n on 'I_n (GTBase path_graphs.v); [clustered_colouring G c s] - some colouring
      of G by 'I_c has every connected monochromatic vertex set of at most s vertices (GTBase surface.v).
    Notes: The conjecture is at l.242-244 of the source (arXiv:2407.21360v1, 31 July 2024,
      Clustered_Colouring_of_Graph_Products.tex).  l.160 defines a c-colouring as any map to at most c colours,
      adjacent vertices allowed the same colour, and the clustering of a colouring as the largest number of vertices
      of a monochromatic component.  A colouring has clustering at most s iff every connected monochromatic vertex
      set has at most s vertices, since each such set lies in a monochromatic component and each component is such a
      set: that is [clustered_colouring] with c colours.  The strong product is the union of the three adjacency
      cases of l.290 (X264's helper); with P = P_n ([ordinal_path n]) the order of the product is
      N = |V(H boxtimes P)| = #|H| * n.  "Omega" is a constant 1 / q, q > 0, which may depend on c and t: clustering
      at least N^(c/(c^2-c+1)) / q, i.e. no c-colouring of clustering s whenever (q s)^(c^2-c+1) < N^c (both sides
      raised to the power c^2-c+1).  "Infinitely many graphs H and paths P" is: for every M some H and P_n with
      N >= M, since only finitely many pairs have a bounded order.
      "Treewidth t" (l.267-275: the minimum width of a tree-decomposition) is encoded as treewidth at most t, which
      is equivalent for an existential t: given t, the exact treewidths of the members lie in {0, ..., t}, so one
      value t' is taken by members of arbitrarily large order (pigeonhole), and t' witnesses the exact form.  The
      tree-decompositions of l.267-270 cover every vertex, as GTBase's do: a vertex in no bag may be added as a new
      leaf bag {v} without raising the width.  Literature status: partial at the pin.  The source proves the lower
      bound for c = 2 (Theorem 1, l.172-175, with treewidth 2) and c = 3 (Theorem 2, l.181-183, with treewidth 3);
      c >= 4 is open.  Encoded as stated for every c >= 2.  c ^ 2 - c + 1 is a truncated subtraction that never
      truncates, since c <= c ^ 2 for every c. *)
Definition bounded_treewidth_path_product_clustering_statement : Prop :=
  forall c : nat, 2 <= c ->
    exists t q : nat, 0 < q /\
      forall M : nat, exists (H : sgraph) (n : nat),
        [/\ M <= #|H| * n, x266_treewidth_at_most H t &
            forall s : nat, (q * s) ^ (c ^ 2 - c + 1) < (#|H| * n) ^ c ->
              ~ clustered_colouring (x264_strong_product H (ordinal_path n)) c s].

(** Corpus row: arxiv:2407.21360#01
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/2407.21360__01/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/2407.21360__01.json
    English statement: (Campbell, Gollin, Hendrey, Lesgourgues, Mohar, Tamitegama, Tan and Wood, Conjecture 8 of
      arXiv:2407.21360v1)
      There exists a positive integer t such that for infinitely many graphs H_1, H_2 with treewidth t, every
      3-colouring of H_1 boxtimes H_2 has clustering Omega(|V(H_1 boxtimes H_2)|^(4/7)).
    Definitions: [x266_treewidth_at_most H t] - some tree-decomposition of H has all bags of at most t + 1 vertices
      (this file); [x264_strong_product H1 H2] - the strong product H1 boxtimes H2 (Chromatic.conjectures.X264);
      [clustered_colouring G 3 s] - some colouring of G by 'I_3 has every connected monochromatic vertex set of at
      most s vertices (GTBase surface.v).
    Notes: The source is arXiv:2407.21360v1 (31 July 2024), Clustered_Colouring_of_Graph_Products.tex l.248-250;
      colourings, clustering and the strong product as in Conjecture 7 (l.160, l.290), and the order of the product
      is N = #|H1| * #|H2|.  "Omega" is a constant 1 / q, q > 0: no 3-colouring of clustering s whenever
      (q s)^7 < N^4.  "Infinitely many graphs H_1, H_2" is infinitely many pairs (as in Theorem 3, l.187-189:
      "infinitely many pairs of graphs"), i.e. for every M some pair with N >= M.  "Treewidth t" is encoded as
      treewidth at most t, for both factors, which is equivalent for an existential positive t.  Pigeonhole alone
      gives a pair (t1, t2) of exact treewidths taken by pairs of arbitrarily large order, possibly with t1 <> t2.
      The disjoint union of each factor with K_(t+1) raises both exact treewidths to t, keeps the old product as a
      union of components of the new one (so every monochromatic component of the old product is one of the new),
      and multiplies N by at most (t + 2)^2 (both factors are nonempty once N >= 1), which replacing q by
      q (t + 2)^2 absorbs.  The guard 0 < t is the source's "positive integer"; with treewidth 0 both factors and
      their product are edgeless, of clustering 1.  Literature status: open at the pin.  The source proves the upper
      bound O(N^(4/7)) and the lower bound Omega(N^(1/2)) (Theorem 3, l.187-189). *)
Definition bounded_treewidth_products_three_colour_clustering_statement : Prop :=
  exists t q : nat,
    [/\ 0 < t, 0 < q &
        forall M : nat, exists H1 H2 : sgraph,
          [/\ M <= #|H1| * #|H2|, x266_treewidth_at_most H1 t, x266_treewidth_at_most H2 t &
              forall s : nat, (q * s) ^ 7 < (#|H1| * #|H2|) ^ 4 ->
                ~ clustered_colouring (x264_strong_product H1 H2) 3 s]].

(** Corpus row: arxiv:1812.07327#01
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/1812.07327__01/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/1812.07327__01.json
    English statement: (Dvorak, Ossona de Mendez and Wu, Problem 5 of arXiv:1812.07327v2)
      Do there exist, for some constant c > 0, graphs G of arbitrarily large fractional chromatic number such that
      rho(G) <= c and alpha_{deg_H}(H) >= |E(H)|/c for every H subseteq G?
    Definitions: [x130_frac_chi_le G p q] - some (a:b)-fold colouring of G has a q <= p b, i.e. chi_f(G) <= p / q
      (Chromatic.conjectures.X130); [x266_hall_ratio_le G p q] - q |V(H)| <= p alpha(H) for every subgraph H of G,
      i.e. rho(G) <= p / q (this file); [has_subgraph G H] - H is isomorphic to a (not necessarily induced)
      subgraph of G (GTBase common.v); α([set: H]) - the independence number of H, [stable I] - I is an independent
      set, E(H) - the edge set, N(v) - the neighbourhood of v in H (coq-graph-theory).
    Notes: The source (arXiv:1812.07327v2, 30 January 2020, no1sub.tex l.161-164) asks the question; it is encoded
      as its affirmative answer.  alpha_w(H) is the largest weight of an independent set of H (l.77-78), so
      alpha_{deg_H}(H) >= |E(H)| / c is: some independent set I of H has degree sum (degrees in H) at least
      |E(H)| / c.  When H has no edge, deg_H is identically 0, which l.75 does not call a weight assignment; the
      clause then asks for 0 <= 0 and holds.  The Hall ratio is the maximum of |V(H)| / alpha(H) over all subgraphs
      H (l.92-95), and "H subseteq G" ranges over all subgraphs, not only induced ones; both quantify over
      [has_subgraph], whose conditions are invariant under isomorphism.  The real constant c > 0 is a rational
      p / q with p, q > 0: every condition weakens as c grows, so some real c works iff some rational one does.  The
      same c bounds both conditions, as in the source.  "Arbitrarily large fractional chromatic number" is: for
      every F some G with chi_f(G) > F, the negation of X130's chi_f(G) <= F / 1 (X130 relates its cross-multiplied
      form to chi_f, which is attained on finite graphs; the source's weight definition, l.79-80, is the LP dual).
      Literature status: true at the pin (pinned status solved).  Steiner, Fractional chromatic number vs. Hall
      ratio (arXiv:2411.16465v1, 25 November 2024), Theorem 1.5 (main.tex l.140-142): for every delta > 0 and every
      large n an n-vertex G with chi_f(G) >= log log n / (50 log log log n), rho(G) <= 4 + delta and
      alpha_{deg_H}(G) >= |E(H)| / (4 + delta) for every subgraph H; deg_H is 0 outside V(H), so an independent set
      of G meets V(H) in an independent set of H of the same weight (l.144: the theorem is stronger).  delta = 1
      gives p / q = 5 / 1. *)
Definition hall_ratio_degree_weighted_fractional_chromatic_statement : Prop :=
  exists p q : nat,
    [/\ 0 < p, 0 < q &
        forall F : nat, exists G : sgraph,
          [/\ ~ x130_frac_chi_le G F 1, x266_hall_ratio_le G p q &
              forall H : sgraph, has_subgraph G H ->
                exists I : {set H}, stable I /\ q * #|E(H)| <= p * \sum_(v in I) #|N(v)|]].
