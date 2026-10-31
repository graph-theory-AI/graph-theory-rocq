(** * Minor.conjectures.X271 -- v2 rows: the odd Hadwiger conjecture (two phrasings), Seymour's H-Hadwiger
    conjecture, Hajos' conjecture at five *)

From GTBase Require Import base.
From Minor.foundations Require Import containment.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** X271 vocabulary *****************************************************)

(** G contains H as an odd minor, in the sources' tree model (Kuhn, Sauermann, Steiner and Wigderson,
    arXiv:2512.20392v1, main.tex l.182-187; Steiner, arXiv:2203.02766v1, main.tex l.124-126): pairwise disjoint
    nonempty branch sets [B x] and one 2-colouring [sigma] such that every branch set is connected through its
    BICHROMATIC edges, and every edge x y of H has a MONOCHROMATIC edge of G between [B x] and [B y].  A set is
    connected through its bichromatic edges iff it spans a tree of G whose edges are properly coloured (a spanning
    tree of those edges), so these are the sources' trees.  Other edges of G inside a branch set are unconstrained:
    a branch set need not induce a bipartite subgraph. *)
Definition x271_odd_minor_tree_model (G H : sgraph) : Prop :=
  exists (B : H -> {set G}) (sigma : G -> bool),
    [/\ forall x : H, B x != set0,
        forall (x : H) (u v : G), u \in B x -> v \in B x ->
          connect (fun a b : G => [&& a \in B x, b \in B x, a -- b & sigma a != sigma b]) u v,
        forall x y : H, x != y -> [disjoint B x & B y] &
        forall x y : H, x -- y ->
          exists u v : G, [/\ u \in B x, v \in B y, u -- v & sigma u == sigma v]].

(** ** X271 statements *****************************************************)

(** Corpus row: studies:std_odd_hadwiger_conjecture
    Site: none
    Review: none
    English statement: (Gerards and Seymour; studies slice of the corpus, record arXiv:2512.20392)
      Let G be a graph.  If chi(G) >= t, then G has K_t as an odd minor.  Equivalently, if G does not have K_t as
      an odd minor, then chi(G) < t.
    Definitions: [x271_odd_minor_tree_model G H] - disjoint nonempty branch sets, each connected through its
      bichromatic edges under one 2-colouring of G, with a monochromatic edge of G between the branch sets of every
      edge of H (this file); [χ([set: G])] - the chromatic number of G (coq-graph-theory's [chi_mem]); ['K_t] - the
      complete graph on t vertices (coq-graph-theory).
    Notes: encoded as stated, the first sentence (the second is its contrapositive); pinned status open, but FALSE
      at the pin.  The statement is Conjecture 1.2 of Kuhn, Sauermann, Steiner and Wigderson (arXiv:2512.20392v1,
      23 December 2025, main.tex l.188-191), after their odd-minor definition (l.182-187): vertex-disjoint trees
      T_1, ..., T_t of G, a proper 2-colouring of each tree, and for every pair a monochromatic edge of G.  Their
      Theorem 1.3 (l.200-202) gives, for every sufficiently large t, a graph with chi(G) >= t and no odd K_t
      minor.  They record t <= 4 as known (Catlin) and t = 5 only as announced (Guenin).  The helper is the tree
      model exactly: a branch set spans a properly coloured tree iff it is connected through its bichromatic edges.
      X218's [x218_odd_minor] (the blocked row arxiv:2308.15721#00) asks EVERY edge of G inside a branch set to be
      bichromatic; each of its models is a tree model (a spanning tree of a connected branch set), the converse is
      not established, so X271 does not reuse it.  The refutation holds in both models.  The instances t = 0 (no
      branch set) and t = 1 (one vertex as its branch set) hold.  The status correction is a separate corpus item. *)
Definition odd_hadwiger_chromatic_odd_minor_statement : Prop :=
  forall (t : nat) (G : sgraph), t <= χ([set: G]) -> x271_odd_minor_tree_model G 'K_t.

(** Corpus row: studies:std_odd_hadwiger_conjecture_411
    Site: none
    Review: none
    English statement: (Gerards and Seymour; studies slice of the corpus, records arXiv:2109.02302, 2203.02766 and
      2312.17130)
      For every integer t >= 2, if G is a graph not containing an odd K_t-minor, then G is properly
      (t-1)-colorable.
    Definitions: [x271_odd_minor_tree_model G H] - disjoint nonempty branch sets, each connected through its
      bichromatic edges under one 2-colouring of G, with a monochromatic edge of G between the branch sets of every
      edge of H (this file); [χ([set: G])] - the chromatic number of G (coq-graph-theory's [chi_mem]); ['K_t] - the
      complete graph on t vertices (coq-graph-theory).
    Notes: encoded as stated; pinned status open, but FALSE at the pin (Kuhn, Sauermann, Steiner and Wigderson,
      arXiv:2512.20392v1, Theorem 1.3, main.tex l.200-202).  The wording is Conjecture 1.2 of Steiner
      (arXiv:2203.02766v1, main.tex l.139-141), whose odd K_t-expansion (l.124-126) is the tree model of the
      helper: its "exactly one additional edge" between two trees, in a subgraph of G, is the helper's
      monochromatic edge of G between two branch sets (choose one per pair).  The same model is in
      arXiv:2109.02302v1 (main.tex l.79-86); arXiv:2312.17130v2 (main.tex l.91-97) contracts an edge
      cut of a subgraph G' of G instead, the same relation (G' = the trees and the connecting edges, the cut given
      by the colouring).  "Properly (t-1)-colorable" is chi(G) <= t - 1, written t.-1, exact since t >= 2.  The
      guard 2 <= t is the source's and is not load-bearing: every graph has an odd K_0 minor, and a graph with no
      odd K_1 minor has no vertex.  This row and studies:std_odd_hadwiger_conjecture are one conjecture: for
      t >= 2 each instance is the contrapositive of the other's, and that row's instances t <= 1 hold. *)
Definition odd_hadwiger_odd_minor_free_colourable_statement : Prop :=
  forall (t : nat) (G : sgraph), 2 <= t -> ~ x271_odd_minor_tree_model G 'K_t -> χ([set: G]) <= t.-1.

(** Corpus row: studies:std_h_hadwiger_conjecture
    Site: none
    Review: none
    English statement: (Seymour; studies slice of the corpus, record arXiv:2304.04246)
      H-minor-free graphs are (v(H)-1)-colorable.
    Definitions: [minor G H] - H is a minor of G: a map from the vertices of G to the vertices of H or none, with
      nonempty connected preimages and an edge of G between the preimages of every edge of H (coq-graph-theory's
      [minor.v]); [#|H|] - v(H); [χ([set: G])] - the chromatic number of G (coq-graph-theory's [chi_mem]).
    Notes: encoded as stated, for every H; pinned status open.  The statement is Conjecture 2 of Fischer and
      Steiner (arXiv:2304.04246v1, text l.69-72), where H is "a specified, possibly non-complete graph H on t
      vertices"; Hadwiger's conjecture implies it "for every H" (l.73), and K_(v(H)-1) shows the bound is best
      possible.  Over all H it is equivalent to Hadwiger's conjecture (bm:bm-041, X214's
      [hadwiger_chromatic_clique_minor_statement]): H = K_t gives Hadwiger at t, and conversely H is a subgraph of
      K_(v(H)), so a graph with no H minor has no K_(v(H)) minor.  Known cases (l.76-87): forests, spanning
      subgraphs of the Petersen graph, K_(3,3), K_(2,t), K_(3,4).  The truncation of #|H|.-1 matters only when H has
      no vertex; then every G has H as a minor (the map sending every vertex to none), so the hypothesis fails and
      the instance holds. *)
Definition h_hadwiger_minor_free_colourable_statement : Prop :=
  forall H G : sgraph, ~ minor G H -> χ([set: G]) <= #|H|.-1.

(** Corpus row: studies:std_haj_s_conjecture_k_5
    Site: none
    Review: none
    English statement: (Hajos; studies slice of the corpus, record arXiv:2605.10112)
      Every 5-chromatic graph contains a subdivision of K_5.
    Definitions: [χ([set: G])] - the chromatic number of G (coq-graph-theory's [chi_mem]); [has_subdivision G H] -
      G contains a subdivision of H: injective branch vertices and internally disjoint paths for the edges of H,
      not necessarily induced (minor-theory/theories/foundations/containment.v); ['K_5] - the complete graph on five
      vertices (coq-graph-theory).
    Notes: encoded as stated; pinned status open.  Hajos' conjecture is stated by Girao, Illingworth, Mohar,
      Norin, Steiner, Tamitegama, Tan, Wood and Yip (arXiv:2605.10112v1, main.tex l.183-185) for every t: a graph
      with chi(G) >= t contains a subdivision of K_t as a subgraph; it is open for t in {5, 6} and false for every
      t >= 7 (Catlin).  "5-chromatic" is read as
      chi(G) = 5, as X214 reads bm:bm-042; the form chi(G) >= 5 is equivalent: deleting vertices one at a time
      lowers chi by at most one each, so a graph with chi(G) >= 5 has a subgraph with chi = 5, and a subdivision in
      a subgraph is one in G.  The paper's results (a dominating K_5 model, a subdivision of K_5 or of a related
      graph) are progress, not a proof.  bm:bm-042 (X214) at k = 5 is this row: a candidate edge, not in this
      wave. *)
Definition hajos_k5_subdivision_statement : Prop :=
  forall G : sgraph, χ([set: G]) = 5 -> has_subdivision G 'K_5.
