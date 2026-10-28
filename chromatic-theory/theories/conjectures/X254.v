(** * Chromatic.conjectures.X254 -- wave X254: induced subdivisions, odd holes, ISK4-free graphs, Tomescu's colouring
    count and odd multiholes (2026-10-28)

    An eight-row wave under the prospective contract of meta/faithfulness_policy.json (hard lint, classified local
    helpers, grounding certificates, an independent verifier).  Rows:
    studies:std_scott_s_conjecture_induced_subdivisions_and_chi (Scott),
    studies:std_gy_rf_s_odd_hole_boundedness_conjecture (Gyarfas),
    studies:std_trotignon_vu_kovi_conjecture_isk4_triangle_free (Trotignon and Vuskovic), the four Tomescu rows
    studies:std_tomescu_s_conjecture_maximum_number_of_proper_k_529 (the canonical statement) and its synonyms
    ..._k_colorin, ..._proper_k and ..._proper_k_530, and arxiv:2202.09118#01 (odd multiholes).  Shared vocabulary is
    reused: [chi_bounded_class] (GTBase.chi_bounding), [poly_chi_bounded] (Chromatic.foundations.chi_bounding),
    [induced_subdivision] (GTBase.induced_subdivisions), [hole] (GTBase.induced_cycles), [proper_colouring]
    (GTBase.colourings), [triangle_free] (GTBase.base) and the library chromatic and clique numbers, [clique] and
    [connected].  The sources are the Mac's deposit coordination/sources/x254-source-mac-20261028 (versioned e-prints,
    TeX line numbers below); the grounding certificates are in grounding_X254.v. *)

From GTBase Require Export base.
From Chromatic.foundations Require Import chi_bounding.
(* GTBase.chi_bounding after Chromatic's: [chi_bounded_class] is the canonical GTBase name. *)
From GTBase Require Import induced_cycles induced_subdivisions chi_bounding colourings.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local x254 vocabulary ************************************************* *)

(** The 2-CORE of G (arXiv:1712.06067v3, TeX l.93): what remains after repeatedly deleting vertices of degree at most
    one.  Encoded as the union of all vertex sets in which every vertex has at least two neighbours inside the set: such
    a union again has that property, so it is the largest one, and the deletion process never removes a vertex of such
    a set (all of the set is still present when its first vertex would go, and that vertex then has degree >= 2), while
    what it leaves has minimum degree >= 2 or is empty. *)
Definition x254_two_core (G : sgraph) : {set G} :=
  \bigcup_(S : {set G} | [forall v in S, 2 <= #|N(v) :&: S|]) S.

(** A k-MULTIHOLE IN WHICH ALL THE CYCLES HAVE ODD LENGTH (arXiv:2202.09118v1, TeX l.70 and l.97-98): k holes (induced
    cycles of length at least four), each of odd length, pairwise vertex-disjoint and with no edge between two of them,
    i.e. an induced subgraph with k components, each an odd cycle of length at least five. *)
Definition x254_odd_multihole (G : sgraph) (k : nat) : Prop :=
  exists c : 'I_k -> seq G,
    (forall i : 'I_k, hole (c i) /\ odd (size (c i))) /\
    (forall (i j : 'I_k) (x y : G), i != j -> x \in c i -> y \in c j -> x != y /\ ~~ (x -- y)).

(** ** Statements ************************************************************ *)

(** Corpus row: studies:std_scott_s_conjecture_induced_subdivisions_and_chi
    Site: none
    Review: none
    English statement: (Scott, "Scott's Conjecture (Induced Subdivisions and Chi-Boundedness)")
      For every graph H, the class of graphs which do not contain any subdivision of H as an induced subgraph is
      chi-bounded.
    Definitions: [induced_subdivision H G] - G has an induced subgraph isomorphic to a subdivision of H, every edge of
      H a path of length at least one (GTBase.induced_subdivisions); [chi_bounded_class F] - one f : nat -> nat with
      chi(G) <= f(omega(G)) for every G in F (GTBase.chi_bounding).
    Notes: H itself counts as a subdivision of H, as in the sources (2602.11990v1 keeps unsubdivided edges).
      Literature status: REFUTED before the pin (pinned status open; CORPUS_FEEDBACK): Pawlik, Kozik, Krawczyk,
      Lason, Micek, Trotter and Walczak, arXiv:1209.1595v5, construct triangle-free families of segments with
      chromatic number above every k (Theorem 1) and observe (TeX l.108-109) that this disproves the conjecture of
      Scott: take H the 1-subdivision of a non-planar graph, no subdivision of which is a segment intersection graph.
      The refutation is of the row for all H; fixed-H instances can hold (Cameron, Sintiari and Spirkl,
      arXiv:2602.11990v1).  Encoded as stated; the row is false at the pin. *)
Definition scott_induced_subdivision_chi_bounded_statement : Prop :=
  forall H : sgraph, chi_bounded_class (fun G : sgraph => ~ induced_subdivision H G).

(** Corpus row: studies:std_gy_rf_s_odd_hole_boundedness_conjecture
    Site: none
    Review: none
    English statement: (Gyarfas, "Gyarfas' Odd Hole chi-Boundedness Conjecture")
      For all integers k, l > 0 there exists n(k, l) such that every graph G with no clique of cardinality more than k
      and no odd hole of length more than l has chromatic number at most n(k, l).
    Definitions: [hole c] - c is a chordless cycle of G on at least four vertices (GTBase.induced_cycles), of length
      size c; omega(G), chi(G) - the library clique and chromatic numbers.
    Notes: "no clique of cardinality more than k" is omega(G) <= k, and "no odd hole of length more than l" is: every
      hole of odd length has length at most l.  k and l are positive, as stated.
      Literature status: proved before the pin (pinned status open; CORPUS_FEEDBACK): Chudnovsky, Scott, Seymour and
      Spirkl, Induced subgraphs of graphs with large chromatic number. VIII. Long odd holes, arXiv:1701.07217v3,
      statement 1.3 (TeX l.86-88: for all kappa, ell >= 0 some c such that omega(G) <= kappa and chi(G) > c give an
      odd hole of length at least ell; "In this paper we prove the third", l.90-91); the row is 1.3 with
      ell = l + 1.  Part III (arXiv:1506.02232v2) proves the version for all holes and part I the odd-hole-free
      one; neither is this row. *)
Definition gyarfas_long_odd_hole_chi_bounded_statement : Prop :=
  forall k l : nat, 0 < k -> 0 < l -> exists N : nat,
    forall G : sgraph, ω([set: G]) <= k ->
      (forall c : seq G, hole c -> odd (size c) -> size c <= l) ->
      χ([set: G]) <= N.

(** Corpus row: studies:std_trotignon_vu_kovi_conjecture_isk4_triangle_free
    Site: none
    Review: none
    English statement: (Trotignon and Vuskovic, "Trotignon-Vuskovic conjecture ({ISK4, triangle}-free
      3-colourability)")
      If G is {ISK4, triangle}-free, then chi(G) <= 3.
    Definitions: [induced_subdivision 'K_4 G] - G has an induced subgraph isomorphic to a subdivision of K_4
      (GTBase.induced_subdivisions); [triangle_free G] - no three mutually adjacent vertices (GTBase.base).
    Notes: an ISK4 is a graph isomorphic to a subdivision of K_4, and ISK4-free means no induced subgraph is an ISK4
      (arXiv:1704.08104v1, TeX l.102).
      Literature status: proved before the pin (pinned status open; CORPUS_FEEDBACK): Chudnovsky, Liu, Schaudt,
      Spirkl, Trotignon and Vuskovic, arXiv:1704.08104v1, Conjecture 1 (TeX l.107-110) and "The main result of the
      present paper is the proof of Conjecture 1" (l.114). *)
Definition isk4_triangle_free_three_colourable_statement : Prop :=
  forall G : sgraph, ~ induced_subdivision 'K_4 G -> triangle_free G -> χ([set: G]) <= 3.

(** Corpus row: studies:std_tomescu_s_conjecture_maximum_number_of_proper_k_529
    Site: none
    Review: none
    English statement: (Tomescu, "Tomescu's conjecture (maximum number of proper k-colourings)")
      For every connected graph G on n vertices with chromatic number k >= 4, P_G(k) <= k!(k-1)^(n-k), with equality if
      and only if the 2-core of G is a k-clique (i.e., G is formed by attaching a tree to each vertex of the complete
      graph K_k).
    Definitions: P_G(k) - #|[set f : {ffun G -> 'I_k} | proper_colouring f]|, the proper colourings of G with the
      LABELLED colours 'I_k (GTBase.colourings); [x254_two_core G] (this file); [clique S] and [connected S]
      (coq-graph-theory).
    Notes: "the 2-core of G is a k-clique" is: the 2-core induces K_k, a clique with k vertices.  P_G(k) counts maps
      into the labelled set [k], as in Fox, He and Manners (arXiv:1712.06067v3).  The canonical row of four (the
      three others are synonyms, below).
      Literature status: proved before the pin (pinned status open; CORPUS_FEEDBACK): Fox, He and Manners,
      arXiv:1712.06067v3, Theorem 1 (TeX l.98-105), after Knox and Mohar (k = 4, 5, arXiv:1710.06535v1); the guard
      k >= 4 is load-bearing (odd cycles at k = 3, l.95; at k = 2 every connected bipartite graph attains the bound,
      grounding_X254.v).  The natural-number subtractions are exact: k - 1 since k >= 4, and #|G| - k since
      chi(G) = k forces at least k vertices. *)
Definition tomescu_connected_colouring_count_statement : Prop :=
  forall (G : sgraph) (k : nat), 4 <= k -> connected [set: G] -> χ([set: G]) = k ->
    #|[set f : {ffun G -> 'I_k} | proper_colouring f]| <= k`! * (k - 1) ^ (#|G| - k) /\
    (#|[set f : {ffun G -> 'I_k} | proper_colouring f]| = k`! * (k - 1) ^ (#|G| - k) <->
       clique (x254_two_core G) /\ #|x254_two_core G| = k).

(** Corpus row: studies:std_tomescu_s_conjecture_maximum_number_of_k_colorin
    Site: none
    Review: none
    English statement: (Tomescu, "Tomescu's Conjecture (maximum number of k-colorings)")
      Let G be a connected k-chromatic graph with k >= 4. Then G has at most k!(k-1)^(|G|-k) k-colourings. Moreover,
      the extremal graphs are precisely the graphs obtained from K_k by adding trees rooted at each vertex of the
      clique.
    Definitions: [tomescu_connected_colouring_count_statement] (above).
    Notes: a synonym of the canonical Tomescu row (_529).  "k-chromatic" is chi(G) = k, the k-colourings are P_G(k),
      and "the extremal graphs" are those attaining the bound.  For connected G with chi(G) = k >= 4, "obtained from K_k
      by adding trees rooted at each vertex" is "the 2-core is a k-clique", as the canonical text says ("i.e.") and
      arXiv:1712.06067v3 (TeX l.93: "Equivalently"): deleting leaves strips each attached tree down to its root, the
      clique vertices keeping degree >= k - 1 >= 3; conversely the deleted vertices form a forest, each component of
      which a connected G joins to the core by exactly one edge.  Literature status as the canonical row. *)
Definition tomescu_colouring_count_rooted_trees_statement : Prop :=
  tomescu_connected_colouring_count_statement.

(** Corpus row: studies:std_tomescu_s_conjecture_maximum_number_of_proper_k
    Site: none
    Review: none
    English statement: (Tomescu, "Tomescu's conjecture (maximum number of proper k-colourings)")
      Let G be a connected k-chromatic graph with k >= 4. Then G has at most k!(k-1)^(|G|-k) k-colourings. Moreover,
      the extremal graphs are precisely the graphs obtained from K_k by adding trees rooted at each vertex of the
      clique.
    Definitions: [tomescu_connected_colouring_count_statement] (above).
    Notes: the same pinned text as the ..._k_colorin row; a synonym of the canonical Tomescu row (_529), read as that
      row is.  Literature status as the canonical row. *)
Definition tomescu_colouring_count_rooted_trees_duplicate_statement : Prop :=
  tomescu_connected_colouring_count_statement.

(** Corpus row: studies:std_tomescu_s_conjecture_maximum_number_of_proper_k_530
    Site: none
    Review: none
    English statement: (Tomescu, "Tomescu's conjecture (maximum number of proper k-colourings)")
      If G is a connected graph on n vertices and chi(G) = k >= 4, then P_G(k) <= k!(k-1)^(n-k), with equality if and
      only if the 2-core of G is a k-clique.
    Definitions: [tomescu_connected_colouring_count_statement] (above).
    Notes: the canonical row's text without its "i.e." gloss; a synonym of the canonical Tomescu row (_529).
      Literature status as the canonical row. *)
Definition tomescu_colouring_count_two_core_duplicate_statement : Prop :=
  tomescu_connected_colouring_count_statement.

(** Corpus row: arxiv:2202.09118#01
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/2202.09118__01/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/2202.09118__01.json
    English statement: (Chudnovsky, Scott, Seymour and Spirkl, Polynomial bounds for chromatic number VII. Disjoint
      holes, arXiv:2202.09118v1, open problem)
      For any integer k >= 1, is the class of graphs with no k-multihole in which all the cycles have odd length
      polynomially chi-bounded?
    Definitions: [x254_odd_multihole G k] (this file); [poly_chi_bounded F] - naturals c and d, chosen before the
      graphs of F, with chi(G) <= c * omega(G)^d (Chromatic.foundations.chi_bounding).
    Notes: encoded in its affirmative form.  The source (TeX l.101-104) proves the class chi-bounded ([9]) and says
      polynomial chi-boundedness is not proved there; its Theorem 1.1 (l.110-113) allows components of length four OR
      odd, a different exclusion, not encoded.  Literature status: open at the pin (pinned status open). *)
Definition odd_multihole_free_poly_chi_bounded_statement : Prop :=
  forall k : nat, 1 <= k -> poly_chi_bounded (fun G : sgraph => ~ x254_odd_multihole G k).
