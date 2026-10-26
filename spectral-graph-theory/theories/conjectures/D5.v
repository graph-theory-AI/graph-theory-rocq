(** * Spectral.conjectures.D5 — milestone D5 open-problem statements (Spectral)

    Statement-only formalisation (plan v4, namespace [Spectral]) of five deferred open
    problems / conjectures in algebraic & spectral graph theory.  Each node is a single
    [Definition <formal_name> : Prop]; the carrier type is chosen per row (NOT a blanket
    [forall G : sgraph]).  No axioms, no [Admitted], no [Conjecture]/[Parameter].

    Sources (verbatim, from the OPG corpus):
    - triangle_free_strongly_regular_graphs:
        "Is there an eighth triangle free strongly regular graph?"
    - signing_a_graph_to_have_small_magnitude_eigenvalues (SOLVED, Marcus–Spielman–
        Srivastava 2015; stated as a Definition only):
        "If A is the adjacency matrix of a d-regular graph, then there is a symmetric
        signing of A ... so that the resulting matrix has all eigenvalues of magnitude
        at most 2*sqrt(d-1)."
    - are_almost_all_graphs_determined_by_their_spectrum:
        "Are almost all graphs uniquely determined by the spectrum of their adjacency
        matrix?"
    - does_the_symmetric_chromatic_function_distinguish_trees:
        "Do there exist non-isomorphic trees which have the same chromatic symmetric
        function?"
    - laplacian_degrees_of_a_graph:
        "If G is a connected graph on n vertices, then c_k(G) >= d_k(G) for
        k = 1, 2, ..., n-1."

    Spectral matrix vocabulary is imported from [Spectral.foundations.spectral]
    (area-local).  Combinatorial primitives that only ONE row needs (strongly regular
    graphs, Stanley's chromatic symmetric function) are defined locally here. *)

From mathcomp Require Import all_boot.
From GTBase Require Import colourings.
From GraphTheory Require Import sgraph.
From GTBase Require Import base strongly_regular.
From mathcomp Require Import all_algebra perm.
From Spectral Require Import foundations.spectral.
From Spectral Require Import foundations.triangle_free_srg.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Import GRing.Theory Num.Theory.

(** ** Row 1 — Triangle-free strongly regular graphs (Algebraic Graph Theory, OPEN)

    [strongly_regular] is an alias of GTBase's [connected_nontrivial_strongly_regular]
    (A33, base/theories/strongly_regular.v): combinatorial (int/nat, no matrices).
    A graph is strongly regular when it is connected, [k]-regular with [0 < k < n-1],
    every pair of adjacent vertices has exactly [lam] common neighbours, and every pair
    of distinct non-adjacent vertices has exactly [mu] common neighbours.  (Triangle-
    freeness forces [lam = 0].)

    The guards [connected [set: G]], [0 < k] and [k < (#|G|).-1] exclude an edgeless
    graph, a complete graph and a disjoint union of cliques, but NOT the complete
    bipartite graphs K_{n,n} (n >= 2): they are connected, triangle-free and strongly
    regular with (n, 0, n), and imprimitive (their complements are disconnected).  The
    former eight-graph statement of this row was therefore provable with K_{2,2}, ...,
    K_{9,9} (migration/strongly_regular.v, meta/STATEMENT_IMPROVEMENTS.md); the statement
    below states its guards on the parameters directly.  The alias stays: grounding_D5.v
    grounds it, with K_{2,2} as its headline witness. *)
Definition strongly_regular (G : sgraph) : Prop :=
  connected_nontrivial_strongly_regular G.

(** Corpus row: opg:triangle_free_strongly_regular_graphs
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/triangle_free_strongly_regular_graphs/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/triangle_free_strongly_regular_graphs.json
    English statement: (OPG "Triangle free strongly regular graphs": "Is there an eighth triangle
      free strongly regular graph?")
      There is a nonempty simple graph G that is triangle-free and strongly regular with
      parameters (k, lam, mu) where 0 < mu < k, and that is isomorphic to none of the seven known
      triangle-free strongly regular graphs: the five-cycle, the Petersen, Clebsch,
      Hoffman-Singleton, Gewirtz and Higman-Sims graphs, and the (77,16,0,4) M22 graph.
    Definitions: [strongly_regular_parameters G k lam mu] - G is k-regular, every adjacent pair
      has exactly lam common neighbours and every distinct non-adjacent pair exactly mu
      (GTBase, base/theories/strongly_regular.v); [known_triangle_free_srg i] - the seven known
      graphs for i < 7, each checked triangle-free with its parameters
      (spectral-graph-theory/theories/foundations/triangle_free_srg.v); [triangle_free] and
      [common_nbr] are GTBase (base/theories/base.v); [diso] written [≃] is coq-graph-theory.
    Notes: the source excludes degeneracies by mu >= 1, here [0 < mu], and counts exactly seven
      known graphs, which are the PRIMITIVE ones (the graph and its complement connected): Klin
      and Ziv-Av, "Computer Algebra Investigation of Known Primitive Triangle-Free Strongly Regular
      Graphs" (2013), section 2 defines primitivity, section 4 lists these seven, and section 5
      shows that a nonempty imprimitive triangle-free strongly regular graph is complete bipartite
      or a union of disjoint edges.  The guards exclude exactly those two families: disjoint edges
      have mu = 0, and K_{k,k} has mu = k (in a triangle-free strongly regular graph mu <= k, with
      equality only for K_{k,k}).  Without [mu < k], K_{2,2}, ..., K_{9,9} proved the former
      eight-graph encoding (meta/STATEMENT_IMPROVEMENTS.md).  [0 < #|G|] excludes the empty
      graph, which has every parameter triple.  Being isomorphic to none of the seven explicit
      graphs is the source's question itself; no uniqueness theorem is assumed.  A 57-regular
      Moore graph of diameter two would be such a G. *)
Definition triangle_free_strongly_regular_graphs_statement : Prop :=
  exists (G : sgraph) (k lam mu : nat),
    [/\ (0 < #|G|)%N, triangle_free G, strongly_regular_parameters G k lam mu,
        (0 < mu)%N & (mu < k)%N] /\
    forall i : 'I_7, ~ inhabited (G ≃ known_triangle_free_srg i).

(** ** Row 2 — Signing a graph to small-magnitude eigenvalues (Graph Theory, SOLVED) *)

(** Corpus row: opg:signing_a_graph_to_have_small_magnitude_eigenvalues
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/signing_a_graph_to_have_small_magnitude_eigenvalues/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/signing_a_graph_to_have_small_magnitude_eigenvalues.json
    English statement: (OPG "Signing a graph to have small magnitude eigenvalues"; the
      Bilu-Linial signing conjecture, solved by Marcus, Spielman and Srivastava in 2015)
      Over any real-closed field R, for every simple graph G that is d-regular with d >= 2
      and has at least one vertex, there is a matrix S indexed by the vertices of G which is
      symmetric, has entry +1 or -1 at every pair of adjacent vertices and entry 0 at every
      other pair — a symmetric signing of the adjacency matrix of G — and all of whose
      eigenvalues x satisfy |x| <= 2 times the square root of d - 1.
    Definitions: [is_signing G S] — S is symmetric, carries +1 or -1 on every edge and 0 off
      the edges (spectral-graph-theory/theories/foundations/spectral.v);
      [spectral_radius_le A b] — every eigenvalue of A has absolute value at most b
      (foundations/spectral.v); [adjmx R G] — the adjacency matrix of G over R, vertices
      indexed through [enum_val] (foundations/spectral.v); [regular G d] is GTBase
      (base/theories/base.v); [rcfType], [eigenvalue] and [Num.sqrt] are MathComp.
    Notes: eigenvalues are taken in an abstract real-closed field R and the statement is
      universally quantified over R, because mathcomp.field / [algC] is not available in
      this development. [d.-1] is the nat predecessor, so the guard [2 <= d] is
      load-bearing: for d <= 1 the bound collapses to 0, which no signing of a non-empty
      regular graph can meet, and the Marcus-Spielman-Srivastava result is stated for
      d >= 2. The corpus status of the row is solved; only the statement is formalized
      here, there is no proof. *)
Definition signing_a_graph_to_have_small_magnitude_eigenvalues_statement : Prop :=
  forall (R : rcfType) (G : sgraph) (d : nat),
    regular G d -> (2 <= d)%N -> (0 < #|G|)%N ->
    exists S : 'M[R]_(#|G|),
      is_signing S /\ spectral_radius_le S (2%:R * Num.sqrt (d.-1)%:R).

(** ** Row 3 — Almost all graphs determined by their spectrum (Graph Theory, OPEN) *)

(** Corpus row: opg:are_almost_all_graphs_determined_by_their_spectrum
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/are_almost_all_graphs_determined_by_their_spectrum/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/are_almost_all_graphs_determined_by_their_spectrum.json
    English statement: (OPG "Are almost all graphs determined by their spectrum?")
      For every positive integer m there is an N such that, for every n >= N, the number of
      labelled graphs on n vertices that are not determined by their adjacency spectrum is
      at most a 1/m fraction of the total number of labelled graphs on n vertices; in other
      words the proportion of labelled n-vertex graphs determined by their spectrum tends
      to 1.
    Definitions: [total_count n] — the number of labelled simple graphs on n vertices, a
      labelled graph being a symmetric irreflexive boolean relation on ['I_n]
      (spectral-graph-theory/theories/foundations/spectral.v: [ladj], [is_lgraph],
      [lgraphs]); [determined_count n] — how many of those are determined by their spectrum,
      that is satisfy [lspec_determined]: every labelled n-vertex graph with the same
      adjacency characteristic polynomial over [int] ([lcospectral], [ladjmx]) is obtained
      from it by a permutation relabelling ([liso]) (foundations/spectral.v).
    Notes: the corpus row is a Problem; it is formalized affirmatively as a density-one
      limit. The limit is written over nat with no real numbers: m times the number of
      undetermined graphs is at most the total. The nat subtraction is harmless because
      [determined_count n <= total_count n], and [total_count n >= 1] always (the edgeless
      graph), so the inequality is not vacuous. Spectral determination is taken inside the
      labelled model — cospectrality is equality of the characteristic polynomial over the
      integers and isomorphism is permutation relabelling, rather than [diso] on [sgraph] —
      because the density has to be a ratio of finite cardinalities. *)
Definition are_almost_all_graphs_determined_by_their_spectrum_statement : Prop :=
  forall m : nat, (0 < m)%N ->
    exists N : nat, forall n : nat, (N <= n)%N ->
      (m * (total_count n - determined_count n) <= total_count n)%N.

(** ** Row 4 — Symmetric chromatic function distinguishing trees (Alg. Graph Th., OPEN)

    Stanley's CHROMATIC SYMMETRIC function (a generating function over proper colourings,
    NOT eigenvalues).  [csf_coeff G k a] counts the proper [k]-colourings of [G] whose
    colour-class sizes are exactly [a] (the monomial-symmetric-function data of X_G);
    [same_csf G H] means [G] and [H] have equal chromatic symmetric function.

    "Do there exist non-isomorphic TREES with the same chromatic symmetric function?" *)
Definition proper_colb (G : sgraph) (k : nat) (c : {ffun G -> 'I_k}) : bool :=
  colourings.proper_colouring c.

Definition csf_coeff (G : sgraph) (k : nat) (a : 'I_k -> nat) : nat :=
  #|[set c : {ffun G -> 'I_k} |
       proper_colb c && [forall b : 'I_k, #|[set x | c x == b]| == a b]]|.

Definition same_csf (G H : sgraph) : Prop :=
  forall (k : nat) (a : 'I_k -> nat), csf_coeff G a = csf_coeff H a.

(** Corpus row: opg:does_the_symmetric_chromatic_function_distinguish_trees
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/does_the_symmetric_chromatic_function_distinguish_trees/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/does_the_symmetric_chromatic_function_distinguish_trees.json
    English statement: (OPG "Does the chromatic symmetric function distinguish between
      trees?", Stanley 1995)
      There exist two trees that are not isomorphic and yet have the same chromatic
      symmetric function, that is: for every number of colours k and every prescribed vector
      a of colour-class sizes, the two trees have exactly the same number of proper
      k-colourings whose colour classes have the sizes prescribed by a.
    Definitions: [proper_colb G k c] — boolean test that the colouring c of the vertices of
      G by ['I_k] gives different colours to adjacent vertices (D5.v); [csf_coeff G k a] —
      the number of proper k-colourings c of G such that, for every colour b, exactly [a b]
      vertices receive colour b (D5.v); [same_csf G H] — [csf_coeff] agrees on G and H for
      every k and every a (D5.v); [is_tree [set: T]] and [diso] written [≃] are
      coq-graph-theory.
    Notes: the chromatic symmetric function is encoded by its monomial-basis data (the
      counts of proper colourings sorted by colour-class-size vector) rather than as a
      symmetric-function object, which avoids a symmetric-function library; this is
      equivalent for the purpose of comparing two graphs. The corpus row is the Problem "Do
      there exist non-isomorphic trees which have the same chromatic symmetric function?",
      formalized affirmatively as an existence statement, so a proof of this Definition
      would refute Stanley's conjecture that the chromatic symmetric function distinguishes
      trees — which is the expected answer. *)
Definition does_the_symmetric_chromatic_function_distinguish_tr_statement : Prop :=
  exists T1 T2 : sgraph,
    [/\ is_tree [set: T1], is_tree [set: T2],
        ~ inhabited (T1 ≃ T2) & same_csf T1 T2].

(** ** Row 5 — Laplacian degrees of a graph (Algebraic Graph Theory, OPEN) *)

(** Corpus row: opg:laplacian_degrees_of_a_graph
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/laplacian_degrees_of_a_graph/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/laplacian_degrees_of_a_graph.json
    English statement: (OPG "Laplacian Degrees of a Graph"; a Brouwer-Haemers-style
      Laplacian-degree majorisation, the corpus row carries no attribution)
      Over any real-closed field R: let G be a connected simple graph with at least one
      vertex, let s list the eigenvalues of the Laplacian matrix of G in non-increasing
      order with multiplicity, and let d list the vertex degrees of G in non-increasing
      order. Then for every index k strictly below |V(G)| - 1, the k-th entry of s is at
      least the k-th entry of d — that is, c_k(G) >= d_k(G) for k = 1, ..., n - 1 in the
      1-based numbering of the source.
    Definitions: [Lapmx R G] — the combinatorial Laplacian [degmx G - adjmx G] of G over R,
      with [adjmx] the adjacency matrix and [degmx] the diagonal degree matrix
      (spectral-graph-theory/theories/foundations/spectral.v); [is_spectrum A s] — s has
      length n, is sorted non-increasingly, and the characteristic polynomial of A factors
      as the product of [X - x] over the entries x of s, so s is the spectrum with
      multiplicities (foundations/spectral.v); [is_deg_sorted G d] — d is a non-increasing
      permutation of the degree sequence [degseq G] (foundations/spectral.v); [connected] is
      coq-graph-theory.
    Notes: quantified over an abstract real-closed field R and over every s and d meeting
      those specifications; such an s and such a d are unique (the sorting constraint pins
      the order), so the universal form is faithful. Indices are 0-based in Rocq, so the
      source range k = 1, ..., n - 1 becomes [k < (#|G|).-1] on [s`_k] and [d`_k]. Degrees
      are cast into R with [_%:R] in order to be compared with eigenvalues. The statement is
      an implication on [is_spectrum], hence vacuous for a field R in which the Laplacian
      characteristic polynomial does not split; it does split over every real-closed field,
      but that fact is not proved in this development. *)
Definition laplacian_degrees_of_a_graph_statement : Prop :=
  forall (R : rcfType) (G : sgraph),
    connected [set: G] -> (0 < #|G|)%N ->
    forall s : seq R, is_spectrum (Lapmx R G) s ->
    forall d : seq nat, is_deg_sorted G d ->
    forall k : nat, (k < (#|G|).-1)%N -> (nth 0%N d k)%:R <= nth 0 s k.
