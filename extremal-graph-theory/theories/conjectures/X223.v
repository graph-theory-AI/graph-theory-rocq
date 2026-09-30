(** * Extremal.conjectures.X223 -- Sidorenko / sparse-pair / Erdos-Hajnal / induced-Turan rows (wave X223, 2026-09-23) *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local x223 vocabulary ***********************************************

    Four groups of paper-local notions, none of which exists in
    coq-graph-theory / GTBase:
    (a) epsilon-bounded graphs and sparse / anticomplete PAIRS
        (Chudnovsky-Fox-Scott-Seymour-Spirkl, arXiv:1810.00058);
    (b) homomorphism COUNTS of oriented graphs and the directed Sidorenko
        property (Fox-Himwich-Mani-Zhou, arXiv:2210.16971);
    (c) the VC-dimension of the neighbourhood set system
        (Fox-Pach-Suk, arXiv:1912.02342);
    (d) (c,t)-sparse host graphs (Fox-Nenadov-Pham, arXiv:2405.05902).
    Cliques, stable sets, induced-freeness, edge sets and closed neighbourhoods
    all come from coq-graph-theory / GTBase. *)

(** *** (a) epsilon-bounded graphs, anticomplete and c-sparse pairs *)

(** [G] is eps-bounded for eps = p/d: every CLOSED neighbourhood has fewer than
    eps * |V(G)| vertices. *)
Definition x223_eps_bounded (G : sgraph) (p d : nat) : Prop :=
  forall v : G, d * #|N[v]| < p * #|G|.

(** [A] and [B] are disjoint with no edge between them. *)
Definition x223_anticomplete (G : sgraph) (A B : {set G}) : Prop :=
  [disjoint A & B] /\ forall a b : G, a \in A -> b \in B -> a -- b -> False.

(** The number of edges between [A] and [B], counted as the ordered pairs
    (u,v) in A x B with u adjacent to v.  For DISJOINT A and B this is exactly
    |E(A,B)|; for general A and B it is the convention used by the (c,t)-sparse
    definition of arXiv:2405.05902. *)
Definition x223_edges_between (G : sgraph) (A B : {set G}) : nat :=
  #|[set uv : G * G | (uv.1 \in A) && (uv.2 \in B) && (uv.1 -- uv.2)]|.

(** [(A,B)] is a c-sparse pair for c = a/b: disjoint, with at most c|A||B|
    edges between them. *)
Definition x223_sparse_pair (G : sgraph) (A B : {set G}) (a b : nat) : Prop :=
  [disjoint A & B] /\
  b * x223_edges_between A B <= a * (#|A| * #|B|).

(** *** (b) oriented graphs, homomorphism counts, directed Sidorenko *)

(** A homomorphism from [B] to the single directed edge: a 2-colouring under
    which every arc runs from the 0-side to the 1-side. *)
Definition x223_hom_to_arc (B : diGraph) : Prop :=
  exists f : B -> bool, forall x y : B, x -- y -> f x = false /\ f y = true.

(** The underlying undirected graph of [B] is bipartite. *)
Definition x223_bipartite_dg (B : diGraph) : Prop :=
  exists f : B -> bool, forall x y : B, x -- y -> f x != f y.

(** The underlying undirected graph of an ORIENTED digraph contains a cycle:
    some non-empty vertex set spans at least as many arcs as it has vertices
    (the matroid characterisation "G is a forest iff e(G[S]) < |S| for every
    non-empty S"). *)
Definition x223_und_cyclic (B : diGraph) : Prop :=
  exists S : {set B},
    0 < #|S| /\ #|S| <= #|[set uv : B * B | [&& uv.1 \in S, uv.2 \in S & uv.1 -- uv.2]]|.

(** The number of digraph homomorphisms [B -> D] (arc-preserving maps, not
    necessarily injective): the [hom(B,D)] of the homomorphism-density
    t(B,D) = hom(B,D)/|V(D)|^{|V(B)|}. *)
Definition x223_dhom_count (B D : diGraph) : nat :=
  #|[set f : {ffun B -> D} | [forall x, [forall y, (x -- y) ==> (f x -- f y)]]]|.

(** [B] has the DIRECTED SIDORENKO PROPERTY: t(B,D) >= t(arc,D)^{e(B)} for every
    oriented [D], where t(arc,D) = e(D)/|V(D)|^2 is the arc density.  Cleared of
    all division, this is
      e(D)^{e(B)} * |V(D)|^{|V(B)|} <= hom(B,D) * |V(D)|^{2 e(B)}. *)
Definition x223_directed_sidorenko (B : diGraph) : Prop :=
  forall D : diGraph,
    oriented D ->
    num_edges D ^ num_edges B * #|D| ^ #|B|
      <= x223_dhom_count B D * #|D| ^ (2 * num_edges B).

(** *** (c) VC-dimension of the neighbourhood set system *)

(** [S] is SHATTERED by the open neighbourhoods: every subset of [S] is cut out
    of [S] by the neighbourhood of some vertex. *)
Definition x223_shattered (G : sgraph) (S : {set G}) : Prop :=
  forall T : {set G}, T \subset S -> exists v : G, N(v) :&: S = T.

(** The VC-dimension of [G] is at most [d]: no shattered set exceeds [d]. *)
Definition x223_vc_dim_leq (G : sgraph) (d : nat) : Prop :=
  forall S : {set G}, x223_shattered S -> #|S| <= d.

(** *** (d) (c,t)-sparse host graphs *)

(** [Gamma] is (c,t)-sparse for c = a/b: any two (not necessarily disjoint)
    vertex sets of size at least [t] span at most (1-c)|A||B| edges. *)
Definition x223_ct_sparse (Gamma : sgraph) (a b t : nat) : Prop :=
  forall A B : {set Gamma}, t <= #|A| -> t <= #|B| ->
    b * x223_edges_between A B <= (b - a) * (#|A| * #|B|).

(** ** X223 statements *****************************************************)

(** Corpus row: arxiv:2210.16971#00
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/2210.16971__00/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/2210.16971__00.json
    English statement: (Fox, Himwich, Mani, Zhou 2022, arXiv:2210.16971 Conjecture 1.4)
      Let B be an oriented graph whose underlying undirected graph is bipartite and which
      admits a homomorphism to the single directed edge.  Then B has the directed Sidorenko
      property: for every oriented graph D, the number of homomorphisms from B to D
      satisfies hom(B,D) * |V(D)|^(2 e(B)) >= e(D)^(e(B)) * |V(D)|^(|V(B)|), that is
      t(B,D) >= t(arc,D)^(e(B)).
    Definitions: [x223_hom_to_arc B] - a 2-colouring under which every arc runs from the
      0-side to the 1-side, i.e. a homomorphism to the directed edge (this file);
      [x223_bipartite_dg B] - the underlying undirected graph is bipartite (this file);
      [x223_dhom_count B D] - the number of arc-preserving maps B -> D (this file);
      [x223_directed_sidorenko B] - the cross-multiplied density inequality above
      (this file); [oriented D] - no pair of opposite arcs (GTBase.common);
      [num_edges D] - the number of arcs (coq-graph-theory digraph.v).
    Notes: the homomorphism DENSITIES t(B,D) = hom(B,D)/|V(D)|^{|V(B)|} and
      t(arc,D) = e(D)/|V(D)|^2 are rationals; the inequality is stated in the equivalent
      cross-multiplied form over nat, which is exact (no o(1) term is needed: the Sidorenko
      inequality is an exact inequality for every FINITE D, the graphon formulation being
      only a reformulation).  The bipartiteness hypothesis is redundant -- a homomorphism to
      the directed edge already 2-colours the underlying graph without monochromatic edge --
      but is kept because the source states it. *)
Definition directed_sidorenko_bipartite_statement : Prop :=
  forall B : diGraph,
    oriented B ->
    x223_bipartite_dg B ->
    x223_hom_to_arc B ->
    x223_directed_sidorenko B.

(** Corpus row: arxiv:2210.16971#01
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/2210.16971__01/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/2210.16971__01.json
    English statement: (Fox, Himwich, Mani, Zhou 2022, arXiv:2210.16971 Conjecture 1.7)
      Every oriented graph B that admits a homomorphism to the single directed edge and
      whose underlying undirected graph contains a cycle has the directed Sidorenko
      property.
    Definitions: [x223_hom_to_arc B], [x223_und_cyclic B] - some non-empty vertex set spans
      at least as many arcs as it has vertices, which for an oriented graph is exactly
      "the underlying undirected graph has a cycle" (this file); [x223_directed_sidorenko B]
      (this file); [oriented] (GTBase.common).
    Notes: BLOCKED. The source conclusion is the directed FORCING property: for every p and
      every sequence of oriented graphs whose arc density tends to p/2 and whose B-density
      tends to (p/2)^(e(B)), the sequence is p-quasirandom.  That is a graph-LIMIT statement
      (quasirandomness is defined through the cut norm of the limit graphon) with no known
      equivalent finite form, and GTBase has no graphon / real-density layer.  The body above
      therefore replaces the forcing conclusion by the strictly WEAKER Sidorenko conclusion of
      the companion row arxiv:2210.16971#00 - a wrong-object placeholder that keeps the
      hypotheses (hom to the arc, a cycle in the underlying graph) faithful but does NOT state
      Conjecture 1.7.  No source-verification tuple is claimed for this row.
      SECOND-READER READBACK (2026-09-23): the placeholder is sound in the sense that it is
      neither vacuous nor refutable, but it is also INFORMATION-FREE relative to the companion
      row: a homomorphism to the arc already 2-colours the underlying graph, so
      [x223_hom_to_arc B] implies [x223_bipartite_dg B], and the placeholder's hypotheses are
      therefore those of directed_sidorenko_bipartite_statement plus "has a cycle".  Hence
      arxiv:2210.16971#00 implies this body outright, and the body must never be used as an
      independent endpoint of a corpus relation edge. *)
Definition directed_forcing_cyclic_statement : Prop :=
  forall B : diGraph,
    oriented B ->
    x223_hom_to_arc B ->
    x223_und_cyclic B ->
    x223_directed_sidorenko B.

(** Corpus row: arxiv:1810.00058#01
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/1810.00058__01/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/1810.00058__01.json
    English statement: (Chudnovsky, Fox, Scott, Seymour, Spirkl 2018, arXiv:1810.00058,
      the open case H = K_3 of Conjecture 1.4)
      There is a positive rational eps = p/d <= 1 such that every triangle-free graph G on
      more than one vertex in which every closed neighbourhood has fewer than eps * |V(G)|
      vertices contains two anticomplete vertex sets A and B with
      |A| >= eps * |V(G)|^eps and |B| >= eps * |V(G)|.
    Definitions: [x223_eps_bounded G p d] - every closed neighbourhood satisfies
      d * |N[v]| < p * |V(G)| (this file); [x223_anticomplete A B] - A and B are disjoint
      with no edge between them (this file); [induced_free G 'K_3] - G has no induced
      triangle, i.e. G is triangle-free (GTBase.common); ['K_3] (coq-graph-theory).
    Notes: the real constant eps is taken rational, eps = p/d with 0 < p <= d, and the
      fractional exponent is cleared by raising |A| >= eps*|G|^eps to the d-th power:
      p^d * |G|^p <= d^d * |A|^d.  This is exactly the shape of the parent row
      arxiv:1810.00058#00 (X58.v), so the corpus edge e076 is a pure instantiation.  The
      eps-boundedness hypothesis uses the source's CLOSED neighbourhood |N[v]| < eps|G|
      (X58.v uses the maximum degree Delta(G) < eps|G|, which is the same condition off by
      one and yields a LARGER graph class; the closed form is the faithful one and is the
      STRONGER of the two conditions -- |N[v]| = deg(v)+1, so it implies the Delta form --
      hence the statement it guards is the weaker of the two and #00 still implies this row,
      which is exactly what implications_X223.v proves for e076).
      SECOND-READER READBACK (2026-09-23): the encoding was checked against arXiv:1810.00058
      verbatim -- "G is eps-bounded if |N[v]| < eps|G| for all v", "(A,B) is c-sparse if
      A cap B = 0 and |E(A,B)| <= c|A||B|", "A is anticomplete to B if there is no edge
      between them", and Conjecture 1.4 "for every graph H there exists eps > 0 such that in
      every H-free eps-bounded graph G with |G| > 1 vertices, there is an anticomplete
      (eps n^eps, eps n)-pair" -- and matches on every clause, including the |G| > 1 guard.
      The earlier sentence calling the closed-neighbourhood form the "weaker hypothesis" was
      the reverse of the truth and has been corrected above. *)
Definition triangle_free_eps_bounded_anticomplete_pair_statement : Prop :=
  exists p d : nat,
    [/\ 0 < p, p <= d &
        forall G : sgraph,
          1 < #|G| ->
          induced_free G 'K_3 ->
          x223_eps_bounded G p d ->
          exists A B : {set G},
            [/\ x223_anticomplete A B,
                p ^ d * #|G| ^ p <= d ^ d * #|A| ^ d &
                p * #|G| <= d * #|B|]].

(** Corpus row: arxiv:1810.00058#02
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/1810.00058__02/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/1810.00058__02.json
    English statement: (Chudnovsky, Fox, Scott, Seymour, Spirkl 2018, arXiv:1810.00058
      Conjecture 3.4)
      For every graph H there are a positive rational eps = p/d <= 1 and a positive integer s
      such that for every H-free graph G on more than one vertex in which every closed
      neighbourhood has fewer than eps * |V(G)| vertices, and every rational c = a/b in
      [0,1], there are disjoint vertex sets A and B with at most c|A||B| edges between them,
      |A| >= eps * c^s * |V(G)| and |B| >= eps * |V(G)|.
    Definitions: [x223_eps_bounded G p d] (this file); [x223_sparse_pair A B a b] - A and B
      are disjoint and b * e(A,B) <= a * |A| * |B|, i.e. (A,B) is (a/b)-sparse (this file);
      [x223_edges_between A B] - the number of ordered pairs (u,v) in A x B with u -- v,
      which for disjoint A and B is |E(A,B)| (this file); [induced_free G H] (GTBase.common).
    Notes: eps is rational (p/d) and so is c (a/b with 0 < b and a <= b); s is a natural
      exponent.  The size bound |A| >= eps * c^s * |G| is cleared of division as
      a^s * (p * |G|) <= d * (b^s * |A|), and |B| >= eps * |G| as p * |G| <= d * |B|.  The
      eps-boundedness hypothesis uses the source's closed-neighbourhood form. *)
Definition h_free_eps_bounded_sparse_pair_statement : Prop :=
  forall H : sgraph,
    exists p d s : nat,
      [/\ 0 < p, p <= d, 0 < s &
          forall G : sgraph,
            1 < #|G| ->
            induced_free G H ->
            x223_eps_bounded G p d ->
            forall a b : nat, 0 < b -> a <= b ->
              exists A B : {set G},
                [/\ x223_sparse_pair A B a b,
                    a ^ s * (p * #|G|) <= d * (b ^ s * #|A|) &
                    p * #|G| <= d * #|B|]].

(** Corpus row: arxiv:1912.02342#00
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/1912.02342__00/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/1912.02342__00.json
    English statement: (Fox, Pach, Suk 2019, arXiv:1912.02342 Conjecture 4.1)
      For every d >= 2 there is a positive integer q such that every finite graph G whose
      neighbourhood set system has VC-dimension at most d contains a clique or a stable set
      S with |V(G)| <= |S|^q, that is |S| >= |V(G)|^(1/q).
    Definitions: [x223_shattered S] - every subset of S is cut out of S by the open
      neighbourhood of some vertex (this file); [x223_vc_dim_leq G d] - no shattered set has
      more than d vertices (this file); [cliqueb] (coq-graph-theory sgraph.v);
      [stable] (coq-graph-theory dom.v); [N(v)] - the open neighbourhood (coq-graph-theory).
    Notes: the real exponent eps(d) > 0 is taken of the form 1/q with q a positive integer,
      so "a clique or stable set of size n^eps(d)" becomes |V(G)| <= |S|^q.  Over the
      rationals every positive eps is bounded below by some 1/q, and the conclusion is
      monotone in eps, so quantifying over 1/q loses nothing.  The corpus records this row
      as SOLVED (Nguyen-Scott-Seymour, arXiv:2312.15572); the statement is nevertheless
      recorded as an open-problem node, not as a proved theorem. *)
Definition vc_dimension_erdos_hajnal_statement : Prop :=
  forall d : nat, 2 <= d ->
    exists q : nat,
      0 < q /\
      forall G : sgraph,
        x223_vc_dim_leq G d ->
        exists S : {set G}, (cliqueb S || stable S) /\ #|G| <= #|S| ^ q.

(** Corpus row: arxiv:2405.05902#01
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/2405.05902__01/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/2405.05902__01.json
    English statement: (Fox, Nenadov, Pham 2024, arXiv:2405.05902 Conjecture 6.1)
      For every rational c = a/b in (0,1] and every integer l >= 1 there is an integer C > 1
      such that for every (c,t)-sparse graph Gamma on n vertices, every spanning subgraph of
      Gamma with no induced cycle of length 2l has m edges with
      m^l <= C^l * t^(l-1) * n^(l+1), that is m <= C * t^(1-1/l) * n^(1+1/l).
    Definitions: [x223_ct_sparse Gamma a b t] - any two vertex sets of size at least t span
      at most (1 - a/b)|A||B| edges (this file); [x223_edges_between] (this file);
      [del_edge_set Gamma F] - Gamma with the edge set F deleted, i.e. a spanning subgraph
      (GTBase.common); [induced_free X (cycle_graph (2*l))] - X has no induced C_2l
      (GTBase.common, GTBase.base); [E(_)] (coq-graph-theory).
    Notes: the induced Turan number ex(Gamma, P_{C_2l}) is NOT defined as a maximum (graphs
      on a fixed vertex set are not a finite type here); the bound "ex(Gamma,P) <= X" is
      stated in the equivalent universal form "every subgraph of Gamma with the property P
      has at most X edges".  Quantifying over SPANNING subgraphs only (an edge subset F to
      delete) loses nothing: any subgraph is obtained from the spanning subgraph with the
      same edges by deleting isolated vertices, which changes neither the edge count nor the
      presence of an induced C_2l.  The fractional exponents are cleared by raising to the
      l-th power, and c is rational (a/b with 0 < a <= b).
      SECOND-READER READBACK (2026-09-23): both primitives were re-fetched from
      arXiv:2405.05902 and match -- "Gamma is (c,t)-sparse if for every pair of vertex subsets
      A, B (NOT necessarily disjoint) with |A|,|B| >= t we have e(A,B) <= (1-c)|A||B|", with
      the edges inside A cap B counted twice, which is exactly the ORDERED-pair convention of
      [x223_edges_between]; and ex(Gamma,P) is "the maximum number of edges of a subgraph
      G subset Gamma that belongs to P".  The guard [0 < l] admits l = 1 (the source writes
      C_{2l} and means l >= 2), but that instance is trivially true -- it reads
      m <= C * n^2 with C > 1 -- so it neither strengthens nor weakens the statement. *)
Definition induced_turan_even_cycle_sparse_statement : Prop :=
  forall a b l : nat,
    0 < a -> a <= b -> 0 < l ->
    exists C : nat,
      1 < C /\
      forall (Gamma : sgraph) (t : nat),
        x223_ct_sparse Gamma a b t ->
        forall F : {set {set Gamma}},
          induced_free (del_edge_set Gamma F) (cycle_graph (2 * l)) ->
          #|E(del_edge_set Gamma F)| ^ l <= C ^ l * (t ^ l.-1 * #|Gamma| ^ l.+1).
