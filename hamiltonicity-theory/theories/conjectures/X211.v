(** * Hamilton.conjectures.X211 -- Bondy–Murty Hamilton rows (wave X211, 2026-09-23) *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local x211 vocabulary ***********************************************

    Only notions ABSENT from coq-graph-theory 0.9.7 and from [GTBase]
    ([base.v] / [common.v]) are introduced here.  Reused from the shared layer:
    [hamiltonian], [hamiltonian_cycle], [traceable] and [induced_free]
    (GTBase.common), [k_connected], [regular], [bipartite], [wagner_planar]
    (GTBase.base), [induced], [components], [connected], ['K_n,m] (the library).

    Cycle convention (GTBase.common): [hamiltonian] accepts the two-vertex
    "digon", so every row whose source assumes at least three vertices carries a
    [2 < #|G|] guard (rows bm-089, bm-091 below); the rows whose hypotheses
    already force [#|G| >= 5] ([k_connected G 4], [regular G 3] with three
    Hamilton cycles, minimum degree >= 4) need none. *)

(** A CLAW is [K_{1,3}]; [G] is claw-free when no induced subgraph of [G] is
    isomorphic to it.  [@MOVE-to-base]: claw-freeness is wanted by the
    hamiltonicity and the chromatic (chi-boundedness) rows alike. *)
Definition x211_claw_free (G : sgraph) : Prop := induced_free G 'K_1,3.

(** Minimum degree at least [d] (the companion of base's maximum degree
    [Delta]).  [@MOVE-to-base]: a [delta] dual to [Delta] belongs in base.v. *)
Definition x211_min_degree_geq (G : sgraph) (d : nat) : Prop :=
  forall v : G, d <= #|N(v)|.

(** A graph automorphism: an adjacency-preserving bijection.  [@MOVE-to-base]:
    byte-identical to [U2.graph_automorphism] (hamiltonicity-theory/U2.v). *)
Definition x211_graph_automorphism (G : sgraph) (f : G -> G) : Prop :=
  bijective f /\ forall u v : G, (f u -- f v) = (u -- v).

(** VERTEX-TRANSITIVE: the automorphism group acts transitively on vertices.
    [@MOVE-to-base]: byte-identical to [U2.vertex_transitive]. *)
Definition x211_vertex_transitive (G : sgraph) : Prop :=
  forall x y : G, exists f : G -> G, x211_graph_automorphism f /\ f x = y.

(** The (unordered) edge set realised by a cycle given as a [seq] of vertices:
    the 2-subsets {x, next c x}.  Two seqs describe the SAME cycle exactly when
    they have the same edge set, so counting Hamilton cycles up to rotation and
    reflection = counting these edge sets.  [@MOVE-to-base]: byte-identical to
    [U2.cycle_edges]. *)
Definition x211_cycle_edges (G : sgraph) (c : seq G) : {set {set G}} :=
  [set [set x; next c x] | x in [set z | z \in c]].
Arguments x211_cycle_edges : clear implicits.

(** The set of Hamilton cycles of [G], each identified with its edge set.  A
    Hamilton cycle has [size c = #|G|], so ranging over [#|G|]-tuples loses
    nothing and keeps the collection a finite set. *)
Definition x211_hamilton_cycle_edge_sets (G : sgraph) : {set {set {set G}}} :=
  [set A : {set {set G}} |
    [exists c : (#|G|).-tuple G,
       hamiltonian_cycle G c && (A == x211_cycle_edges G c)]].

(** [G] contains a triangle: three pairwise adjacent vertices (the positive
    form of the negation of base's [triangle_free]). *)
Definition x211_has_triangle (G : sgraph) : Prop :=
  exists x y z : G, [/\ x -- y, y -- z & z -- x].

(** [k]-TOUGHNESS, rational-free: for every vertex set [S] whose removal leaves
    at least two components, [k * c(G - S) <= |S|], where [c(G - S)] is the
    number of connected components of [G - S] ([#|components (~: S)|], the
    library's [components] of the complement of [S]).  This is the standard
    "|S| >= t * c(G - S) for every vertex cut S" with [t] an integer, so no
    rationals are needed. *)
Definition x211_tough (G : sgraph) (k : nat) : Prop :=
  forall S : {set G},
    1 < #|components (~: S)| -> k * #|components (~: S)| <= #|S|.

(** HYPOHAMILTONIAN: not Hamiltonian, but every vertex-deleted subgraph is. *)
Definition x211_hypohamiltonian (G : sgraph) : Prop :=
  ~ hamiltonian G /\ forall v : G, hamiltonian (induced ([set: G] :\ v)).

(** HYPOTRACEABLE: no Hamilton path, but every vertex-deleted subgraph has one. *)
Definition x211_hypotraceable (G : sgraph) : Prop :=
  ~ traceable G /\ forall v : G, traceable (induced ([set: G] :\ v)).

(** PLACEHOLDER for "G is the graph of a 4-regular (= simple) 4-dimensional
    convex polytope" (row bm-080).  The real notion lives in R^4: a polytope is
    the convex hull of finitely many points, "simple" means every vertex lies on
    exactly 4 facets, and the graph is its 1-skeleton.  GTBase has NO real
    geometry / convexity / polytope layer, and no combinatorial characterisation
    of 4-polytope graphs is known, so this stand-in proxies the hypothesis by
    its two classical CONSEQUENCES -- 4-regularity (simplicity) and
    4-connectivity (Balinski's theorem).  Every 4-regular 4-polytope graph
    satisfies it, but so do many other graphs, i.e. the proxy is STRICTLY WEAKER
    than the real hypothesis and the resulting statement is STRICTLY STRONGER
    than Barnette's conjecture.  NOT faithful -- the row's statement leg is
    BLOCKED. *)
Definition x211_four_polytope_graph_placeholder (G : sgraph) : Prop :=
  regular G 4 /\ k_connected G 4.

(** ** X211 statements *****************************************************)

(** Corpus row: bm:bm-079
    Site: https://graph-theory-ai.github.io/graph-conjectures/bm/bm-079/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/bondy_murty_reviews/bm-079.json
    English statement: (Matthews and Sumner 1984; Bondy–Murty, Appendix A #79)
      Every finite simple graph that is 4-connected and has no induced subgraph
      isomorphic to the claw K_{1,3} has a Hamilton cycle.
    Definitions: [x211_claw_free G] — no vertex set of G induces a subgraph
      isomorphic to the complete bipartite graph K_{1,3} ([induced_free G
      'K_1,3], this file X211.v, over GTBase.common's [induced_free]);
      [k_connected G 4] — more than four vertices, and deleting any set of fewer
      than four vertices leaves the rest connected (Whitney form,
      base/theories/base.v); [hamiltonian G] — G has a closed spanning walk
      visiting every vertex exactly once (base/theories/common.v).
    Notes: [k_connected G 4] forces [4 < #|G|], so the digon convention of
      [hamiltonian] ([hamiltonian 'K_2] holds) cannot weaken the conclusion
      here.  "Claw-free" is stated as the absence of an INDUCED K_{1,3}, which
      is the standard meaning; the subgraph-containment reading would be a
      different (much stronger) hypothesis. *)
Definition matthews_sumner_four_connected_claw_free_statement : Prop :=
  forall G : sgraph, k_connected G 4 -> x211_claw_free G -> hamiltonian G.

(** Corpus row: bm:bm-080
    Site: https://graph-theory-ai.github.io/graph-conjectures/bm/bm-080/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/bondy_murty_reviews/bm-080.json
    English statement: (Barnette; see Grünbaum 1970, p. 1145; Bondy–Murty,
      Appendix A #80) Every graph that is 4-regular and 4-connected has a
      Hamilton cycle.  This is NOT the conjecture: the source restricts the
      hypothesis to the graphs of simple 4-dimensional convex polytopes, and
      4-regular + 4-connected is only a consequence of that hypothesis.
    Definitions: [x211_four_polytope_graph_placeholder G] — PLACEHOLDER for "G
      is the graph of a 4-regular 4-polytope", proxied by [regular G 4 /\
      k_connected G 4] (this file, X211.v); [regular G 4] and [k_connected G 4]
      (base/theories/base.v); [hamiltonian G] (base/theories/common.v).
    Notes: BLOCKED.  The hypothesis of row bm-080 is geometric: G must be the
      1-skeleton of a simple (equivalently, for 4-polytopes, 4-regular)
      4-dimensional convex polytope.  Formalising it needs a real-geometry /
      convex-polytope layer (points of R^4, convex hulls, faces, simplicity),
      which neither coq-graph-theory 0.9.7 nor GTBase provides, and no purely
      combinatorial characterisation of 4-polytope graphs is known (already for
      3-polytopes it is Steinitz's theorem: 3-connected planar, a nontrivial
      theorem and a genuinely different statement).  The placeholder above
      replaces the hypothesis by its two classical consequences (simplicity =>
      4-regular; Balinski => 4-connected), which is STRICTLY WEAKER, hence the
      statement as written is STRICTLY STRONGER than Barnette's conjecture and
      is a proxy, not the row.  The statement leg is `blocked` in
      meta/v2_statement_waves.json; this file still compiles.
      Readback 2026-09-23 (second reader): the `blocked` verdict is confirmed,
      and the placeholder is worse than "strictly stronger" - it is FALSE.
      "Every 4-regular 4-connected graph is Hamiltonian" is Nash-Williams'
      conjecture, refuted by the Meredith graph (70 vertices, 4-regular,
      4-connected, non-Hamiltonian).  So this definition must never be promoted
      to a `done` row, and a future grounding or applications file could even
      commit an unconditional refutation of it - which the exact-type probe of
      meta/check_milestone.py would then flag on a non-`disproved` row.  Keep it
      `blocked`. *)
Definition barnette_simple_four_polytope_hamiltonian_statement : Prop :=
  forall G : sgraph, x211_four_polytope_graph_placeholder G -> hamiltonian G.

(** Corpus row: bm:bm-085
    Site: https://graph-theory-ai.github.io/graph-conjectures/bm/bm-085/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/bondy_murty_reviews/bm-085.json
    English statement: (Cantoni; see Ninčák 1974 and Tutte 1976; Bondy–Murty,
      Appendix A #85) Let G be a planar graph in which every vertex has exactly
      three neighbours.  If G has exactly three Hamilton cycles, counted as edge
      sets, then G has three pairwise adjacent vertices.
    Definitions: [wagner_planar G] — neither K_5 nor K_{3,3} is a minor of G,
      which by Wagner's theorem is exactly planarity (base/theories/base.v);
      [regular G 3] — every vertex has exactly three neighbours (base.v);
      [x211_hamilton_cycle_edge_sets G] — the set of edge sets
      [x211_cycle_edges G c] of the Hamilton cycles c of G, c ranging over the
      [#|G|]-tuples of vertices (this file, X211.v; [hamiltonian_cycle] is
      GTBase.common's [ucycleb (--) c && (size c == #|G|)]);
      [x211_cycle_edges G c] — the 2-sets {x, next c x} for x on c (X211.v);
      [x211_has_triangle G] — three pairwise adjacent vertices (X211.v).
    Notes: "exactly three Hamilton cycles" is counted UP TO ROTATION AND
      REFLECTION, by identifying a Hamilton cycle with its edge set — the
      standard convention for "3H graphs" (a single Hamilton cycle on n vertices
      is described by 2n different seqs).  [regular G 3] together with three
      distinct Hamilton cycles forces [3 < #|G|], so the digon convention of
      [hamiltonian_cycle] is harmless.  Planarity is the combinatorial
      (Wagner/minor) form, faithful and axiom-free; it carries no embedding, but
      the statement needs none. *)
Definition cantoni_planar_cubic_three_hamilton_cycles_statement : Prop :=
  forall G : sgraph,
    wagner_planar G ->
    regular G 3 ->
    #|x211_hamilton_cycle_edge_sets G| = 3 ->
    x211_has_triangle G.

(** Corpus row: bm:bm-088
    Site: https://graph-theory-ai.github.io/graph-conjectures/bm/bm-088/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/bondy_murty_reviews/bm-088.json
    English statement: (Thomassen 1976; Bondy–Murty, Appendix A #88) There is a
      number n0 such that every connected vertex-transitive graph with at least
      n0 vertices has a Hamilton cycle.
    Definitions: [x211_vertex_transitive G] — for any two vertices x, y some
      automorphism of G maps x to y, an automorphism being an adjacency-
      preserving bijection [x211_graph_automorphism] (this file, X211.v);
      [connected [set: G]] — the library's connectedness of the full vertex set
      (coq-graph-theory sgraph.v, re-exported by GTBase.base); [hamiltonian G]
      (base/theories/common.v).
    Notes: "all but finitely many" is encoded as "there is a size threshold n0
      beyond which all of them are Hamiltonian".  Over finite simple graphs this
      is equivalent to the finiteness of the set of non-Hamiltonian connected
      vertex-transitive graphs UP TO ISOMORPHISM only because there are finitely
      many graphs of each order; the threshold form is the one the source's
      "only five are known" reading supports (K_2, Petersen, Coxeter and the two
      truncations all have at most 28 vertices).  The digon convention
      ([hamiltonian 'K_2]) is irrelevant: any n0 >= 3 may be chosen.
      Readback 2026-09-23 (second reader): the convention does disagree with the
      source on one listed exception - under [hamiltonian] the graph K_2 IS
      Hamiltonian, so the encoding recognises only four of the five known
      exceptions - but since the exceptions are asserted to be finite in number
      and the encoding is a size threshold, the disagreement cannot change the
      truth value of this row.  It would matter for any future row that counts
      or names the exceptions. *)
Definition thomassen_vertex_transitive_all_but_finitely_many_statement : Prop :=
  exists n0 : nat,
    forall G : sgraph,
      n0 <= #|G| -> connected [set: G] -> x211_vertex_transitive G ->
      hamiltonian G.

(** Corpus row: bm:bm-089
    Site: https://graph-theory-ai.github.io/graph-conjectures/bm/bm-089/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/bondy_murty_reviews/bm-089.json
    English statement: (Chvátal 1973; Bondy–Murty, Appendix A #89) There is a
      positive integer k with the following property: every graph on more than
      two vertices in which, for every vertex set S whose removal leaves at
      least two connected components, k times the number of those components is
      at most the size of S, has a Hamilton cycle.
    Definitions: [x211_tough G k] — for every S, if G - S has at least two
      components then [k * #|components (~: S)| <= #|S|], i.e. G is k-tough
      (this file, X211.v, over the library's [components] from sgraph.v);
      [hamiltonian G] (base/theories/common.v).
    Notes: toughness is stated in the cleared integral form [k * c(G - S) <=
      |S|], so no rationals are needed; the conjecture quantifies over a
      positive INTEGER k, exactly as the corpus text does.  (The rational
      version — some rational t0 with every t0-tough graph Hamiltonian — is
      equivalent: k-tough implies t0-tough for k >= t0, so any rational witness
      can be rounded up.)  The guard [2 < #|G|] is load-bearing: a one-vertex
      graph is vacuously k-tough for every k and is NOT Hamiltonian under the
      convention of GTBase.common (see grounding_X211.v,
      [tough_K1_all_k]/[not_hamiltonian_K1]), so without it the statement would
      be refutable for trivial reasons.  A k-tough graph with k >= 1 is
      automatically connected (take S = set0). *)
Definition chvatal_toughness_hamiltonian_statement : Prop :=
  exists k : nat,
    0 < k /\ forall G : sgraph, 2 < #|G| -> x211_tough G k -> hamiltonian G.

(** Corpus row: bm:bm-090
    Site: https://graph-theory-ai.github.io/graph-conjectures/bm/bm-090/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/bondy_murty_reviews/bm-090.json
    English statement: (Thomassen 1978; Bondy–Murty, Appendix A #90) There is a
      graph in which every vertex has at least four neighbours, which has no
      Hamilton cycle, and in which deleting any single vertex leaves a graph
      that does have a Hamilton cycle.
    Definitions: [x211_min_degree_geq G 4] — every vertex has at least four
      neighbours (this file, X211.v); [x211_hypohamiltonian G] — G is not
      Hamiltonian but [induced ([set: G] :\ v)], the subgraph induced on the
      vertices other than v, is Hamiltonian for every vertex v (X211.v, over the
      library's [induced] and GTBase.common's [hamiltonian]).
    Notes: the row is a QUESTION ("Is there a hypohamiltonian graph of minimum
      degree at least 4?"), formalised as the existence statement it asks about;
      its status is open, so neither this statement nor its negation is proved
      here.  Minimum degree at least 4 forces [4 < #|G|], hence every
      vertex-deleted subgraph has at least four vertices and the digon
      convention of [hamiltonian] cannot make the conclusion cheap.  The
      quantification [exists G : sgraph] ranges over finite simple graphs, which
      is the intended scope. *)
Definition hypohamiltonian_minimum_degree_four_statement : Prop :=
  exists G : sgraph, x211_min_degree_geq G 4 /\ x211_hypohamiltonian G.

(** Corpus row: bm:bm-091
    Site: https://graph-theory-ai.github.io/graph-conjectures/bm/bm-091/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/bondy_murty_reviews/bm-091.json
    English statement: (Grötschel 1978; Bondy–Murty, Appendix A #91) No
      bipartite graph on more than two vertices has the property that it has no
      Hamilton path while every one of its vertex-deleted subgraphs has one.
    Definitions: [bipartite G] — a 2-colouring of the vertices with no
      monochromatic edge (base/theories/base.v); [x211_hypotraceable G] — G has
      no Hamilton path, but [induced ([set: G] :\ v)] has one for every vertex v
      (this file, X211.v, over the library's [induced] and GTBase.common's
      [traceable]).
    Notes: the guard [2 < #|G|] is load-bearing and is exactly the source's
      implicit "nontrivial graph" assumption: the edgeless graph on two vertices
      has no Hamilton path while each of its one-vertex subgraphs has one (a
      single vertex is a Hamilton path), so it is literally hypotraceable and
      bipartite (see grounding_X211.v, [hypotraceable_edgeless2] — the guard has
      teeth).  An exhaustive search over all graphs on at most 7 vertices found
      no other bipartite hypotraceable graph, in agreement with the literature
      (the smallest hypotraceable graphs have 34 vertices). *)
Definition grotschel_no_bipartite_hypotraceable_statement : Prop :=
  forall G : sgraph, 2 < #|G| -> bipartite G -> ~ x211_hypotraceable G.
