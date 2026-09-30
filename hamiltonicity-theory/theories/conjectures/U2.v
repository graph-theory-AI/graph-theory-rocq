(** * Hamilton.conjectures.U2 — milestone U2 (namespace Hamilton, plan v4)

    Statement-only formalizations (axiom-free: no Conjecture/Axiom/Parameter/
    Admitted) of nine open problems on Hamiltonicity.

    CORE undirected vocabulary comes from graph-theory-base (GTBase.base), which
    re-exports the coq-graph-theory undirected API (sgraph, x -- y, N(x), connected,
    'K_n, diso, ucycle/ucycleb) plus the cross-area primitives Delta, regular, ...
    We REUSE [regular] from base verbatim (cubic = [regular G 3]).

    fingroup is imported in addition to base because Cayley graphs (Row 2) are
    genuinely group-theoretic and finGroupType is NOT part of base's vocabulary.

    PLANARITY G2-GATE: planarity/genus are NOT installed (coq-graph-theory-planar +
    coq-fourcolor are absent on this switch).  Rows 5, 7, 8 (manifest
    requires_planarity=true, the *planar* — not surface — rows) now state their
    planarity hypothesis as the combinatorial [wagner_planar G] from base (NO K5
    and NO K3,3 minor), which by Wagner's theorem IS planarity: faithful, axiom-free
    and fourcolor-free.  [wagner_planar] is used OPAQUELY (base imports minor; we do
    not).  Row 6 (toroidal) is DONE since Wave 1: it uses the REAL [toroidal]
    (= [embeds_in_genus G 1], an orientable rotation-system embedding of Euler
    genus ≤ 1) from the Track-A foundation [Topological.foundations.embedding];
    the 4-connectivity hypothesis keeps the genus formula in its faithful
    (connected) regime.  All rows model their statements fully. *)

From GTBase Require Export base.
From mathcomp Require Import fingroup.
From Topological.foundations Require Import embedding.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Shared Hamiltonicity primitives

    A path / cycle is encoded as a [seq] of vertices.  [sorted (--) s] is the
    consecutive-adjacency walk condition; [ucycleb (--) c] additionally closes the
    walk (boolean cycle predicate).  Adding [uniq] makes the walk simple, and
    [size = #|G|] forces it to visit every vertex exactly once (a uniq seq of that
    size is a permutation of the vertex set). *)

(** A Hamiltonian path: a simple spanning walk. *)
Definition hamiltonian_path (G : sgraph) (s : seq G) : bool :=
  [&& sorted (--) s, uniq s & size s == #|G|].
Arguments hamiltonian_path : clear implicits.

(** A Hamiltonian cycle: a simple spanning closed walk. *)
Definition hamiltonian_cycle (G : sgraph) (c : seq G) : bool :=
  ucycleb (--) c && (size c == #|G|).
Arguments hamiltonian_cycle : clear implicits.

(** A graph is Hamiltonian iff it has a Hamilton cycle. *)
Definition is_hamiltonian (G : sgraph) : Prop :=
  exists c : seq G, hamiltonian_cycle G c.

(** The (unordered) edge set realised by a cycle [c]: the 2-subsets {x, next c x}
    for x ranging over the cycle.  Used to compare cycles up to rotation /
    reflection (two seqs are "the same cycle" iff they have the same edge set),
    so "a second Hamilton cycle" / "uniquely Hamiltonian" are stated on edge sets,
    not on raw seqs. *)
Definition cycle_edges (G : sgraph) (c : seq G) : {set {set G}} :=
  [set [set x; next c x] | x in [set z | z \in c]].
Arguments cycle_edges : clear implicits.

(** [k_connected] (Whitney k-connectivity) is now in graph-theory-base — promoted from
    U2 ∩ U3 ∩ U9 — and reused here via the base export. *)

(** ** Bipartiteness now comes from [GTBase.base] (promoted during the D2
    reconcile, 2-colouring form [exists f : G -> bool, forall edge, f x != f y]);
    the former local [{set G}]-part version was interchangeable and is removed. *)

(** ** Graph automorphisms and vertex-transitivity (Algebraic Graph Theory).
    An automorphism is an adjacency-preserving bijection; [G] is vertex-transitive
    iff its automorphism group acts transitively on vertices. *)
Definition graph_automorphism (G : sgraph) (f : G -> G) : Prop :=
  bijective f /\ forall u v : G, (f u -- f v) = (u -- v).

Definition vertex_transitive (G : sgraph) : Prop :=
  forall x y : G, exists f : G -> G, graph_automorphism f /\ f x = y.

(** ** Cartesian (box) product G □ H — PROMOTED to graph-theory-base (GTBase.base).
    [cartesian_product] (and [box_rel]/[box_sym]/[box_irrefl]) now live in base/ — used here
    via `From GTBase Require Import base` — since a second area (homomorphism-theory/U3) needs
    products too. No local definition remains. *)

(** ** Line graph L(G).
    Vertices are the (undirected) edges of [G], canonically oriented once via
    [enum_rank] (low endpoint first); two distinct edges are adjacent iff they
    share an endpoint.  [@MOVE-to-base]: pure structural construction. *)
Section LineGraph.
Variable G : sgraph.

Definition lg_oedge (p : G * G) : bool :=
  (p.1 -- p.2) && (enum_rank p.1 < enum_rank p.2)%N.

Notation EdgeT := {p : G * G | lg_oedge p}.

Definition lg_ends (e : EdgeT) : {set G} := [set (val e).1; (val e).2].

Definition lg_rel : rel EdgeT :=
  fun e f => (e != f) && [exists v, (v \in lg_ends e) && (v \in lg_ends f)].

Lemma lg_sym : symmetric lg_rel.
Proof.
move=> e f; rewrite /lg_rel eq_sym; congr (_ && _).
by apply: eq_existsb => v; exact: andbC.
Qed.

Lemma lg_irrefl : irreflexive lg_rel.
Proof. by move=> e; rewrite /lg_rel eqxx. Qed.

Definition line_graph : sgraph := SGraph lg_sym lg_irrefl.
End LineGraph.

(** ** Cayley graph of a finite group [gT] with connection set [S].
    Vertices are group elements; [x -- y] iff x⁻¹y or y⁻¹x lies in [S].  The
    explicit symmetrisation (OR) and [x != y] make the [sgraph] obligations
    immediate for ANY [S]; the meaningful regime (symmetric, generating [S]) is
    pinned by the guards in the statement. *)
Section Cayley.
Variable gT : finGroupType.
Variable S : {set gT}.
Local Open Scope group_scope.

Definition cayley_rel : rel gT :=
  fun x y => (x != y) && ((x^-1 * y \in S) || (y^-1 * x \in S)).

Lemma cayley_sym : symmetric cayley_rel.
Proof. by move=> x y; rewrite /cayley_rel eq_sym orbC. Qed.

Lemma cayley_irrefl : irreflexive cayley_rel.
Proof. by move=> x; rewrite /cayley_rel eqxx. Qed.

Definition cayley_graph : sgraph := SGraph cayley_sym cayley_irrefl.
End Cayley.

(** A connection set is symmetric iff it is closed under inverses. *)
Definition symmetric_set (gT : finGroupType) (S : {set gT}) : Prop :=
  forall x : gT, (x \in S) = (x^-1 \in S)%g.

(** ----------------------------------------------------------------------- *)
(** Corpus row: opg:hamiltonian_paths_and_cycles_in_vertex_transitive_graphs
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/hamiltonian_paths_and_cycles_in_vertex_transitive_graphs/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/hamiltonian_paths_and_cycles_in_vertex_transitive_graphs.json
    English statement: (Open Problem Garden, "Hamiltonian paths and cycles in
      vertex transitive graphs") Every nonempty connected vertex-transitive
      graph has a Hamiltonian path: a duplicate-free sequence of vertices whose
      consecutive entries are adjacent and whose length is the number of
      vertices of the graph.
    Definitions: [hamiltonian_path G s] - [sorted (--) s], [uniq s] and
      [size s = #|G|] (this file, U2.v); [graph_automorphism f] - f is a
      bijection with f u -- f v exactly when u -- v (U2.v);
      [vertex_transitive G] - for any two vertices some automorphism maps the
      first to the second (U2.v); [connected [set: G]] (coq-graph-theory
      connectivity.v).
    Notes: the guard 0 < #|G| excludes the empty graph, for which the empty
      sequence would vacuously be a Hamiltonian path.  The source is a Problem
      (a question); the body asserts the affirmative answer.  Only the PATH half
      of the row's title is formalised, which is what the source proposition
      asks.  [hamiltonian_path] here duplicates the identical definition in
      GTBase.common (base/theories/common.v). *)
Definition hamiltonian_paths_and_cycles_in_vertex_transitive_gr_statement : Prop :=
  forall G : sgraph,
    0 < #|G| -> connected [set: G] -> vertex_transitive G ->
    exists s : seq G, hamiltonian_path G s.

(** Corpus row: opg:hamiltonicity_of_cayley_graphs
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/hamiltonicity_of_cayley_graphs/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/hamiltonicity_of_cayley_graphs.json
    English statement: (Open Problem Garden, "Hamiltonicity of Cayley graphs")
      For every finite group with more than two elements and every connection
      set S that is closed under inverses and generates the whole group, the
      Cayley graph of S is Hamiltonian, i.e. it has a closed duplicate-free walk
      visiting every group element exactly once.
    Definitions: [cayley_graph S] - vertices are the group elements, distinct
      x, y adjacent iff x^-1*y or y^-1*x lies in S (this file, U2.v);
      [symmetric_set S] - S is closed under inverses (U2.v);
      [hamiltonian_cycle]/[is_hamiltonian] (U2.v); [<<S>>] - the subgroup
      generated by S (MathComp fingroup).
    Notes: the three guards (more than two elements, S inverse-closed, S
      generating) are MODELLING ADDITIONS that pin the meaningful
      Lovasz/Babai form of the question; the literal source, "Is every Cayley
      graph Hamiltonian?", carries none of them, so the formalised statement is
      weaker than the literal one.  Adjacency is symmetrised explicitly so that
      [cayley_graph S] is a simple graph for ANY S; the identity, if it lies in
      S, contributes no edge because x != y is required. *)
Definition hamiltonicity_of_cayley_graphs_statement : Prop :=
  forall (gT : finGroupType) (S : {set gT}),
    2 < #|gT| -> symmetric_set S -> <<S>>%g = [set: gT] ->
    is_hamiltonian (cayley_graph S).

(** Corpus row: opg:4_connected_graphs_are_not_uniquely_hamiltonian
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/4_connected_graphs_are_not_uniquely_hamiltonian/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/4_connected_graphs_are_not_uniquely_hamiltonian.json
    English statement: (Open Problem Garden, "4-connected graphs are not uniquely
      hamiltonian") For every 4-connected graph G and every Hamilton cycle c of
      G there is a second Hamilton cycle of G whose edge set differs from that
      of c.
    Definitions: [k_connected G 4] - more than four vertices, and deleting any
      set of fewer than four vertices leaves the rest connected
      (base/theories/base.v); [hamiltonian_cycle G c] - [ucycleb (--) c] and
      [size c = #|G|] (this file, U2.v); [cycle_edges G c] - the set of the
      unordered pairs {x, next c x} for x on c (U2.v).
    Notes: "second Hamilton cycle" is compared on EDGE SETS, so a rotation or
      reflection of c does not count as a second cycle; this is the intended
      reading and is load-bearing. *)
Definition four_connected_graphs_are_not_uniquely_hamiltonian_statement : Prop :=
  forall G : sgraph, k_connected G 4 ->
    forall c : seq G, hamiltonian_cycle G c ->
      exists c' : seq G,
        hamiltonian_cycle G c' /\ cycle_edges G c' != cycle_edges G c.

(** ** Row 4 — Uniquely Hamiltonian graphs  (OPEN)

    Source: "Conjecture: If G is a finite r-regular graph, where r > 2, then G is
    not uniquely hamiltonian."

    Carrier: [sgraph].  New AREA primitives: [hamiltonian_cycle],
    [uniquely_hamiltonian] (unique-hamiltonicity, up to cycle edge set).  Reuses
    base [regular]. *)
Definition uniquely_hamiltonian (G : sgraph) : Prop :=
  exists c : seq G,
    hamiltonian_cycle G c /\
    forall c' : seq G, hamiltonian_cycle G c' -> cycle_edges G c' = cycle_edges G c.

(** Corpus row: opg:uniquely_hamiltonian_graphs
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/uniquely_hamiltonian_graphs/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/uniquely_hamiltonian_graphs.json
    English statement: (Open Problem Garden, "r-regular graphs are not uniquely
      hamiltonian") For every r > 2, no r-regular graph is uniquely
      hamiltonian, i.e. no such graph has a Hamilton cycle whose edge set is the
      edge set of every Hamilton cycle of the graph.
    Definitions: [regular G r] - every vertex has exactly r neighbours
      (base/theories/base.v); [hamiltonian_cycle G c] and [cycle_edges G c]
      (this file, U2.v); [uniquely_hamiltonian G] - some Hamilton cycle exists
      and every Hamilton cycle has its edge set (U2.v).
    Notes: a graph with NO Hamilton cycle fails [uniquely_hamiltonian] (which
      demands one), so for non-hamiltonian r-regular graphs the conclusion holds
      trivially, as in the usual reading.  The source says "finite r-regular
      graph"; finiteness is carried by the [sgraph] carrier itself. *)
Definition uniquely_hamiltonian_graphs_statement : Prop :=
  forall (r : nat) (G : sgraph),
    2 < r -> regular G r -> ~ uniquely_hamiltonian G.

(** ** Row 5 — Decomposing the prism of a 3-connected cubic planar graph  (OPEN)
    Planarity is the combinatorial [wagner_planar] (no K5/K3,3 minor) from base.

    Source: "Conjecture: Every prism over a 3-connected cubic planar graph can be
    decomposed into two Hamilton cycles."

    Carrier: the prism [G □ 'K_2].  New AREA primitive:
    [hamilton_decomposition_into_two] (hamilton-decomposition) — two
    edge-disjoint Hamilton cycles whose edge sets partition E(prism).  Reuses
    [cartesian_product] (cartesian-product), [k_connected], base [regular]
    (cubic).  [@MOVE-to-base]: [edge_set] is a pure structural edge-set of a
    graph (no Hamilton content), a base candidate like [cartesian_product] /
    [line_graph] / [bipartite]. *)
Definition edge_set (G : sgraph) : {set {set G}} :=
  [set e : {set G} | [exists x, exists y, (x -- y) && (e == [set x; y])]].

Definition hamilton_decomposition_into_two (G : sgraph) : Prop :=
  exists c1 c2 : seq G,
    [/\ hamiltonian_cycle G c1, hamiltonian_cycle G c2,
        [disjoint cycle_edges G c1 & cycle_edges G c2]
      & cycle_edges G c1 :|: cycle_edges G c2 = edge_set G].

(** Corpus row: opg:decomposing_the_prism_of_a_3_connected_cubic_planar_graphs_in_hamilton_cycles
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/decomposing_the_prism_of_a_3_connected_cubic_planar_graphs_in_hamilton_cycles/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/decomposing_the_prism_of_a_3_connected_cubic_planar_graphs_in_hamilton_cycles.json
    English statement: (Open Problem Garden, "Hamilton decomposition of prisms
      over 3-connected cubic planar graphs") For every planar, 3-connected,
      cubic graph G, the prism over G - the cartesian product of G with K2 -
      decomposes into two Hamilton cycles: there are two Hamilton cycles of the
      prism whose edge sets are disjoint and whose union is the whole edge set
      of the prism.
    Definitions: [wagner_planar G] - neither K5 nor K3,3 is a minor of G, which
      by Wagner's theorem is exactly planarity (base/theories/base.v);
      [k_connected G 3] and [regular G 3] (cubic) (base.v);
      [cartesian_product G 'K_2] - the prism, the box product (base.v);
      [edge_set G] - the set of 2-element edges of G (this file, U2.v, a local
      copy of GTBase.common's [edge_set]); [hamilton_decomposition_into_two G] -
      two Hamilton cycles with disjoint edge sets covering [edge_set G] (U2.v);
      [cycle_edges], [hamiltonian_cycle] (U2.v).
    Notes: the prism over a cubic graph is 3-regular plus one matching edge per
      vertex, hence 4-regular, so "decomposed into two Hamilton cycles" means
      every edge is used exactly once - which is what disjointness plus
      union = [edge_set] expresses. *)
Definition decomposing_the_prism_of_a_3_connected_cubic_planar_statement : Prop :=
  forall (G : sgraph),
    wagner_planar G -> k_connected G 3 -> regular G 3 ->
    hamilton_decomposition_into_two (cartesian_product G 'K_2).

(** Corpus row: opg:every_4_connected_toroidal_graph_has_a_hamilton_cycle
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/every_4_connected_toroidal_graph_has_a_hamilton_cycle/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/every_4_connected_toroidal_graph_has_a_hamilton_cycle.json
    English statement: (Open Problem Garden, "Every 4-connected toroidal graph
      has a Hamilton cycle") Every 4-connected graph that embeds in a surface of
      Euler genus at most one has a Hamilton cycle.
    Definitions: [toroidal G] - [embeds_in_genus G 1], i.e. G admits a
      combinatorial rotation-system embedding of Euler genus at most one
      (topological-graph-theory/theories/foundations/embedding.v);
      [k_connected G 4] (base/theories/base.v); [is_hamiltonian G] (this file,
      U2.v).
    Notes: [toroidal] is "genus at most 1", so planar graphs count as toroidal,
      the usual convention for this conjecture.  The 4-connectivity hypothesis
      keeps the genus formula in its faithful (connected) regime.  This is the
      one row of the file using the real topological embedding layer rather than
      the Wagner minor characterisation. *)
Definition every_4_connected_toroidal_graph_has_a_hamilton_cycl_statement : Prop :=
  forall G : sgraph, toroidal G -> k_connected G 4 -> is_hamiltonian G.

(** Corpus row: opg:every_prism_over_a_3_connected_planar_graph_is_hamiltonian
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/every_prism_over_a_3_connected_planar_graph_is_hamiltonian/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/every_prism_over_a_3_connected_planar_graph_is_hamiltonian.json
    English statement: (Open Problem Garden, "Every prism over a 3-connected
      planar graph is hamiltonian") For every planar 3-connected graph G, the
      prism over G - the cartesian product of G with K2 - has a Hamilton cycle.
    Definitions: [wagner_planar G] - no K5 and no K3,3 minor, i.e. planarity by
      Wagner's theorem (base/theories/base.v); [k_connected G 3] (base.v);
      [cartesian_product G 'K_2] - the prism (base.v); [is_hamiltonian G] (this
      file, U2.v).
    Notes: unlike the decomposition row above, cubicity is NOT assumed here,
      matching the source. *)
Definition every_prism_over_a_3_connected_planar_graph_is_hamil_statement : Prop :=
  forall (G : sgraph),
    wagner_planar G -> k_connected G 3 -> is_hamiltonian (cartesian_product G 'K_2).

(** Corpus row: opg:barnettes_conjecture
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/barnettes_conjecture/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/barnettes_conjecture.json
    English statement: (Open Problem Garden, "Barnette's Conjecture") Every
      planar, 3-connected, cubic, bipartite graph has a Hamilton cycle.
    Definitions: [wagner_planar G] - no K5 and no K3,3 minor, i.e. planarity by
      Wagner's theorem (base/theories/base.v); [k_connected G 3] (base.v);
      [regular G 3] - cubic (base.v); [bipartite G] - a two-valued vertex
      labelling giving different labels to the ends of every edge (base.v);
      [is_hamiltonian G] (this file, U2.v).
    Notes: Barnette's conjecture is usually stated for 3-connected cubic
      bipartite PLANAR graphs, equivalently for simple 3-polytopes with only
      even faces; the polytopal formulation is not available without the
      embedding layer, and the minor characterisation of planarity is used
      instead. *)
Definition barnettes_statement : Prop :=
  forall (G : sgraph),
    wagner_planar G -> k_connected G 3 -> regular G 3 -> bipartite G -> is_hamiltonian G.

(** Corpus row: opg:hamiltonian_cycles_in_line_graphs
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/hamiltonian_cycles_in_line_graphs/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/hamiltonian_cycles_in_line_graphs.json
    English statement: (Open Problem Garden, "Hamiltonian cycles in line graphs")
      For every graph G, if the line graph of G is 4-connected then the line
      graph of G is hamiltonian.
    Definitions: [line_graph G] - vertices are the edges of G, each canonically
      oriented once via [enum_rank], two distinct edges adjacent iff they share
      an endpoint (this file, U2.v); [k_connected _ 4]
      (base/theories/base.v); [is_hamiltonian] (U2.v).
    Notes: the statement quantifies over line graphs of SIMPLE graphs G, not
      over abstract 4-connected line graphs; line graphs of multigraphs are
      therefore out of scope.  base/theories/base.v carries a [line_graph] on
      multigraphs ([mgraph]); the local [line_graph] here is the [sgraph]
      analogue, not the same constant. *)
Definition hamiltonian_cycles_in_line_graphs_statement : Prop :=
  forall G : sgraph,
    k_connected (line_graph G) 4 -> is_hamiltonian (line_graph G).
