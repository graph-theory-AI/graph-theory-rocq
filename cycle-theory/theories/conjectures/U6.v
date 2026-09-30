(** * Cycle.conjectures.U6 — milestone U6 (namespace Cycle, plan v4)

    Statement-only formalizations (axiom-free: no Conjecture/Axiom/Parameter/
    Admitted) of eleven open problems of cycle theory: cycle double covers,
    edge-decompositions, eulerian decompositions, cycle covers, oddness and
    faithful covers.

    CARRIER: every row is an undirected MULTIGRAPH statement, so the carrier is
    coq-graph-theory's [mgraph] = [graph unit unit].  Subgraphs / cycles /
    matchings / covers are all represented as EDGE SETS [{set edge G}] (or
    sequences of them, for multisets of cycles).  This is the faithful object
    level for cycle theory: a "cycle" is a connected 2-regular edge set
    (a circuit), a "cycle double cover" a list of circuits hitting each edge
    exactly twice, etc.

    IMPORT ORDER: [mgraph] is imported BEFORE [base], because coq-graph-theory's
    [mgraph] ships a DIRECTED [line_graph] that would otherwise shadow base's
    undirected one (base re-exports the line/total-graph vocabulary).  We need
    the raw multigraph edge API: [edge G], [source]/[target] (= [endpoint]),
    [incident], [edges_at], [edges], [walk], [eseparates].

    CORE API used (verified on switch `digraph`, Rocq 9.1.1 + coq-graph-theory):
      - [edge G] : finType of edges; [source e]/[target e] : G endpoints;
      - [incident x e] : bool; [edges_at x] : {set edge G};
      - [edges x y] : {set edge G} the edges between x and y;
      - [uwalk x y w] : closed/open edge-walk predicate (w : seq (edge G));
      - [eseparates x y E] : every [x]–[y] walk meets the edge set [E];
      - [partition P D] : mathcomp partition of a finite set.

    AREA primitives introduced here (cycle-theory specific; would only migrate to
    graph-theory-base if a 2nd area needs them): [subdeg], [mdeg], [cubic],
    [bridgeless], [is_circuit], [even_subgraph], [cdc], [two_factor], [oddness_le],
    [faithful_cover], [admissible], transition systems and compatible
    decompositions.  [eulerian] and [edge_connected] are general graph notions
    (tagged [@MOVE-to-base] candidates). *)

From GraphTheory Require Import mgraph.
From GTBase Require Import base.
From Cycle.foundations Require Export connectivity.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Degrees and subgraph degrees *)

(** [mdeg], [subdeg] and [subgraph_kregular] now live in
    [Cycle.foundations.connectivity] (imported above).

    DEGREE CONVENTION (textbook).  [subdeg H v] is the number of ARC ENDS of the
    edge set [H] at [v], so a LOOP of [H] at [v] contributes 2; [mdeg v] is
    [subdeg [set: edge G] v].  Every degree notion below -- [two_factor],
    [even_subgraph], [is_matching], [is_path], [cubic], [eulerian] -- and
    [subgraph_kregular] / [is_circuit] of [Cycle.foundations.connectivity]
    inherit that convention, so a single loop IS an even subgraph and a circuit
    of length 1, as the classical conventions require, and the degree sum is
    twice the number of edges.  On a LOOPLESS carrier the arc-end count agrees
    with the incidence count [#|edges_at v :&: H|]
    ([connectivity.subdeg_loopless]), so every row guarded by [loopless],
    [cubic] or [simple_mgraph] reads exactly as before. *)

(** A 2-factor: a SPANNING 2-regular subgraph (every vertex has degree 2,
    counting arc ends, so a single loop at [v] already gives [v] degree 2). *)
Definition two_factor (G : mgraph) (F : {set edge G}) : Prop :=
  forall v : G, subdeg F v = 2.

(** An even subgraph ("binary cycle" / element of the cycle space):
    every vertex has even subgraph-degree.  Degrees count arc ends, so a LOOP
    contributes 2 and a single loop is an even subgraph, as the cycle space
    requires. *)
Definition even_subgraph (G : mgraph) (C : {set edge G}) : Prop :=
  forall v : G, ~~ odd (subdeg C v).

(** ** Connectivity at the multigraph level (via [uwalk]) *)

(** [walk_in], [mconnected], [connected_del_edges], [connected_del_verts],
    [two_connected], [edge_connected], [H_inc], [subgraph_connected] and the
    circuit predicate [is_circuit] now live in [Cycle.foundations.connectivity]
    (imported above). *)

(** ** Circuits and acyclicity *)

(** Acyclic: contains no circuit. *)
Definition acyclic (G : mgraph) (H : {set edge G}) : Prop :=
  forall C : {set edge G}, C \subset H -> ~ is_circuit C.

(** A path subgraph: nonempty, connected, acyclic, max degree ≤ 2 (arc ends,
    so a loop already saturates the bound at its vertex). *)
Definition is_path (G : mgraph) (P : {set edge G}) : Prop :=
  [/\ P != set0, subgraph_connected P, acyclic P & forall v : G, (subdeg P v <= 2)%N].

(** A matching: every vertex meets at most one matching edge.  Since [subdeg]
    counts arc ends, a LOOP can never belong to a matching -- it gives its
    vertex degree 2 -- which is again the textbook convention. *)
Definition is_matching (G : mgraph) (M : {set edge G}) : Prop :=
  forall v : G, (subdeg M v <= 1)%N.

(** A spanning tree (as an edge set): spanning + connected + acyclic.  Spanning
    is automatic from [walk]-connectivity over ALL vertices (an isolated vertex
    has no nontrivial walk to the others). *)
Definition spanning_connected (G : mgraph) (T : {set edge G}) : Prop :=
  forall x y : G, exists w, uwalk x y w /\ all (fun e => e \in T) w.

Definition spanning_tree (G : mgraph) (T : {set edge G}) : Prop :=
  spanning_connected T /\ acyclic T.

(** ** Bridges, cubic, eulerian *)

(** [is_bridge] and [bridgeless] now live in [Cycle.foundations.connectivity]
    (imported above). *)

(** Cubic: loopless and 3-regular ([mdeg] counts arc ends; [loopless] makes
    that agree with the incidence count, [connectivity.subdeg_loopless]). *)
Definition cubic (G : mgraph) : Prop :=
  loopless G /\ forall v : G, mdeg v = 3.

(** Simple multigraph: loopless and at most one edge between any pair OF
    VERTICES, counted UNDIRECTEDLY.  [mgraph.edges x y] only counts the arcs
    whose [source] is [x] and whose [target] is [y], so the undirected
    multiplicity of the pair {x,y} is [#|edges x y| + #|edges y x|] (cf. the
    carrier convention in [Cycle.foundations.connectivity]): bounding that sum
    is what rules out a doubled edge carried by two ANTIPARALLEL arcs.  At
    [x = y] the bound reads [2 * #|edges x x| <= 1], i.e. no loop, which
    [loopless] already gives. *)
Definition simple_mgraph (G : mgraph) : Prop :=
  loopless G /\ forall x y : G, (#|edges x y| + #|edges y x| <= 1)%N.

(** Eulerian: connected with all degrees even ([mdeg] counts arc ends, so a
    loop contributes 2 and never breaks evenness -- the textbook convention,
    under which a loop graph is eulerian).
    [@MOVE-to-base]: general graph notion, migrate to graph-theory-base when a
    second area needs it. *)
Definition eulerian (G : mgraph) : Prop :=
  mconnected G /\ forall v : G, ~~ odd (mdeg v).

(** An eulerian tour: a closed walk traversing every edge exactly once. *)
Definition is_eulerian_tour (G : mgraph) (w : seq (edge G)) : Prop :=
  (exists x : G, walk x x w) /\ (forall e : edge G, count (pred1 e) w = 1).

(** ** Edge partitions and decompositions *)

(** A list of edge sets partitions ALL edges: each edge in exactly one part. *)
Definition edge_partitionT (G : mgraph) (D : seq {set edge G}) : Prop :=
  forall e : edge G, count (fun C : {set edge G} => e \in C) D = 1.

(** A list of edge sets partitions the edges of [H]: each edge of [H] in exactly
    one part, each non-[H] edge in none. *)
Definition edge_partition_of (G : mgraph) (H : {set edge G}) (D : seq {set edge G}) : Prop :=
  forall e : edge G, count (fun C : {set edge G} => e \in C) D = ((e \in H) : nat).

(** Decomposition of [H] into circuits. *)
Definition cycle_decomposition_of (G : mgraph) (H : {set edge G})
    (D : seq {set edge G}) : Prop :=
  (forall C, C \in D -> is_circuit C) /\ edge_partition_of H D.

(** Decomposition of the WHOLE edge set into circuits. *)
Definition cycle_decomposition (G : mgraph) (D : seq {set edge G}) : Prop :=
  (forall C, C \in D -> is_circuit C) /\ edge_partitionT D.

(** Decomposition into paths. *)
Definition path_decomposition (G : mgraph) (D : seq {set edge G}) : Prop :=
  (forall P, P \in D -> is_path P) /\ edge_partitionT D.

(** ** Cycle covers *)

(** A cycle double cover: a list of circuits with every edge covered exactly twice. *)
Definition cdc (G : mgraph) (L : seq {set edge G}) : Prop :=
  (forall C, C \in L -> is_circuit C) /\
  (forall e : edge G, count (fun C : {set edge G} => e \in C) L = 2).

(** A faithful cover for an edge weighting [p]: circuits covering [e] exactly [p e] times. *)
Definition faithful_cover (G : mgraph) (p : edge G -> nat) (L : seq {set edge G}) : Prop :=
  (forall C, C \in L -> is_circuit C) /\
  (forall e : edge G, count (fun C : {set edge G} => e \in C) L = p e).

(** The edge cut [cut] now lives in [Cycle.foundations.connectivity]
    (imported above). *)

(** Admissible weighting: across every cut, the total is even and no single edge
    exceeds the sum of the others (i.e. 2·p(e) ≤ p(δ(S))). *)
Definition admissible (G : mgraph) (p : edge G -> nat) : Prop :=
  forall (S : {set G}) (e : edge G), e \in cut S ->
    (2 * p e <= \sum_(f in cut S) p f)%N /\ ~~ odd (\sum_(f in cut S) p f).

(** ** Transition systems and compatible decompositions *)

(** A 2-transition system: at every vertex [v], [P v] partitions the incident
    edges into transitions, each of size exactly 2. *)
Definition transition2_system (G : mgraph) (P : G -> {set {set edge G}}) : Prop :=
  (forall v : G, partition (P v) (edges_at v)) /\
  (forall (v : G) (T : {set edge G}), T \in P v -> #|T| = 2).

(** A cycle decomposition is compatible with [P] if no circuit uses a transition
    of [P] (at each vertex its two circuit-edges are not a [P]-transition). *)
Definition compatible_decomposition (G : mgraph) (P : G -> {set {set edge G}})
    (D : seq {set edge G}) : Prop :=
  cycle_decomposition D /\
  (forall C, C \in D -> forall v : G, (edges_at v :&: C) \notin P v).

(** Two edges are consecutive in the cyclic tour [w]. *)
Definition cyc_pairs (G : mgraph) (w : seq (edge G)) : seq (edge G * edge G) :=
  zip w (rot 1 w).

Definition two_consecutive (G : mgraph) (w : seq (edge G)) (C : {set edge G}) : bool :=
  has (fun p => (p.1 \in C) && (p.2 \in C)) (cyc_pairs w).

(** Oddness ≤ [k]: some 2-factor decomposes into circuits, at most [k] of them odd. *)
Definition oddness_le (G : mgraph) (k : nat) : Prop :=
  exists (F : {set edge G}) (D : seq {set edge G}),
    [/\ two_factor F, cycle_decomposition_of F D & (count (fun C : {set edge G} => odd #|C|) D <= k)%N].

(** ================================================================= *)
(** ** Row 1 — Cycle double covers containing a predefined 2-regular subgraph *)
(** Corpus row: opg:cycle_double_covers_containing_predefined_2_regular_subgraphs
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/cycle_double_covers_containing_predefined_2_regular_subgraphs/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/cycle_double_covers_containing_predefined_2_regular_subgraphs.json
    English statement: (Open Problem Garden, "Cycle Double Covers Containing Predefined
      2-Regular Subgraphs")
      Let G be a cubic multigraph with at least one vertex that is 2-connected, that is, has
      at least three vertices and stays connected after deleting any single vertex, and let
      S be a set of edges in which every vertex lies on either no edge or exactly two
      edges, such that G with the edges of S deleted is still connected. Then G has a cycle
      double cover, a list of circuits covering every edge exactly twice, which contains
      all the cycles of S: S decomposes into circuits, each of which is a member of that
      list.
    Definitions: [cubic G] - loopless and every vertex on exactly three edges (U6.v);
      [two_connected G] - at least three vertices and connected after deleting any one
      vertex, [connected_del_edges S] - connected using only edges outside S,
      [subgraph_kregular S k] - every vertex has S-degree 0 or k, [is_circuit C] - a
      nonempty connected 2-regular edge set, [subdeg] and [mdeg] - degrees counting ARC
      ENDS at a vertex, so a loop contributes 2
      (cycle-theory/theories/foundations/connectivity.v);
      [cdc L] - every member is a circuit and every edge is counted exactly twice over L
      (U6.v); [cycle_decomposition_of S D] - the members of D are circuits and partition
      the edges of S (U6.v); [edge_partition_of] (U6.v).
    Notes: "contains S" is rendered as: some circuit decomposition D of S has all its
      members among the members of the cycle double cover L, using [{subset D <= L}].
      Subgraphs are edge sets, so "2-regular subgraph" is the non-spanning notion, degree 0
      or 2 at each vertex. *)
Definition cycle_double_covers_containing_predefined_2_regular_statement : Prop :=
  forall (G : mgraph) (S : {set edge G}),
    (0 < #|G|)%N -> cubic G -> two_connected G ->
    subgraph_kregular S 2 -> connected_del_edges S ->
    exists L : seq {set edge G},
      cdc L /\
      exists D : seq {set edge G},
        cycle_decomposition_of S D /\ {subset D <= L}.

(** ** Row 2 — 3-Decomposition Conjecture *)
(** Corpus row: opg:3_decomposition_conjecture
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/3_decomposition_conjecture/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/3_decomposition_conjecture.json
    English statement: (Open Problem Garden, "3-Decomposition Conjecture")
      Every connected cubic multigraph G with at least one vertex has three edge sets T, F
      and M such that T is a spanning tree, F is 2-regular, every vertex lying on no edge
      or on exactly two edges of F, M is a matching, every vertex lying on at most one edge
      of M, and every edge of G belongs to exactly one of T, F, M.
    Definitions: [spanning_connected T] and [spanning_tree T] - every two vertices are
      joined by a walk using only edges of T, and T contains no circuit (U6.v);
      [acyclic H] - no subset of H is a circuit (U6.v); [is_matching M] - every vertex has
      M-degree at most one (U6.v); [edge_partitionT D] - every edge of G is in exactly one
      member of the list D (U6.v); [cubic] (U6.v); [subgraph_kregular], [mconnected],
      [is_circuit], [subdeg] - the degree counting ARC ENDS, so a loop contributes 2
      (cycle-theory/theories/foundations/connectivity.v).
    Notes: "a family of cycles" is modelled by a single 2-regular edge set F, which is
      exactly a disjoint union of circuits, rather than by a list of circuits; spanning is
      automatic from walk-connectivity over all vertices. *)
Definition three_decomposition_statement : Prop :=
  forall G : mgraph,
    (0 < #|G|)%N -> cubic G -> mconnected G ->
    exists T F M : {set edge G},
      [/\ spanning_tree T, subgraph_kregular F 2, is_matching M
        & edge_partitionT [:: T; F; M]].

(** ** Row 3 — Decomposing a connected graph into paths *)
(** Corpus row: opg:decomposing_a_connected_graph_into_paths
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/decomposing_a_connected_graph_into_paths/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/decomposing_a_connected_graph_into_paths.json
    English statement: (Open Problem Garden, "Decomposing a connected graph into paths.")
      Every simple connected multigraph G with n vertices, n at least one, and at least one
      edge admits a list of edge sets, each of them a path, such that every edge of G lies
      in exactly one of them and the list has at most floor((n+1)/2) members.
    Definitions: [simple_mgraph G] - loopless and at most one edge between any two vertices
      (U6.v); [is_path P] - P is nonempty, connected, contains no circuit and every vertex
      has P-degree at most two (U6.v); [path_decomposition D] - every member of D is a path
      and every edge is in exactly one member (U6.v); [acyclic], [edge_partitionT] (U6.v);
      [mconnected], [subgraph_connected], [subdeg] - the degree counting ARC ENDS, so a
      loop contributes 2, [is_circuit] (cycle-theory/theories/foundations/connectivity.v).
    Notes: the bound one half of (n+1) is written with natural division, [(#|G| + 1) %/ 2],
      which is its floor; since the number of paths is an integer this is equivalent to the
      real inequality. *)
Definition decomposing_a_connected_graph_into_paths_statement : Prop :=
  forall G : mgraph,
    (0 < #|G|)%N -> (0 < #|edge G|)%N -> simple_mgraph G -> mconnected G ->
    exists D : seq {set edge G},
      path_decomposition D /\ (size D <= (#|G| + 1) %/ 2)%N.

(** ** Row 4 — Decomposing an eulerian graph into cycles *)
(** Corpus row: opg:decomposing_an_eulerian_graph_into_cycles
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/decomposing_an_eulerian_graph_into_cycles/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/decomposing_an_eulerian_graph_into_cycles.json
    English statement: (Open Problem Garden, "Decomposing an eulerian graph into cycles")
      Every simple eulerian multigraph G with n vertices, n at least one, and at least one
      edge, that is, connected with every vertex of even degree, admits a list of circuits
      such that every edge of G lies in exactly one of them and the list has at most
      floor((n-1)/2) members.
    Definitions: [simple_mgraph G] - loopless and at most one edge between any two vertices
      (U6.v); [eulerian G] - connected and every vertex has even multigraph degree, degrees
      counting ARC ENDS so that a loop contributes 2 (U6.v);
      [cycle_decomposition D] - every member of D is a circuit and every edge of G is in
      exactly one member (U6.v); [edge_partitionT] (U6.v); [is_circuit], [mconnected],
      [mdeg] - the arc-end degree, a loop contributing 2
      (cycle-theory/theories/foundations/connectivity.v).
    Notes: the bound one half of (n-1) is written with truncated natural subtraction and
      natural division, [(#|G| - 1) %/ 2], which is its floor; this is equivalent to the
      real inequality because the number of circuits is an integer, and the guard
      [0 < #|G|] makes the truncated subtraction harmless. *)
Definition decomposing_an_eulerian_graph_into_cycles_statement : Prop :=
  forall G : mgraph,
    (0 < #|G|)%N -> (0 < #|edge G|)%N -> simple_mgraph G -> eulerian G ->
    exists D : seq {set edge G},
      cycle_decomposition D /\ (size D <= (#|G| - 1) %/ 2)%N.

(** ** Row 5 — Eulerian decomposition avoiding two consecutive tour edges *)
(** Corpus row: opg:decomposing_an_eulerian_graph_into_cycles_with_no_two_consecutives_edges_on_a_prescirbed_eulerian_tour
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/decomposing_an_eulerian_graph_into_cycles_with_no_two_consecutives_edges_on_a_prescirbed_eulerian_tour/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/decomposing_an_eulerian_graph_into_cycles_with_no_two_consecutives_edges_on_a_prescirbed_eulerian_tour.json
    English statement: (Open Problem Garden, "Decomposing an eulerian graph into cycles
      with no two consecutive edges on a prescribed eulerian tour")
      Let G be an eulerian multigraph with at least one vertex, connected with all degrees
      even, in which every vertex lies on at least four edges, and let w be an eulerian
      tour of G, a closed walk using every edge exactly once. Then the edges of G can be
      partitioned into circuits none of which contains two edges that are consecutive
      along w, the tour being read cyclically so that its last and first edges are also
      consecutive.
    Definitions: [eulerian G] - connected with every multigraph degree even, degrees
      counting ARC ENDS so that a loop contributes 2 (U6.v);
      [is_eulerian_tour w] - w is a closed walk from some vertex to itself using every edge
      exactly once (U6.v); [cyc_pairs w] - the list of cyclically consecutive pairs of w,
      w zipped with its rotation by one (U6.v); [two_consecutive w C] - some cyclically
      consecutive pair of w has both edges in C (U6.v); [cycle_decomposition D] - the
      members of D are circuits and every edge is in exactly one of them (U6.v);
      [is_circuit], [mdeg] - the arc-end degree, a loop contributing 2
      (cycle-theory/theories/foundations/connectivity.v); [walk] - a DIRECTED walk following the
      intrinsic source-to-target orientation of the multigraph edges (coq-graph-theory
      mgraph).
    Notes: the eulerian tour is required to be a [walk], which follows the intrinsic edge
      orientations, rather than an undirected [uwalk]; the hypothesis therefore only bites
      on multigraphs whose reference orientation is itself an eulerian orientation. Every
      eulerian multigraph has such a presentation, and the conclusion does not mention
      orientations, so the statement is equivalent up to reorienting edges, but the
      universally quantified form is formally weaker than the undirected one. *)
Definition decomposing_an_eulerian_graph_into_cycles_with_no_tw_statement : Prop :=
  forall (G : mgraph) (w : seq (edge G)),
    (0 < #|G|)%N -> eulerian G -> (forall v : G, (4 <= mdeg v)%N) ->
    is_eulerian_tour w ->
    exists D : seq {set edge G},
      cycle_decomposition D /\ (forall C, C \in D -> ~~ two_consecutive w C).

(** ** Row 6 — Compatible decompositions of eulerian graphs *)
(** Corpus row: opg:decomposing_eulerian_graphs
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/decomposing_eulerian_graphs/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/decomposing_eulerian_graphs.json
    English statement: (Open Problem Garden, "Decomposing eulerian graphs")
      For every eulerian multigraph G with at least one vertex and at least one edge that is
      6-edge-connected, deleting fewer than six edges never disconnects it, and every
      2-transition system P on G, which at each vertex v partitions the edges incident with
      v into pairs, the edges of G can be partitioned into circuits such that at every
      vertex no circuit enters and leaves through a pair belonging to P, that is, for every
      circuit C and vertex v the set of edges of C at v is not a transition of P at v.
    Definitions: [transition2_system P] - for every vertex, P v is a partition of the edges
      at v into blocks of size exactly two (U6.v); [compatible_decomposition P D] - D is a
      circuit decomposition of all edges and for every member C and vertex v the set
      [edges_at v :&: C] is not a block of P v (U6.v); [cycle_decomposition],
      [edge_partitionT] (U6.v); [eulerian] - connected with every arc-end degree even, a
      loop contributing 2 (U6.v); [edge_connected G k], [is_circuit]
      (cycle-theory/theories/foundations/connectivity.v); [partition], [edges_at] (MathComp finset, coq-graph-theory mgraph).
    Notes: compatibility is stated as "the whole trace of C at v is not a P-transition",
      which for a circuit through v, whose trace at v has two edges, is exactly the
      usual condition that the circuit does not use a transition of P.
      LOOP-DEGREE REPAIR (2026-09-23): this row was a FOURTH victim of the old degree
      convention -- undiagnosed until the second-reader re-read -- and its body is
      unchanged. Its guards are [edge_connected G 6] and [eulerian G], with no
      looplessness, so loopful carriers are admitted. Take the one-vertex multigraph with
      TWO loops e1, e2. It is eulerian (one vertex, and its degree is 4 now, 2 under the
      old count, even either way) and 6-edge-connected (deleting edges leaves the single
      vertex, still connected), and P v = [set [set e1; e2]] is a [transition2_system]:
      it partitions [edges_at v] = {e1, e2} into one block of size two. While a LOOP had
      degree 1, neither [set e1] nor [set e2] was an [is_circuit], so the ONLY cycle
      decomposition available was [:: [set e1; e2]], whose trace [edges_at v :&: [set e1;
      e2]] IS the transition: no compatible decomposition existed and the row was
      refutable on that graph, although the conjecture plainly holds there. With a loop of
      degree 2 each loop is a circuit of length 1 and [:: [set e1]; [set e2]] is a
      compatible decomposition (each trace is a singleton, never a two-element transition).
      Machine-checked instance: [grounding_U6.u6_decomposing_eulerian_G2loop] exhibits the
      hypotheses AND the conclusion of THIS row on that carrier, via
      [grounding_U6.compatible_decomposition_G2loop]. Residual notion-level remark
      (observation, not a defect of this row): [transition2_system] partitions
      [edges_at v], an INCIDENCE set, whereas a classical 2-transition system partitions
      the edge ENDS at v, of which a loop occupies two; on a loopless carrier the two
      agree. See meta/X211-X229_faithfulness_audit.md and meta/STATEMENT_IMPROVEMENTS.md. *)
Definition decomposing_eulerian_graphs_statement : Prop :=
  forall (G : mgraph) (P : G -> {set {set edge G}}),
    (0 < #|G|)%N -> (0 < #|edge G|)%N -> edge_connected G 6 -> eulerian G ->
    transition2_system P ->
    exists D : seq {set edge G}, compatible_decomposition P D.

(** ** Row 7 — (5,2)-cycle covers *)
(** Corpus row: opg:m_n_cycle_covers
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/m_n_cycle_covers/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/m_n_cycle_covers.json
    English statement: (Open Problem Garden, "(m,n)-cycle covers")
      Every bridgeless multigraph with at least one vertex and at least one edge has a
      (5,2)-cycle cover: a list of exactly five even subgraphs, edge sets in which every
      vertex has even degree, such that every edge of the graph belongs to exactly two
      members of the list.
    Definitions: [even_subgraph C] - every vertex has even C-degree, that is, C is an
      element of the binary cycle space, a disjoint union of circuits (U6.v); [subdeg] -
      the degree counting ARC ENDS, so a loop contributes 2 and a single loop is an even
      subgraph, and [bridgeless] (cycle-theory/theories/foundations/connectivity.v).
    Notes: MODELLING CHOICE. In a (5,2)-cover, as in the strong 5-cycle-double-cover row
      below, a "cycle" means an even subgraph, an element of the cycle space and hence a
      disjoint union of circuits, not necessarily a single circuit; this is the standard
      even-subgraph formulation, so the members are typed [even_subgraph]. The cycle
      double cover row further down instead uses [cdc], whose members are single circuits.
      The cover is a list, so repeated members are allowed and the covering count is taken
      over positions.
      LOOP-DEGREE REPAIR (2026-09-23): this row was a THIRD victim of the old degree
      convention, alongside [cycle_double_cover_statement] and
      [X212.orientable_five_cycle_double_cover_statement], and its body is unchanged.
      While [connectivity.subdeg] counted the edges INCIDENT to a vertex, a LOOP had degree
      1, so NO edge set containing a loop was an [even_subgraph]. On the one-vertex
      one-loop multigraph [Lp] -- which is bridgeless, since a loop is never a cut edge
      ([connectivity.loop_not_bridge]), and has a vertex and an edge -- the single loop
      would have had to occupy exactly two of the five list positions, and every set
      containing it had odd degree at the vertex: the conclusion was UNSATISFIABLE although
      the conjecture plainly holds there (take the whole edge set twice). [subdeg] now
      counts ARC ENDS, so a loop contributes 2 and a single loop is an even subgraph;
      [connectivity.subdegE] ("degree = incidences + loops") and
      [connectivity.subdeg_loopless] show the two readings agree on a loopless carrier, so
      no row guarded by [loopless], [cubic] or [simple_mgraph] changes meaning. The
      conclusion is now REALISED on that carrier by
      [grounding_X212.x212_m_n_cover_Lp], which is this row's conclusion instantiated at
      [Lp] with L = [:: setT; setT; set0; set0; set0]. See
      meta/X211-X229_faithfulness_audit.md and meta/STATEMENT_IMPROVEMENTS.md. *)
Definition m_n_cycle_covers_statement : Prop :=
  forall G : mgraph,
    (0 < #|G|)%N -> (0 < #|edge G|)%N -> bridgeless G ->
    exists L : seq {set edge G},
      [/\ size L = 5,
          (forall C, C \in L -> even_subgraph C)
        & (forall e : edge G, count (fun C : {set edge G} => e \in C) L = 2)].

(** ** Row 8 — Odd cycles and low oddness *)
(** Corpus row: opg:odd_cycles_and_low_oddness
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/odd_cycles_and_low_oddness/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/odd_cycles_and_low_oddness.json
    English statement: (Open Problem Garden, "Odd cycles and low oddness")
      Let G be a bridgeless cubic multigraph with at least one vertex. If every circuit
      contained in any 2-factor of G, a spanning edge set in which every vertex lies on
      exactly two edges, has an odd number of edges, then the oddness of G is at most 2:
      some 2-factor of G decomposes into circuits of which at most two are odd.
    Definitions: [two_factor F] - every vertex has F-degree exactly two, a spanning
      2-regular subgraph, degrees counting ARC ENDS so that a loop contributes 2 (U6.v);
      [oddness_le G k] - some 2-factor has a circuit decomposition with at most k circuits
      of odd size (U6.v); [cycle_decomposition_of],
      [edge_partition_of] (U6.v); [cubic] (U6.v); [is_circuit], [bridgeless], [subdeg] -
      the arc-end degree, a loop contributing 2, immaterial here since [cubic] forces
      [loopless] (cycle-theory/theories/foundations/connectivity.v).
    Notes: the oddness bound is expressed directly as the existence of a 2-factor together
      with a circuit decomposition of it having at most two odd members, rather than by
      defining the minimum; this is equivalent to "the minimum over 2-factors is at most
      2". Odd circuits are counted by odd cardinality of the edge set, which for a circuit
      is its length. *)
Definition odd_cycles_and_low_oddness_statement : Prop :=
  forall G : mgraph,
    (0 < #|G|)%N -> cubic G -> bridgeless G ->
    (forall F : {set edge G}, two_factor F ->
       forall C : {set edge G}, C \subset F -> is_circuit C -> odd #|C|) ->
    oddness_le G 2.

(** ** Row 9 — Faithful cycle covers *)
(** Corpus row: opg:faithful_cycle_covers
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/faithful_cycle_covers/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/faithful_cycle_covers.json
    English statement: (Open Problem Garden, "Faithful cycle covers")
      Let G be a multigraph with at least one vertex and at least one edge and let p assign
      a natural number to every edge. If p is admissible, meaning that for every vertex set
      S and every edge e of the cut of S the weight of e counted twice is at most the total
      weight of the cut and the total weight of the cut is even, and if p(e) is even for
      every edge e, then there is a list of circuits covering every edge e exactly p(e)
      times.
    Definitions: [admissible p] - for every vertex set S and every edge e in [cut S],
      2 * p e is at most the sum of p over [cut S] and that sum is even (U6.v);
      [faithful_cover p L] - every member of L is a circuit and every edge e is counted
      exactly p e times over L (U6.v); [cut S], [is_circuit] (cycle-theory/theories/foundations/connectivity.v).
    Notes: the weighting is [edge G -> nat] whereas the source writes p : E -> Z; only
      nonnegative weights are covered, which is the standard setting for faithful covers,
      since a cover count is a nonnegative number, but it is formally a restriction of the
      source's hypothesis class. *)
Definition faithful_cycle_covers_statement : Prop :=
  forall (G : mgraph) (p : edge G -> nat),
    (0 < #|G|)%N -> (0 < #|edge G|)%N -> admissible p ->
    (forall e : edge G, ~~ odd (p e)) ->
    exists L : seq {set edge G}, faithful_cover p L.

(** ** Row 10 — Strong 5-cycle double cover conjecture *)
(** Corpus row: opg:strong_5_cycle_double_cover_conjecture
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/strong_5_cycle_double_cover_conjecture/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/strong_5_cycle_double_cover_conjecture.json
    English statement: (Open Problem Garden, "Strong 5-cycle double cover conjecture")
      For every bridgeless cubic multigraph G with at least one vertex and every circuit C
      of G there is a list of exactly five even subgraphs of G such that every edge of G
      lies in exactly two of them and C is contained in one of the five.
    Definitions: [even_subgraph D] - every vertex has even D-degree, an element of the
      cycle space (U6.v); [cubic] (U6.v); [is_circuit C] - a nonempty connected 2-regular
      edge set, [bridgeless], [subdeg] - the degree counting ARC ENDS, so a loop
      contributes 2, immaterial here since [cubic] forces [loopless]
      (cycle-theory/theories/foundations/connectivity.v).
    Notes: as in the (5,2)-cycle-cover row above, the five "cycles" are even subgraphs,
      disjoint unions of circuits, not necessarily single circuits; containment of C in one
      of them is set inclusion of edge sets. The cover is a list, so members may
      repeat. *)
Definition strong_5_cycle_double_cover_statement : Prop :=
  forall (G : mgraph) (C : {set edge G}),
    (0 < #|G|)%N -> cubic G -> bridgeless G -> is_circuit C ->
    exists L : seq {set edge G},
      [/\ size L = 5,
          (forall D, D \in L -> even_subgraph D),
          (forall e : edge G, count (fun D : {set edge G} => e \in D) L = 2)
        & (exists D, D \in L /\ C \subset D)].

(** ** Row 11 — Cycle double cover conjecture *)
(** Corpus row: opg:cycle_double_cover_conjecture
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/cycle_double_cover_conjecture/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/cycle_double_cover_conjecture.json
    English statement: (Open Problem Garden, "Cycle double cover conjecture")
      Every bridgeless multigraph with at least one vertex and at least one edge has a
      cycle double cover: a list of circuits, each a nonempty connected 2-regular edge set,
      such that every edge of the graph lies in exactly two members of the list.
    Definitions: [cdc L] - every member of L is a circuit and every edge is counted exactly
      twice over L (U6.v); [is_circuit], [bridgeless] - no edge is a cut edge, an edge that
      every UNDIRECTED walk between its endpoints must use, [subgraph_connected],
      [subgraph_kregular C 2] - every vertex has C-degree 0 or 2, and [subdeg] - that
      degree, counting ARC ENDS at the vertex, so that a LOOP contributes 2 and a single
      loop is a circuit of length 1 (cycle-theory/theories/foundations/connectivity.v).
    Notes: here the cover members are single circuits, the stricter reading of "cycle",
      whereas the (5,2)-cover and strong 5-cycle-double-cover rows above use even
      subgraphs; for the unrestricted cycle double cover conjecture the two readings are
      equivalent, since an even subgraph splits into circuits, but the Rocq bodies differ.
      The list form allows repeated members.
      REPAIRED (foundation repair, 2026-09-23): [is_bridge] is now stated with
      the UNDIRECTED [uwalk] of GTBase.base ([ueseparates] in
      cycle-theory/theories/foundations/connectivity.v), so [bridgeless] means
      "no CUT EDGE", the textbook notion. The earlier reading went through
      coq-graph-theory's [eseparates] over the DIRECTED [walk] and demanded an
      alternative DIRECTED route for every arc, which excluded every cycle,
      every cubic simple graph and every snark from the hypothesis class; that
      caveat no longer applies. Witnesses of the repaired notion:
      [grounding_X212.x212_bridgeless_Tri] (the cyclically oriented triangle IS
      bridgeless) and [grounding_X212.x212_not_bridgeless_G1] (an edge whose
      deletion separates its ends is a bridge).
      LOOP-DEGREE REPAIR (2026-09-23, main session): a SECOND, independent
      defect of the shared degree layer is fixed as well, and the row's body is
      unchanged. [connectivity.subdeg] used to count the edges INCIDENT to a
      vertex, so a LOOP had degree 1: the one-loop edge set was neither
      2-regular nor a circuit, while the one-vertex one-loop multigraph is
      connected and bridgeless (a loop is never a cut edge,
      [connectivity.loop_not_bridge]). This committed row was therefore
      axiom-free REFUTABLE on that graph, although the conjecture plainly holds
      there - cover the loop twice. [subdeg H v] is now the number of ARC ENDS
      of H at v, so a loop contributes 2, the textbook convention;
      [connectivity.subdegE] is the identity "degree = incidences + loops" and
      [connectivity.subdeg_loopless] shows the two readings agree on a loopless
      carrier, so no row guarded by [loopless], [cubic] or [simple_mgraph]
      changes meaning. The loop graph now satisfies the conclusion:
      [grounding_U6.mdeg_Gloop] (degree 2), [grounding_U6.is_circuit_Gloop] and
      [grounding_U6.cdc_Gloop], restated on the bm-026 side as
      [grounding_X212.x212_is_circuit_Lp] and [grounding_X212.x212_cdc_Lp]. The
      refutation hint meta/probe_hints/cycle_double_cover_statement.v no longer
      compiles (meta/vacuity_probe.py reports hint-stale-FIX-OK), and neither
      does its sibling for
      [X212.orientable_five_cycle_double_cover_statement], which the same graph
      refuted through [even_subgraph] instead of [is_circuit]. See
      meta/X211-X229_faithfulness_audit.md and meta/STATEMENT_IMPROVEMENTS.md. *)
Definition cycle_double_cover_statement : Prop :=
  forall G : mgraph,
    (0 < #|G|)%N -> (0 < #|edge G|)%N -> bridgeless G ->
    exists L : seq {set edge G}, cdc L.
