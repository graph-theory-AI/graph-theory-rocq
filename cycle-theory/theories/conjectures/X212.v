(** * Cycle.conjectures.X212 -- Bondy-Murty cycle and edge-decomposition rows (wave X212, 2026-09-23) *)

(** Eight rows of Appendix A of Bondy-Murty, "Graph Theory" (corpus tag [bm]),
    routed to cycle-theory by [meta/v2_classification.json]: the Barat-Thomassen
    tree-decomposition conjecture (bm-011), Bondy's small cycle double cover
    conjecture (bm-013), the linear arboricity conjecture (bm-016), the
    orientable five cycle double cover conjecture (bm-026), Kotzig's unique
    k-path conjecture (bm-062), Smith's conjecture on longest cycles (bm-064),
    Bondy's linear-length cycle conjecture for cyclically 4-edge-connected cubic
    graphs (bm-065) and Birmele's conjecture on long cycles (bm-066).

    CARRIER per row.  The three rows that live in the cycle-double-cover /
    edge-decomposition family of [U6.v] are MULTIGRAPH statements on
    coq-graph-theory's [mgraph] (bm-013, bm-026), so that they share the
    [is_circuit] / [cdc] / [even_subgraph] / [bridgeless] vocabulary with the
    already committed CDC rows and the corpus implication edges e209 / e218 /
    e246 are stated between comparable objects.  The remaining rows speak about
    SIMPLE graphs ("simple k-edge-connected graph", "simple k-regular graph",
    "graph", "k-connected graph", "cubic graph") and use [sgraph] with the
    GTBase vocabulary ([k_edge_connected], [k_connected], [regular], [E(G)],
    [is_tree], [ucycleb], [ceil_div]).

    IMPORT ORDER: [mgraph] is imported BEFORE [base], as in [U6.v] / [D1.v],
    because coq-graph-theory's [mgraph] ships a DIRECTED [line_graph] that would
    otherwise shadow base's undirected one. *)

From GraphTheory Require Import mgraph.
From GTBase Require Export base.
From Cycle.foundations Require Export connectivity.
From Cycle.conjectures Require Export U6.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local x212 vocabulary ***********************************************)

(** *** Copies of a tree inside a simple graph (bm-011)

    A COPY of the simple graph [T] inside [G] is the image of an injective
    adjacency-preserving map [f : T -> G]; its edge set is the set of the
    2-element vertex sets [[set f x; f y]] for the adjacent pairs [x -- y] of
    [T].  Injectivity makes the copy have exactly [#|E(T)|] edges. *)

Definition x212_copy_edges (G T : sgraph) (f : T -> G) : {set {set G}} :=
  [set e : {set G} |
     [exists p : T * T, (p.1 -- p.2) && (e == [set f p.1; f p.2])]].

Definition x212_copy_of (G T : sgraph) (A : {set {set G}}) : Prop :=
  exists f : T -> G,
    [/\ injective f,
        (forall x y : T, x -- y -> f x -- f y)
      & A = x212_copy_edges f].

(** A DECOMPOSITION of [E(G)] into copies of [T]: a list of edge sets, each a
    copy of [T], such that every 2-element vertex set lies in exactly one member
    when it is an edge of [G] and in none otherwise. *)
Definition x212_decomposition_into_copies (G T : sgraph)
    (D : seq {set {set G}}) : Prop :=
  (forall A, A \in D -> x212_copy_of T A) /\
  (forall e : {set G},
     count (fun A : {set {set G}} => e \in A) D = ((e \in E(G)) : nat)).

(** *** Linear forests and linear arboricity (bm-016)

    Same encoding as [topological-graph-theory/.../X23.v]: an edge colouring is
    a map on 2-element vertex sets, colour class [i] is the spanning subgraph of
    the [G]-edges coloured [i], and a linear forest is an acyclic subgraph of
    maximum degree at most two, i.e. a disjoint union of paths. *)

Definition x212_edge_colour_rel
    (G : sgraph) (q : nat) (col : {set G} -> 'I_q) (i : 'I_q) : rel G :=
  fun x y => (x -- y) && (col [set x; y] == i).

Lemma x212_edge_colour_sym
    (G : sgraph) (q : nat) (col : {set G} -> 'I_q) (i : 'I_q) :
  symmetric (x212_edge_colour_rel col i).
Proof. by move=> x y; rewrite /x212_edge_colour_rel sg_sym setUC. Qed.

Lemma x212_edge_colour_irrefl
    (G : sgraph) (q : nat) (col : {set G} -> 'I_q) (i : 'I_q) :
  irreflexive (x212_edge_colour_rel col i).
Proof. by move=> x; rewrite /x212_edge_colour_rel sg_irrefl. Qed.

Definition x212_colour_graph
    (G : sgraph) (q : nat) (col : {set G} -> 'I_q) (i : 'I_q) : sgraph :=
  SGraph (x212_edge_colour_sym col i) (x212_edge_colour_irrefl col i).

Definition x212_linear_forest_colour
    (G : sgraph) (q : nat) (col : {set G} -> 'I_q) (i : 'I_q) : Prop :=
  is_forest [set: x212_colour_graph col i] /\ Delta (x212_colour_graph col i) <= 2.

Definition x212_linear_arboricity_at_most (G : sgraph) (q : nat) : Prop :=
  exists col : {set G} -> 'I_q, forall i : 'I_q, x212_linear_forest_colour col i.

Definition x212_linear_arboricity (G : sgraph) (q : nat) : Prop :=
  x212_linear_arboricity_at_most G q /\
  forall q' : nat, x212_linear_arboricity_at_most G q' -> q <= q'.

(** *** Orientations of even subgraphs (bm-026)

    An orientation of the multigraph [G] is a boolean [d] on the edges: [true]
    keeps the intrinsic [source -> target] direction, [false] reverses it. *)

Definition x212_tail (G : mgraph) (d : edge G -> bool) (e : edge G) : G :=
  if d e then source e else target e.

Definition x212_head (G : mgraph) (d : edge G -> bool) (e : edge G) : G :=
  if d e then target e else source e.

(** [d] orients the edge set [C] in a balanced ("eulerian") way: inside [C],
    every vertex has as many outgoing as incoming edges. *)
Definition x212_balanced (G : mgraph) (C : {set edge G}) (d : edge G -> bool) : Prop :=
  forall v : G,
    #|[set e in C | x212_tail d e == v]| = #|[set e in C | x212_head d e == v]|.

(** An ORIENTABLE double cover by five even subgraphs: five edge sets, each an
    even subgraph carrying a balanced orientation, covering every edge exactly
    twice, the two covering members traversing it in opposite directions. *)
Definition x212_orientable_5_even_double_cover (G : mgraph) : Prop :=
  exists (C : 'I_5 -> {set edge G}) (d : 'I_5 -> edge G -> bool),
    [/\ (forall i : 'I_5, even_subgraph (C i)),
        (forall i : 'I_5, x212_balanced (C i) (d i)),
        (forall e : edge G, #|[set i : 'I_5 | e \in C i]| = 2)
      & (forall (e : edge G) (i j : 'I_5),
           i != j -> e \in C i -> e \in C j -> d i e != d j e)].

(** *** Paths of a prescribed length (bm-062)

    A path of length [k] from [x] to [y]: a list [p] of [k] vertices such that
    [x :: p] is duplicate-free, consecutively adjacent, and ends at [y]. *)
Definition x212_path_len (G : sgraph) (k : nat) (x y : G) (p : seq G) : bool :=
  [&& path (--) x p, size p == k, uniq (x :: p) & last x p == y].

(** *** Cycles, longest cycles, cycles inside a vertex set (bm-064/065/066)

    A cycle is a [ucycle] of length more than two -- the genuine cycles of a
    simple graph, cf. the [n >= 3] convention of [GTBase.common]. *)
Definition x212_cycle (G : sgraph) (c : seq G) : bool :=
  ucycleb (--) c && (2 < size c).

Definition x212_cycle_vertices (G : sgraph) (c : seq G) : {set G} := [set v | v \in c].

Definition x212_longest_cycle (G : sgraph) (c : seq G) : Prop :=
  x212_cycle c /\ forall c' : seq G, x212_cycle c' -> size c' <= size c.

(** Some cycle of [G] has all its vertices in [S]. *)
Definition x212_cycle_within (G : sgraph) (S : {set G}) : Prop :=
  exists c : seq G, x212_cycle c /\ {subset c <= S}.

(** The edge cut of a vertex set: the edges with exactly one end in [S]. *)
Definition x212_edge_cut (G : sgraph) (S : {set G}) : {set {set G}} :=
  [set e in E(G) | #|e :&: S| == 1].

(** Cyclic edge connectivity: no set of fewer than [k] edges separates [G] into
    two sides that both contain a cycle. *)
Definition x212_cyclically_edge_connected (G : sgraph) (k : nat) : Prop :=
  forall S : {set G},
    x212_cycle_within S -> x212_cycle_within (~: S) -> k <= #|x212_edge_cut S|.

(** ** X212 statements *****************************************************)

(** Corpus row: bm:bm-011
    Site: https://graph-theory-ai.github.io/graph-conjectures/bm/bm-011/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/bondy_murty_reviews/bm-011.json
    English statement: (Barat and Thomassen 2006, Bondy-Murty Appendix A #11; proved by
      Bensmail, Harutyunyan, Le, Merker and Thomasse 2017)
      For every nonempty finite simple graph T that is a tree, that is, connected and
      without cycles, there is a natural number k with the following property: whenever a
      finite simple graph G is k-edge-connected and the number of edges of T divides the
      number of edges of G, the edges of G can be listed as a finite family of edge sets,
      each of which is the edge set of a copy of T inside G, that is, the image of an
      injective adjacency-preserving map from the vertices of T to the vertices of G, in
      such a way that every edge of G belongs to exactly one member of the family.
    Definitions: [x212_copy_edges f] - the set of the 2-element vertex sets [set f x; f y]
      for the adjacent pairs x, y of T (X212.v); [x212_copy_of T A] - A is the edge set of
      such a copy, for some injective adjacency-preserving f (X212.v);
      [x212_decomposition_into_copies T D] - every member of the list D is a copy of T and
      every 2-element vertex set is counted over D exactly once if it is an edge of G and
      zero times otherwise (X212.v); [k_edge_connected G k] - G has at least two vertices
      and stays connected after deleting any fewer than k edges (GTBase.common);
      [is_tree S] and [E(G)] - the library tree predicate and edge set (coq-graph-theory
      sgraph.v, re-exported by GTBase.base).
    Notes: "decomposition into copies of T" is a list of edge sets, so two copies occupying
      the same edges are counted separately; the covering condition is the exact-count form
      [count ... D = (e \in E(G))], which is simultaneously the "covers every edge" and the
      "edge-disjoint" requirement. A copy is a not necessarily induced subgraph isomorphic
      to T: only [x -- y -> f x -- f y] is required. The divisibility hypothesis is written
      with the natural-number divisibility [%|] on [#|E(T)|] and [#|E(G)|]. The existential
      k is the conjecture's k(T); the guard [0 < #|T|] excludes the empty "tree". *)
Definition barat_thomassen_tree_decomposition_statement : Prop :=
  forall T : sgraph,
    0 < #|T| -> is_tree [set: T] ->
    exists k : nat,
      forall G : sgraph,
        k_edge_connected G k ->
        #|E(T)| %| #|E(G)| ->
        exists D : seq {set {set G}}, x212_decomposition_into_copies T D.

(** Corpus row: bm:bm-013
    Site: https://graph-theory-ai.github.io/graph-conjectures/bm/bm-013/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/bondy_murty_reviews/bm-013.json
    English statement: (Bondy 1990, Bondy-Murty Appendix A #13, small cycle double cover
      conjecture)
      Every simple multigraph G with at least one vertex, that is, loopless and with at most
      one edge between any two vertices, in which no edge is a bridge, has a cycle double
      cover with at most one fewer members than G has vertices: a list of circuits, each a
      nonempty connected edge set in which every vertex lies on no edge or on exactly two
      edges, such that every edge of G lies in exactly two members of the list, the list
      having at most #|G| - 1 members.
    Definitions: [simple_mgraph G] - loopless and at most one edge between any two vertices,
      counted UNDIRECTEDLY ([#|edges x y| + #|edges y x| <= 1], since [mgraph.edges] counts
      arcs in one direction only) (U6.v); [cdc L] - every member of L is a circuit and every
      edge is counted exactly twice over L (U6.v); [is_circuit C] - a nonempty connected
      2-regular edge set, [bridgeless G] - no edge is a bridge (cut edge), that is, no edge
      that every UNDIRECTED walk between its endpoints must use, [subdeg],
      [subgraph_connected], [subgraph_kregular]
      (cycle-theory/theories/foundations/connectivity.v).
    Notes: the bound n - 1 uses truncated natural subtraction; the guard [0 < #|G|] makes it
      harmless. The source says "simple graph"; the carrier is nevertheless [mgraph] with an
      explicit [simple_mgraph] hypothesis, so that the row shares the [cdc] vocabulary of the
      already committed [cycle_double_cover_statement] (U6.v, row 11) that it strengthens
      (corpus relation e209). Edgeless graphs are included, with the empty cover.
      REPAIRED (foundation repair, 2026-09-23): the two defects found by the
      second-reader readback are fixed in the foundation, and the row's body is
      unchanged. (i) [simple_mgraph] now bounds the UNDIRECTED multiplicity
      [#|edges x y| + #|edges y x|], so a doubled edge carried by two
      ANTIPARALLEL arcs is rejected ([grounding_X212.x212_not_simple_Gd]); the
      complete symmetric digraph on three vertices that refuted the row is no
      longer [simple_mgraph], and its refutation hint
      (meta/probe_hints/small_cycle_double_cover_statement.v) no longer compiles
      (the probe reports hint-stale-FIX-OK). (ii) [is_bridge] now quantifies
      over the UNDIRECTED [uwalk], so [bridgeless] is "no cut edge"
      ([grounding_X212.x212_bridgeless_Tri] /
      [grounding_X212.x212_not_bridgeless_G1]). The cyclically oriented triangle
      is a simple, bridgeless three-vertex witness of the hypothesis class
      ([grounding_X212.x212_small_cdc_hypotheses_Tri]).
      UNBLOCKED (second-reader re-read, 2026-09-23): both defects confirmed
      fixed by independent back-translation, the hint confirmed stale, and the
      row is also immune to the LOOP defect that used to block [bm-026] - now
      repaired as well: [subdeg] counts ARC ENDS, so a loop contributes 2 and a
      single loop is an [even_subgraph] and an [is_circuit]. The repair leaves
      THIS row's meaning untouched, because [simple_mgraph] forces [loopless]
      and on a loopless carrier the arc-end count and the incidence count agree
      ([connectivity.subdeg_loopless]). PASS. See
      meta/X211-X229_faithfulness_audit.md and
      meta/STATEMENT_IMPROVEMENTS.md. *)
Definition small_cycle_double_cover_statement : Prop :=
  forall G : mgraph,
    (0 < #|G|)%N -> simple_mgraph G -> bridgeless G ->
    exists L : seq {set edge G}, cdc L /\ (size L <= #|G| - 1)%N.

(** Corpus row: bm:bm-016
    Site: https://graph-theory-ai.github.io/graph-conjectures/bm/bm-016/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/bondy_murty_reviews/bm-016.json
    English statement: (Akiyama, Exoo and Harary 1981, Bondy-Murty Appendix A #16, linear
      arboricity conjecture)
      Let k be a natural number and let G be a finite simple graph with at least one vertex
      in which every vertex has exactly k neighbours. Then the least number of colours in a
      colouring of the 2-element vertex sets of G all of whose colour classes are linear
      forests, that is, spanning subgraphs of G without cycles in which every vertex has at
      most two neighbours, equals the ceiling of (k + 1) divided by 2.
    Definitions: [x212_edge_colour_rel col i] and [x212_colour_graph col i] - the spanning
      subgraph of G whose edges are those receiving colour i (X212.v);
      [x212_linear_forest_colour col i] - that subgraph is a forest of maximum degree at
      most two (X212.v); [x212_linear_arboricity_at_most G q] - some colouring with q
      colours has all its classes linear forests (X212.v); [x212_linear_arboricity G q] - q
      is such a number and no smaller number is (X212.v); [regular G k] - every vertex has
      exactly k neighbours, [Delta] - maximum degree, [ceil_div a b] - the ceiling of a/b
      (GTBase.base); [is_forest] (coq-graph-theory sgraph.v).
    Notes: the colouring is a total map on 2-element vertex sets, [{set G} -> 'I_q]; only
      its values on genuine edges matter, a non-edge contributing nothing to
      [x212_edge_colour_rel]. "Linear forest" is rendered as acyclic plus maximum degree at
      most 2, exactly a disjoint union of paths. The conjectured value is an EQUALITY,
      encoded as achievability plus minimality; the easy half is the lower bound. Because
      ['I_0] is empty while [{set G}] never is, [x212_linear_arboricity_at_most G 0] is
      always false, so the encoded minimum is at least 1 and the degenerate k = 0 case
      (an edgeless graph, value [ceil_div 1 2] = 1) is consistent. The guard [0 < #|G|] is
      needed: on the empty graph the encoded value is 1 for every k. The equivalent
      "union of linear forests" phrasing of the source gives the same minimum, a subset of
      a linear forest being a linear forest.
      Readback 2026-09-23: the encoded minimum differs from the CLASSICAL linear
      arboricity on exactly one family, the edgeless graphs, where the classical
      value is 0 and the encoded one is 1; every graph with an edge has classical
      value at least 1 and the two agree. That single divergence is what makes the
      degenerate k = 0 instance come out TRUE, whereas the source's formula
      ceil((0+1)/2) = 1 is literally false for the edgeless graph. The encoding
      therefore repairs a degenerate falsehood of the source sentence instead of
      guarding 1 <= k; benign, but recorded as a modelling divergence. *)
Definition linear_arboricity_regular_statement : Prop :=
  forall (k : nat) (G : sgraph),
    0 < #|G| -> regular G k -> x212_linear_arboricity G (ceil_div (k + 1) 2).

(** Corpus row: bm:bm-026
    Site: https://graph-theory-ai.github.io/graph-conjectures/bm/bm-026/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/bondy_murty_reviews/bm-026.json
    English statement: (Archdeacon 1984 and Jaeger 1985, Bondy-Murty Appendix A #26,
      orientable five cycle double cover conjecture)
      Every multigraph G with at least one vertex that is connected and has no bridge
      carries five edge sets, indexed by the integers modulo 5, such that each of them is an
      even subgraph, every vertex lying on an even number of its edges, each of them can be
      given a direction on each of its edges under which every vertex has as many outgoing
      as incoming edges of that set, every edge of G lies in exactly two of the five sets,
      and the two sets containing a given edge give it opposite directions.
    Definitions: [x212_tail d e] and [x212_head d e] - the two ends of e under the
      orientation d, which keeps the intrinsic source-to-target direction when d e is true
      and reverses it otherwise (X212.v); [x212_balanced C d] - inside C every vertex is the
      tail of as many edges as it is the head of (X212.v);
      [x212_orientable_5_even_double_cover G] - five even subgraphs with balanced
      orientations covering each edge exactly twice, in opposite directions (X212.v);
      [even_subgraph C] - every vertex has even C-degree (U6.v); [two_edge_connected G] -
      connected and bridgeless, that is, no edge is a cut edge, [mconnected], [bridgeless],
      [subdeg H v] - that degree, the number of ARC ENDS of H at v, so that a LOOP
      contributes 2 and a single loop is an even subgraph
      (cycle-theory/theories/foundations/connectivity.v).
    Notes: "orientable" is the combinatorial condition recorded in the corpus context - each
      even subgraph can be oriented so that every edge of the graph is traversed once in
      each direction - and needs no surface or embedding layer. The cover is indexed by
      ['I_5] rather than given as a list, so "five" is exact and the "two members" condition
      is the cardinality of the index set [[set i | e \in C i]]; repetitions of the same
      edge set at different indices are allowed, as in a list. 2-edge-connected is read as
      connected and bridgeless, the reading of [two_edge_connected] used throughout
      cycle-theory.
      REPAIRED (foundation repair, 2026-09-23): [is_bridge] is now stated with
      the UNDIRECTED [uwalk] of GTBase.base ([ueseparates] in
      cycle-theory/theories/foundations/connectivity.v), so [bridgeless] is the
      textbook "no cut edge" and [two_edge_connected] is connected + bridgeless
      in that sense. The earlier reading went through coq-graph-theory's
      [eseparates] over the DIRECTED [walk] and demanded an alternative DIRECTED
      route u -> ... -> v for every arc u -> v, which forced out-degree and
      in-degree at least 2 at the ends of every non-loop edge, excluded every
      orientation of a cycle and left only disjoint unions of triple-edge
      dipoles among cubic carriers. That is fixed: the cyclically oriented
      triangle is now bridgeless and 2-edge-connected
      ([grounding_X212.x212_bridgeless_Tri],
      [grounding_X212.x212_two_edge_connected_Tri]), while an edge whose
      deletion separates its endpoints is a bridge
      ([grounding_X212.x212_not_bridgeless_G1]). The same repair applies to
      [cycle_double_cover_statement] (U6.v), [five_flow_statement] (D1.v) and
      [half_flow_pair_statement] (X228.v).
      LOOP-DEGREE REPAIR (2026-09-23, main session). The SECOND, independent
      defect found by the second-reader re-read is now fixed in the foundation
      too, and the row's body is unchanged. [connectivity.subdeg] used to count
      the edges INCIDENT to a vertex, so a LOOP contributed 1, not 2; under that
      reading [U6.even_subgraph [set e]] failed on a loop, and the one-vertex
      one-loop multigraph - connected and bridgeless, since a loop is never a
      cut edge ([connectivity.loop_not_bridge]), hence [two_edge_connected] -
      made this row axiom-free REFUTABLE, although the conjecture plainly holds
      there (cover the loop twice). [subdeg H v] is now the number of ARC ENDS
      of H at v ([#|ends_at H false v| + #|ends_at H true v|]), so a loop
      contributes 2, the textbook convention; [connectivity.subdegE] states the
      identity "degree = incidences + loops" and
      [connectivity.subdeg_loopless] shows that the two readings agree on a
      loopless carrier, so no row guarded by [loopless], [cubic] or
      [simple_mgraph] changes meaning. The loop graph is now a genuine INSTANCE
      of this row, with the conclusion EXHIBITED: [grounding_X212.Lp] (the same
      construction as [grounding_U6.Gloop]) has [mdeg = 2]
      ([grounding_X212.x212_mdeg_Lp]), its single edge is an even subgraph and a
      circuit ([grounding_X212.x212_even_subgraph_Lp],
      [grounding_X212.x212_is_circuit_Lp]), it satisfies the hypotheses
      ([grounding_X212.x212_orientable_5_hypotheses_Lp]) and it carries a
      five-member orientable even double cover - the loop in members [ord0] and
      [ord_max], oppositely oriented, the other three empty -
      ([grounding_X212.x212_orientable_5_Lp], packaged with the hypotheses as
      [grounding_X212.x212_orientable_5_loop_instance]). The refutation is
      therefore gone: meta/probe_hints/orientable_five_cycle_double_cover_statement.v
      no longer compiles (meta/vacuity_probe.py reports hint-stale-FIX-OK), and
      neither does its sibling for [cycle_double_cover_statement] (U6.v), which
      the same graph refuted through [is_circuit] instead of [even_subgraph].
      Rows guarded by [loopless] were never affected:
      [small_cycle_double_cover_statement] via [simple_mgraph], the [U10] rows
      via [cubic]. See meta/X211-X229_faithfulness_audit.md and
      meta/STATEMENT_IMPROVEMENTS.md. *)
Definition orientable_five_cycle_double_cover_statement : Prop :=
  forall G : mgraph,
    (0 < #|G|)%N -> two_edge_connected G -> x212_orientable_5_even_double_cover G.

(** Corpus row: bm:bm-062
    Site: https://graph-theory-ai.github.io/graph-conjectures/bm/bm-062/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/bondy_murty_reviews/bm-062.json
    English statement: (Kotzig 1974, Bondy-Murty Appendix A #62, unique k-path conjecture)
      For every natural number k at least 3, no finite simple graph with at least two
      vertices has the property that any two distinct vertices x and y are joined by exactly
      one path with k edges, a path being a duplicate-free list of vertices in which
      consecutive entries are adjacent.
    Definitions: [x212_path_len k x y p] - p is a list of k vertices such that x :: p is
      duplicate-free, consecutive entries are adjacent and the last entry is y, that is, a
      path from x to y with k edges (X212.v); [path] and [uniq] (MathComp path.v / seq.v).
    Notes: the conjecture is a NON-existence statement, so the Rocq body is the negation of
      the unique-path property, universally quantified over k at least 3 and over the graph.
      "Every pair of vertices" is read as every pair of DISTINCT vertices, the reading under
      which the case k = 2 is the Friendship Theorem, whose windmill graphs do satisfy the
      property. The guard [1 < #|G|] is load-bearing: on a graph with fewer than two
      vertices the property holds vacuously, so without it the statement would be false for
      trivial reasons. Uniqueness is MathComp's [exists!] on vertex lists. *)
Definition kotzig_unique_k_path_statement : Prop :=
  forall (k : nat) (G : sgraph),
    3 <= k -> 1 < #|G| ->
    ~ (forall x y : G, x != y -> exists! p : seq G, x212_path_len k x y p).

(** Corpus row: bm:bm-064
    Site: https://graph-theory-ai.github.io/graph-conjectures/bm/bm-064/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/bondy_murty_reviews/bm-064.json
    English statement: (S. Smith, see Grotschel 1984, Bondy-Murty Appendix A #64)
      For every natural number k at least 2 and every finite simple graph G that is
      k-connected, that is, has more than k vertices and stays connected after deleting any
      fewer than k vertices, any two longest cycles of G share at least k vertices; a cycle
      is a closed duplicate-free walk on more than two vertices, and a longest cycle is one
      no shorter than every cycle of G.
    Definitions: [x212_cycle c] - c is a [ucycle] on more than two vertices (X212.v);
      [x212_longest_cycle c] - c is a cycle and no cycle is longer (X212.v);
      [x212_cycle_vertices c] - the set of vertices occurring in c (X212.v);
      [k_connected G k] - more than k vertices and deleting fewer than k leaves the graph
      connected (GTBase.base); [ucycleb] (MathComp path.v).
    Notes: "longest" is taken relative to cycles on more than two vertices, the genuine
      cycles of a simple graph (a two-element [ucycle] is just an edge traversed back and
      forth). If G has no cycle the hypotheses are unsatisfiable and the row holds vacuously
      for it. The same conjecture is also carried, from the studies corpus, as
      [smith_longest_cycles_r_connected_statement] (X10.v); the two bodies are proved
      equivalent in [implications_X212.v]. *)
Definition smith_two_longest_cycles_statement : Prop :=
  forall (k : nat) (G : sgraph) (c d : seq G),
    2 <= k -> k_connected G k ->
    x212_longest_cycle c -> x212_longest_cycle d ->
    k <= #|x212_cycle_vertices c :&: x212_cycle_vertices d|.

(** Corpus row: bm:bm-065
    Site: https://graph-theory-ai.github.io/graph-conjectures/bm/bm-065/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/bondy_murty_reviews/bm-065.json
    English statement: (J. A. Bondy, see Fleischner and Jackson 1989, Bondy-Murty Appendix A
      #65)
      There are positive natural numbers p and q such that every finite simple graph G with
      at least one vertex in which every vertex has exactly three neighbours, which is
      3-connected and cyclically 4-edge-connected, that is, no set of fewer than four edges
      separates G into two sides that both contain a cycle, has a cycle c with
      p times the number of vertices of G at most q times the length of c.
    Definitions: [x212_cycle c] - c is a [ucycle] on more than two vertices (X212.v);
      [x212_cycle_within S] - some cycle of G has all its vertices in S (X212.v);
      [x212_edge_cut S] - the edges with exactly one end in S (X212.v);
      [x212_cyclically_edge_connected G k] - every vertex set whose two sides both contain a
      cycle has an edge cut of at least k edges (X212.v); [regular G 3] - every vertex has
      exactly three neighbours, [k_connected G 3], [E(G)] (GTBase.base / coq-graph-theory).
    Notes: the positive real constant c of the source is encoded as the positive rational
      p/q by the two positive naturals p and q, the conclusion "length at least c n" being
      the cross-multiplied inequality [p * #|G| <= q * size c]; this is equivalent to the
      real form since both sides are naturals and every positive real constant can be
      lowered to a positive rational one. "Cubic" is [regular G 3] on a simple graph, which
      is loopless and without parallel edges by construction. The length of the cycle c is
      [size c], its number of vertices, which for a cycle is also its number of edges. *)
Definition bondy_linear_cycle_cubic_statement : Prop :=
  exists p q : nat,
    [/\ 0 < p, 0 < q &
        forall G : sgraph,
          0 < #|G| -> regular G 3 -> k_connected G 3 ->
          x212_cyclically_edge_connected G 4 ->
          exists c : seq G, x212_cycle c /\ p * #|G| <= q * size c].

(** Corpus row: bm:bm-066
    Site: https://graph-theory-ai.github.io/graph-conjectures/bm/bm-066/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/bondy_murty_reviews/bm-066.json
    English statement: (Birmele, Bondy and Reed 2007, Bondy-Murty Appendix A #66)
      For every natural number k at least 3 and every finite simple graph G, if any two
      cycles of G on at least k vertices share a vertex, then some set of at most k vertices
      of G meets every cycle of G on at least k vertices; a cycle is a closed duplicate-free
      walk on more than two vertices.
    Definitions: [x212_cycle c] - c is a [ucycle] on more than two vertices (X212.v);
      [ucycleb] (MathComp path.v).
    Notes: "cycles of length at least k" is [k <= size c], the number of vertices of the
      cycle, which for a cycle equals its number of edges. "A set of k vertices meeting
      every long cycle" is read as a set of AT MOST k vertices, the standard transversal
      form (a set of exactly k vertices need not exist when G has fewer than k vertices).
      The guard [3 <= k] is load-bearing: for k at most 2 the hypothesis only says that any
      two cycles meet, which holds in the complete graph on five vertices, while no single
      vertex (k = 1) or pair (k = 2) meets all of its cycles, so the unguarded statement is
      false; the conjecture of Birmele, Bondy and Reed is posed for k at least 3. The
      hypothesis is stated for all pairs of long cycles, including a cycle with itself,
      which is harmless. Readback 2026-09-23: the guard and the "at most k"
      reading both agree with the literature form recorded in the row's review
      ("every graph without two vertex-disjoint cycles of length at least l has
      a set of AT MOST l vertices meeting all cycles of length at least l"); the
      guard is an added hypothesis, so the encoded statement is formally weaker
      than the unguarded corpus sentence - which is false, hence not the
      intended reading. *)
Definition birmele_long_cycle_transversal_statement : Prop :=
  forall (k : nat) (G : sgraph),
    3 <= k ->
    (forall c d : seq G,
       x212_cycle c -> k <= size c -> x212_cycle d -> k <= size d ->
       exists x : G, (x \in c) && (x \in d)) ->
    exists S : {set G},
      #|S| <= k /\
      forall c : seq G, x212_cycle c -> k <= size c -> exists x : G, (x \in S) && (x \in c).
