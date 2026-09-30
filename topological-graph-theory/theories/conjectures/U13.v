(** * Topological.conjectures.U13 — milestone U13 (namespace Topological, plan v4)

    Statement-only formalizations (axiom-free: no Conjecture/Axiom/Parameter/
    Admitted) of four planar / topological-graph-theory problems.

    PLANARITY G2-GATE.  [coq-graph-theory-planar] / [coq-fourcolor] are NOT
    installed on this switch, so there is no [planar : sgraph -> Prop] in scope.
    Every row of THIS milestone is intrinsically about planar graphs
    (manifest [requires_planarity = true] for all four slugs).  Per plan §3 the
    planarity predicate is therefore discharged INTO each statement as a
    universally-quantified ORACLE [is_planar : sgraph -> Prop] — never a
    top-level Parameter/Axiom (which would contaminate Print Assumptions).  The
    file type-checks and is axiom-free, but the rows are honestly marked
    [compile_blocked]: their MATHEMATICAL content is faithful only when
    [is_planar] is instantiated with the real planarity predicate from the
    planar/fourcolor stack (plan gate G2).  Once G2 lands, replace the leading
    [forall (is_planar : sgraph -> Prop)] by the concrete predicate.

    CORE API reused (switch `digraph`, Rocq 9.1.1 + coq-graph-theory + base):
      - [G : sgraph]; [x -- y] adjacency; [N(x)] open neighbourhood;
      - [is_forest S] : Prop  (coq-graph-theory sgraph) — the induced subgraph
        on [S : {set G}] is a forest (acyclic);  this IS the "induced forest"
        primitive, so no new primitive is introduced for row 1;
      - [χ(A)] : nat — subset-relative chromatic number, whole-graph [χ([set:G])];
      - [Delta G] : nat (base) — sgraph maximum degree Δ ("max-degree");
      - [graph_power G 2] : sgraph (base) — the square G² ("graph-square"):
        distinct vertices at distance ≤ 2 are adjacent.
    Thus "graph-square" = [graph_power _ 2] and "max-degree" = [Delta] are
    REUSED from base verbatim.  Two genuinely-new primitives are introduced:
      - [union_of_two_planar] (row 2) is AREA-SPECIFIC (intrinsically planar /
        thickness-2), so it stays local;
      - [k_degenerate_on] / [k_degenerate] (row 4) are a generic structural /
        sparsity notion that is plausibly CROSS-AREA, so they are tagged
        [@MOVE-to-base] and should migrate to base once a second area needs
        degeneracy. *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Corpus row: opg:large_induced_forest_in_a_planar_graph
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/large_induced_forest_in_a_planar_graph/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/large_induced_forest_in_a_planar_graph.json
    English statement: (Open Problem Garden, "Large induced forest in a planar graph";
      Albertson-Berman)
      Every planar graph on n vertices has an induced forest on at least n/2 vertices.  In
      the Rocq body: for every finite simple graph G with no K5 and no K3,3 minor there is a
      vertex set S such that the subgraph induced on S is acyclic and the number of vertices
      of G is at most twice the size of S.
    Definitions: standard - [wagner_planar] (no K5 and no K3,3 minor, i.e. planarity by
      Wagner's theorem, base/theories/base.v) and [is_forest S] (coq-graph-theory sgraph.v:
      the subgraph induced on S is acyclic).
    Notes: The bound |S| >= n/2 is cross-multiplied as [#|G| <= 2 * #|S|] to avoid nat
      division, which is equivalent over the naturals and slightly stronger than the floor
      reading when n is odd (it demands |S| >= n/2 exactly, i.e. ceil(n/2)).  The corpus row
      is PARTIAL: partial lower bounds on the induced-forest size are proven, the conjectured
      fraction 1/2 is open.  The milestone header of this file describes an earlier encoding
      in which planarity was a universally-quantified oracle [is_planar] (planarity gate G2);
      the definition now uses the concrete [wagner_planar], so that caveat no longer applies
      here - but it still applies to the copy of this statement in implications_U13.v. *)
Definition large_induced_forest_in_a_planar_graph_statement : Prop :=
  forall (G : sgraph),
    wagner_planar G ->
    exists S : {set G}, is_forest S /\ (#|G| <= 2 * #|S|)%N.

(** ** Row 2 — Earth–Moon problem (thickness-2 chromatic number)
    OPEN (the maximum is known to lie between 9 and 12).
    G2-GATE (planarity).

    Source (Problem): "What is the maximum number of colours needed to colour
    countries such that no two countries sharing a common border have the same
    colour in the case where each country consists of one region on earth and
    one region on the moon?"

    The map-colouring formulation is, via duality, the chromatic number of a
    graph that is the edge-UNION of two planar graphs on a common vertex set
    (a thickness-≤ 2 graph).  The open Problem "what is the maximum?" is stated
    as: there is a value [m] that is simultaneously an UPPER BOUND on χ over all
    such graphs and ACHIEVED by one of them — i.e. the maximum exists and equals
    [m].

    NON-VACUITY GUARD (faithfulness): the ACHIEVED clause is an existential over
    biplanar graphs, so under the degenerate oracle [is_planar := fun _ => False]
    (where [union_of_two_planar] is unsatisfiable) it would make the whole Prop
    FALSE for reasons unrelated to the mathematics — i.e. refutable, not merely
    over-strong.  We therefore guard the statement on the existence of at least
    one biplanar graph: [(exists G0, union_of_two_planar is_planar G0) -> …].
    Once G2 instantiates [is_planar] with the real planarity predicate the guard
    is automatically discharged (planar graphs exist), so the guard adds nothing
    mathematically yet keeps the pre-G2 statement self-contained (non-refutable).

    New AREA primitive: [union_of_two_planar] (edge-union of two [is_planar]
    graphs on the vertex set of [G]).  Each planar layer is reconstructed as an
    [sgraph] over the SAME vertex type [G] from a symmetric irreflexive edge
    relation, so [is_planar] applies to it and χ([set:G]) is the union's
    chromatic number. *)
Definition union_of_two_planar
    (is_planar : sgraph -> Prop) (G : sgraph) : Prop :=
  exists (e1 e2 : rel G)
         (s1 : symmetric e1) (i1 : irreflexive e1)
         (s2 : symmetric e2) (i2 : irreflexive e2),
    [/\ is_planar (SGraph s1 i1),
        is_planar (SGraph s2 i2)
      & forall x y : G, (x -- y) = e1 x y || e2 x y ].

(** Corpus row: opg:earth_moon_problem
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/earth_moon_problem/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/earth_moon_problem.json
    English statement: (Open Problem Garden, "Earth-Moon Problem"; Ringel)
      Corpus question: what is the maximum number of colours needed to colour countries so
      that no two countries sharing a border get the same colour, when each country consists
      of one region on earth and one region on the moon?  By duality this is the maximum
      chromatic number of a graph that is the edge-union of two planar graphs on a common
      vertex set (a graph of thickness at most 2).  Back-translation of the Rocq body:
      assuming at least one such biplanar graph exists, there is a number m that is
      simultaneously an upper bound on the chromatic number of every biplanar graph and is
      attained by some biplanar graph - i.e. the maximum exists and equals m.
    Definitions: [union_of_two_planar is_planar G] - the adjacency of G is the disjunction of
      two symmetric irreflexive relations each of which, read as an [sgraph] on the same
      vertex type, is planar (defined just above in this file, instantiated here with
      [wagner_planar]); [wagner_planar] - no K5 and no K3,3 minor (base/theories/base.v); the
      chromatic number is coq-graph-theory's [chi(A)] on the full vertex set.
    Notes: The open "what is the maximum?" problem is rendered as the EXISTENCE of the
      maximum together with its two defining properties, not as a numeric answer (the value
      is known only to lie between 9 and 12).  NON-VACUITY GUARD: the "attained" clause is an
      existential over biplanar graphs, so the statement is prefixed by the hypothesis that
      at least one biplanar graph exists; with the concrete [wagner_planar] that guard is
      automatically satisfied and adds nothing mathematically, but it keeps the statement
      non-refutable for the degenerate planarity predicates the earlier oracle-based encoding
      allowed.  [union_of_two_planar] is area-specific (intrinsically thickness-2) and stays
      local. *)
Definition earth_moon_statement : Prop :=
    (exists G0 : sgraph, union_of_two_planar wagner_planar G0) ->
    exists m : nat,
      (forall G : sgraph, union_of_two_planar wagner_planar G -> (χ([set: G]) <= m)%N)
   /\ (exists G : sgraph, union_of_two_planar wagner_planar G /\ χ([set: G]) = m).

(** Corpus row: opg:colouring_the_square_of_a_planar_graph
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/colouring_the_square_of_a_planar_graph/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/colouring_the_square_of_a_planar_graph.json
    English statement: (Open Problem Garden, "Colouring the square of a planar graph";
      Wegner's conjecture)
      For every planar graph G with at least one vertex and maximum degree D, the chromatic
      number of the square of G is at most 7 when D = 3, at most D + 5 when 4 <= D <= 7, and
      at most floor(3D/2) + 1 when D >= 8.  The Rocq body is exactly this three-regime
      guarded conjunction, with planarity read as "no K5 and no K3,3 minor".
    Definitions: standard - [wagner_planar] (base/theories/base.v), [Delta G] (maximum
      degree, base/theories/base.v), [graph_power G 2] (the square: distinct vertices at
      distance at most 2 are adjacent, base/theories/base.v), and coq-graph-theory's [chi(A)]
      on the full vertex set.
    Notes: floor(3D/2) is the nat halving [(3 * Delta G)./2].  The [0 < #|G|] guard keeps
      [Delta] meaningful on the empty graph.  The three regimes are conjoined rather than
      given as a case split, which is equivalent since the guards are mutually exclusive and,
      together with D <= 2, exhaust the possibilities - note that D <= 2 is left
      unconstrained here, as in the source. *)
Definition colouring_the_square_of_a_planar_graph_statement : Prop :=
  forall (G : sgraph),
    wagner_planar G -> (0 < #|G|)%N ->
    [/\ ( Delta G = 3 -> (χ([set: graph_power G 2]) <= 7)%N ),
        ( (4 <= Delta G)%N -> (Delta G <= 7)%N ->
            (χ([set: graph_power G 2]) <= Delta G + 5)%N )
      & ( (8 <= Delta G)%N ->
            (χ([set: graph_power G 2]) <= (3 * Delta G)./2 + 1)%N ) ].

(** Corpus row: opg:degenerate_colorings_of_planar_graphs
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/degenerate_colorings_of_planar_graphs/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/degenerate_colorings_of_planar_graphs.json
    English statement: (Open Problem Garden, "Degenerate colorings of planar graphs")
      Every simple planar graph has a 5-colouring such that, for every k between 1 and 4, the
      union of any k colour classes induces a (k-1)-degenerate graph (a graph is
      j-degenerate when every subgraph of it has a vertex of degree at most j).  In the Rocq
      body: for every finite simple graph G with no K5 and no K3,3 minor there is a map col
      from vertices to a 5-element set that is proper (adjacent vertices get different
      colours) and such that for every palette T of between 1 and 4 of the five colours, the
      vertex set {v : col v in T} is (|T| - 1)-degenerate.
    Definitions: [k_degenerate_on W k] - every non-empty subset S of W contains a vertex with
      at most k neighbours inside S (base/theories/base.v; it was promoted there from this
      milestone, which is why the definition is no longer local); [wagner_planar] -
      base/theories/base.v.
    Notes: Degeneracy of "the graph induced by the union of k colour classes" is expressed by
      quantifying over induced subgraphs of that vertex set, which is equivalent to the
      subgraph formulation used by the source (a vertex of minimum degree in a subgraph can
      be found in the induced subgraph on the same vertex set).  The palette is a set T of
      colours with 1 <= |T| <= 4 and the degeneracy parameter is |T| - 1, matching the
      source's k and k-1.  The companion whole-graph form [k_degenerate] also lives in
      base/theories/base.v and is not used by this statement. *)
Definition degenerate_colorings_of_planar_graphs_statement : Prop :=
  forall (G : sgraph),
    wagner_planar G ->
    exists col : G -> 'I_5,
      (forall x y : G, x -- y -> col x != col y)
   /\ (forall T : {set 'I_5},
         (1 <= #|T|)%N -> (#|T| <= 4)%N ->
         k_degenerate_on [set v : G | col v \in T] (#|T| - 1)).
