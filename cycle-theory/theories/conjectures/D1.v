(** * Cycle.conjectures.D1 — milestone D1 (namespace Cycle, plan v4)

    Statement-only formalizations (axiom-free: no Conjecture/Axiom/Parameter/
    Admitted) of fifteen open problems of FLOW theory: nowhere-zero flows,
    circular flow numbers, bidirected flows, group/B-flows, the flow polynomial,
    modular orientations, local tensions on embedded graphs, cycle-continuous
    maps and an edge-disjoint-paths approximation question.

    CARRIER per row (chosen from each row's rocq_idiom, NOT a blanket sgraph):
      - Most flow rows are undirected MULTIGRAPH statements, carrier
        coq-graph-theory's [mgraph] = [graph unit unit].  Edges carry an
        intrinsic reference orientation ([source]/[target]); a nowhere-zero
        r-flow is a real/integer edge weighting that may be negative (this
        absorbs the choice of orientation), with [1 <= |phi e| <= r-1] and
        Kirchhoff conservation [out-sum = in-sum] at every vertex.
      - Bouchet's row carries two endpoint SIGN functions on top of [mgraph]
        (a bidirected graph).
      - The cycle-continuous row carries [nat -> sgraph] (an infinite family of
        SIMPLE graphs) with the binary cycle space on its 2-element edge sets.
      - The local-tensions row carries [mgraph] + a rotation system
        [{perm (edge G * bool)}] (a combinatorial surface embedding).
      - The group/B-flow row carries two [finGroupType]s and Cayley graphs.
      - The real-roots row uses [{poly int}] and roots in any [rcfType].
      - The unit-vector row uses [ 'rV[R]_3 ] over any [rcfType] R (S^2).

    IMPORT ORDER: [mgraph] (and [sgraph], [treewidth]) are imported BEFORE
    [base] (base ships an undirected line_graph that the multigraph one would
    otherwise shadow); the mathcomp algebra/fingroup layer is imported AFTER
    [base] so its canonical [int]/[rat]/order instances win (importing it before
    [base] makes ring numerals lose their order instance).  The shared
    multigraph vocabulary ([mdeg], [cut], [bridgeless], [mconnected],
    [edge_connected], [is_circuit], ...) mirrors cycle-theory U6 but is INLINED
    here (kept self-contained rather than importing U6).

    AREA primitives introduced here (flow-theory specific): all the flow
    families ([iconservative]/[rconservative]/[int_bounded]/[has_nz_kflow]/
    [has_nz_kflow_del]/[has_nz_rflow]/[circular_flow_number_le]), [is_2t1_graph],
    [mreg], [mDelta]/[is_class1], the bidirected primitives ([is_sign]/[bnet]/
    [has_nz_biflow]), [petersen]/[mg_minor], [imbalance], [nullity]/[flow_poly]/
    [flow_poly_eval], the embedded-graph primitives ([faces]/[fbound]/
    [contractible]/[edge_width_geq]/[local_tension]), Cayley graphs + [Bflow],
    the cycle space ([sedge]/[in_cycle_space]/[cycle_continuous]) and the
    edge-disjoint-paths primitives ([routes]/[edp_feasible]/[frac_feasible]/
    [mtreewidth_le]).  [two_edge_connected] is tagged [@MOVE-to-base]. *)

From mathcomp Require Import all_boot.
From GraphTheory Require Import mgraph sgraph treewidth.
From GTBase Require Import base.
From Cycle.foundations Require Export connectivity.
From mathcomp Require Import all_algebra all_fingroup.

Import GRing.Theory Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope ring_scope.

(** ================================================================= *)
(** ** Reused multigraph vocabulary (from [Cycle.foundations.connectivity]) *)

(** [mdeg], [cut], [mconnected], [connected_del_edges], [edge_connected],
    [is_bridge], [bridgeless], [subdeg], [subgraph_kregular], [walk_in],
    [H_inc], [subgraph_connected], [is_circuit] and [two_edge_connected] now
    live in [Cycle.foundations.connectivity] (imported above).

    DEGREE CONVENTION (textbook).  [subdeg H v] counts the ARC ENDS of [H] at
    [v] and [mdeg v] is [subdeg [set: edge G] v], so a LOOP at [v] contributes
    2 -- the convention under which the degree sum is twice the number of edges
    and a single loop is a circuit.  On a LOOPLESS carrier it agrees with the
    incidence count [#|edges_at v|] ([connectivity.mdeg_loopless]).

    The two [mreg] / [mDelta] rows below are NOT affected alike (corrected
    2026-09-23 after the second-reader re-read; the earlier note claimed both
    "read exactly as before", which was true only of the first):
      - [circular_flow_numbers_of_r_graphs_statement] reads exactly as before:
        its [is_2t1_graph G t] guard FORCES looplessness under either degree
        convention ([grounding_D1.is_2t1_loopless], via
        [grounding_D1.mdeg_cut]), so its carrier class did not move;
      - [circular_flow_number_of_regular_class_1_graphs_statement] had NO such
        guard, and its carrier class strictly GREW when a loop started counting
        2: loopful 3-regular carriers that base's [line_graph] still colours
        (a loop is not adjacent to itself) became class-1 instances with no
        nowhere-zero flow.  The row now carries an explicit [loopless G]
        hypothesis, which is what the source means by a class-1 graph; see the
        [LOOPLESS GUARD] paragraph of its doc block. *)

(** ================================================================= *)
(** ** Shared flow infrastructure (mgraph, intrinsic [source]/[target]) *)

(** Kirchhoff conservation for an integer / rational edge weighting: the total
    weight on the edges leaving [v] equals the total weight on the edges
    entering [v] (a LOOP at [v] occurs in both sums and so cancels -- it still
    has its two arc ends at [v], exactly as [mdeg] counts them; negative weights
    reverse the reference orientation). *)
Definition iconservative (G : mgraph) (phi : edge G -> int) : Prop :=
  forall v : G, \sum_(e | source e == v) phi e = \sum_(e | target e == v) phi e.

Definition rconservative (G : mgraph) (phi : edge G -> rat) : Prop :=
  forall v : G, \sum_(e | source e == v) phi e = \sum_(e | target e == v) phi e.

(** Nowhere-zero [k]-bounds for an integer flow: [1 <= |phi e| <= k-1]. *)
Definition int_bounded (G : mgraph) (k : nat) (phi : edge G -> int) : Prop :=
  forall e : edge G, (1 <= `|phi e|)%R /\ (`|phi e| <= (k.-1)%:R)%R.

(** [G] has a nowhere-zero [k]-flow (integer formulation). *)
Definition has_nz_kflow (G : mgraph) (k : nat) : Prop :=
  exists phi : edge G -> int, iconservative phi /\ int_bounded k phi.

(** [G \ A] (delete the edge set [A]) has a nowhere-zero [k]-flow: a flow
    supported off [A], conservative on the whole vertex set. *)
Definition has_nz_kflow_del (G : mgraph) (A : {set edge G}) (k : nat) : Prop :=
  exists phi : edge G -> int,
    [/\ iconservative phi,
        (forall e : edge G, e \in A -> phi e = 0)
      & (forall e : edge G, e \notin A ->
           (1 <= `|phi e|)%R /\ (`|phi e| <= (k.-1)%:R)%R)].

(** Nowhere-zero real [r]-flow (rational values suffice and are faithful): a
    rational conservative weighting with [1 <= |phi e| <= r-1]. *)
Definition has_nz_rflow (G : mgraph) (r : rat) : Prop :=
  exists phi : edge G -> rat,
    rconservative phi /\
    (forall e : edge G, (1 <= `|phi e|)%R /\ (`|phi e| <= r - 1)%R).

(** Circular flow number bound [F_c(G) <= c]: since the set of feasible [r] is
    an up-set, [F_c(G) = inf {r | G has a nz r-flow} <= c] iff [G] has a
    nowhere-zero [r]-flow for every rational [r > c]. *)
Definition circular_flow_number_le (G : mgraph) (c : rat) : Prop :=
  forall r : rat, (c < r)%R -> has_nz_rflow G r.

(** ** [(2t+1)]-graphs and regularity

    [mdeg] is the multigraph degree of [Cycle.foundations.connectivity]: the
    number of ARC ENDS at the vertex, so a LOOP contributes 2. *)

(** [d]-regular multigraph.  [@MOVE-to-base] (see mdeg note above). *)
Definition mreg (G : mgraph) (d : nat) : Prop := forall v : G, mdeg v = d.

(** A [(2t+1)]-graph: [(2t+1)]-regular and every odd vertex set has an edge cut
    of size at least [2t+1]. *)
Definition is_2t1_graph (G : mgraph) (t : nat) : Prop :=
  mreg G (2 * t + 1)%N /\
  (forall X : {set G}, odd #|X| -> (2 * t + 1 <= #|cut X|)%N).

(** Maximum multigraph degree and the class-1 property (χ'(G) = Δ(G)).
    [@MOVE-to-base] (see mdeg note above). *)
Definition mDelta (G : mgraph) : nat := \max_(v : G) mdeg v.
Definition is_class1 (G : mgraph) : Prop := chromatic_index G = mDelta G.

(** [two_edge_connected] (= connected and bridgeless) now lives in
    [Cycle.foundations.connectivity] (imported above). *)

(** ================================================================= *)
(** ** Row 1 — Circular flow numbers of [(2t+1)]-graphs *)
(** Corpus row: opg:circular_flow_numbers_of_r_graphs
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/circular_flow_numbers_of_r_graphs/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/circular_flow_numbers_of_r_graphs.json
    English statement: (Open Problem Garden, "Circular flow numbers of r-graphs")
      For every integer t > 1 and every multigraph G with at least one vertex that is a
      (2t+1)-graph, that is, every vertex has degree exactly 2t+1, a loop counting twice,
      and every vertex set of odd size has an edge cut of at least 2t+1 edges, the circular
      flow number of G is at most 2 + 2/t: for every rational r > 2 + 2/t there is a
      rational weighting phi of the edges with 1 <= |phi e| <= r - 1 on every edge whose
      outgoing sum equals its incoming sum at every vertex.
    Definitions: [is_2t1_graph G t] - (2t+1)-regular and every odd vertex set has a cut of
      at least 2t+1 edges (D1.v); [mreg G d] - every vertex has multigraph degree d (D1.v);
      [mdeg v] - the degree of v, that is, the number of ARC ENDS at v, so that a loop
      contributes 2, and [cut S] - edges with exactly one endpoint in S
      (cycle-theory/theories/foundations/connectivity.v);
      [circular_flow_number_le G c] - G has a nowhere-zero r-flow for every rational r > c
      (D1.v); [has_nz_rflow G r] and [rconservative] - nowhere-zero rational r-flow and
      Kirchhoff conservation, sum over edges with source v equals sum over edges with
      target v (D1.v).
    Notes: the circular flow number is an infimum, so the bound F_c(G) <= c is encoded by
      the up-set of feasible values, "a nowhere-zero r-flow for every rational r > c";
      flow values are rationals rather than reals, and orientations are absorbed into the
      sign of phi on the intrinsic [source]/[target] orientation of the multigraph edges.
      The guard [0 < #|G|] excludes the empty graph. *)
Definition circular_flow_numbers_of_r_graphs_statement : Prop :=
  forall (t : nat) (G : mgraph),
    (1 < t)%N -> (0 < #|G|)%N -> is_2t1_graph G t ->
    circular_flow_number_le G (2%:R + 2%:R / t%:R).

(** ================================================================= *)
(** ** Bidirected graphs and Bouchet's 6-flow conjecture *)

Definition is_sign (s : int) : bool := (s == 1) || (s == -1).

(** Bidirected graph = an [mgraph] with a sign [±1] at each endpoint of each
    edge ([ss] at the [source]-end, [st] at the [target]-end). *)
Definition is_bidirected (G : mgraph) (ss st : edge G -> int) : Prop :=
  forall e : edge G, is_sign (ss e) /\ is_sign (st e).

(** Bidirected vertex balance: the signed sum of incident edge weights at [v]. *)
Definition bnet (G : mgraph) (ss st : edge G -> int) (phi : edge G -> int)
    (v : G) : int :=
  \sum_(e | source e == v) ss e * phi e + \sum_(e | target e == v) st e * phi e.

(** [G] (with signature [ss],[st]) has a nowhere-zero [k]-flow. *)
Definition has_nz_biflow (G : mgraph) (ss st : edge G -> int) (k : nat) : Prop :=
  exists phi : edge G -> int,
    (forall v : G, bnet ss st phi v = 0) /\
    (forall e : edge G, (1 <= `|phi e|)%R /\ (`|phi e| <= (k.-1)%:R)%R).

(** ** Row 2 — Bouchet's 6-flow conjecture *)
(** Corpus row: opg:bouchets_6_flow_conjecture
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/bouchets_6_flow_conjecture/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/bouchets_6_flow_conjecture.json
    English statement: (Open Problem Garden, "Bouchet's 6-flow conjecture")
      Let G be a multigraph with at least one edge, equipped with a bidirection, that is, a
      sign +1 or -1 at each of the two ends of each edge. If G has a nowhere-zero k-flow
      for some natural number k, then G has a nowhere-zero 6-flow: an integer weighting phi
      of the edges with 1 <= |phi e| <= 5 on every edge whose signed sum at every vertex is
      zero.
    Definitions: [is_sign s] - s is 1 or -1 (D1.v); [is_bidirected ss st] - ss and st give
      the signs at the source end and at the target end of every edge (D1.v); [bnet ss st
      phi v] - the signed balance at v, the sum of ss e * phi e over the edges with source
      v plus the sum of st e * phi e over the edges with target v (D1.v);
      [has_nz_biflow ss st k] - some integer phi has zero balance at every vertex and
      1 <= |phi e| <= k - 1 on every edge (D1.v).
    Notes: the bound |phi e| <= k.-1 makes "nowhere-zero 6-flow" mean 1 <= |phi e| <= 5;
      the hypothesis k is existentially quantified with no constraint, so k = 0 or k = 1
      would make the hypothesis unsatisfiable on a graph with an edge, not the conclusion
      trivial. The guard [0 < #|edge G|] excludes the edgeless graph. *)
Definition bouchets_6_flow_statement : Prop :=
  forall (G : mgraph) (ss st : edge G -> int),
    (0 < #|edge G|)%N -> is_bidirected ss st ->
    (exists k : nat, has_nz_biflow ss st k) -> has_nz_biflow ss st 6.

(** ================================================================= *)
(** ** Cycle space of a simple graph and cycle-continuous maps *)

(** The (2-element) edge set of a simple graph, as a set of vertex pairs. *)
Definition sedge (G : sgraph) : {set {set G}} :=
  [set e : {set G} | [exists x, [exists y, (x -- y) && (e == [set x; y])]]].

(** Binary cycle space: an even subgraph (every vertex has even degree). *)
Definition in_cycle_space (G : sgraph) (C : {set {set G}}) : Prop :=
  C \subset sedge G /\
  (forall v : G, ~~ odd #|[set e in C | v \in e]|).

(** A cycle-continuous map [f : E(G) -> E(H)]: it sends edges to edges and the
    pre-image of every cycle-space element of [H] is a cycle-space element
    of [G]. *)
Definition cycle_continuous (G H : sgraph) (f : {set G} -> {set H}) : Prop :=
  (forall e : {set G}, e \in sedge G -> f e \in sedge H) /\
  (forall C : {set {set H}}, in_cycle_space C ->
     in_cycle_space [set e in sedge G | f e \in C]).

(** ** Row 3 — Antichains in the cycle-continuous order *)
(** Corpus row: opg:antichains_in_the_cycle_continuous_order
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/antichains_in_the_cycle_continuous_order/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/antichains_in_the_cycle_continuous_order.json
    English statement: (Open Problem Garden, "Antichains in the cycle continuous order")
      There is a family of simple graphs G_0, G_1, G_2, ... indexed by the natural numbers
      such that each G_i has at least one edge and, for all indices i and j with i
      different from j, no map from the edge set of G_i to the edge set of G_j is
      cycle-continuous. Since the condition is imposed on the ordered pair (i, j) for both
      orders, this rules out cycle-continuous maps in either direction between two distinct
      members.
    Definitions: [sedge G] - the set of two-element vertex sets that are edges of the
      simple graph G (D1.v); [in_cycle_space C] - C is a set of edges of G in which every
      vertex lies on an even number of edges, that is, an element of the binary cycle space
      (D1.v); [cycle_continuous f] - f sends edges to edges and the pre-image of every
      cycle-space element of the target is a cycle-space element of the source (D1.v).
    Notes: "infinite set of graphs" is modelled as a family indexed by [nat]; the members
      are not required to be pairwise non-isomorphic, but the no-map condition forces this,
      since the identity is cycle-continuous. Requiring each member to have an edge
      strengthens the existential claim and excludes the degenerate edgeless family, which
      would not be a witness anyway, because between edgeless graphs every map is
      vacuously cycle-continuous. *)
Definition antichains_in_the_cycle_continuous_order_statement : Prop :=
  exists Gs : nat -> sgraph,
    (forall i : nat, sedge (Gs i) != set0) /\
    (forall i j : nat, i <> j ->
       ~ exists f : {set (Gs i)} -> {set (Gs j)}, cycle_continuous f).

(** ================================================================= *)
(** ** Edge-connectivity flows: 3-flow, 4-flow, 5-flow *)

(** ** Row 4 — Tutte's 3-flow conjecture *)
(** Corpus row: opg:3_flow_conjecture
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/3_flow_conjecture/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/3_flow_conjecture.json
    English statement: (Open Problem Garden, "3-flow conjecture")
      Every multigraph with at least one edge that is 4-edge-connected, that is, deleting
      any set of at most three edges leaves it connected, has a nowhere-zero 3-flow: an
      integer weighting phi of the edges with 1 <= |phi e| <= 2 on every edge whose sum
      over the edges leaving a vertex equals the sum over the edges entering it, at every
      vertex.
    Definitions: [edge_connected G k] - deleting any edge set of size less than k leaves
      every pair of vertices joined by a walk (cycle-theory/theories/foundations/
      connectivity.v); [has_nz_kflow G k] - some integer edge weighting is [iconservative]
      (out-sum equals in-sum at every vertex) and [int_bounded k] (1 <= |phi e| <= k - 1)
      (D1.v).
    Notes: edges carry the intrinsic [source]/[target] orientation of [mgraph] and negative
      weights reverse it, so no separate orientation is quantified. The guard
      [0 < #|edge G|] excludes the edgeless graph. *)
Definition three_flow_statement : Prop :=
  forall G : mgraph,
    (0 < #|edge G|)%N -> edge_connected G 4 -> has_nz_kflow G 3.

(** Minor model of a simple graph [H] inside a multigraph [G]: disjoint
    nonempty connected branch sets, one per vertex of [H], joined by an edge of
    [G] whenever the corresponding vertices are adjacent in [H]. *)
Definition mg_branch_connected (G : mgraph) (A : {set G}) : Prop :=
  forall x y : G, x \in A -> y \in A ->
    exists w : seq (edge G),
      uwalk x y w /\ all (fun e => (source e \in A) && (target e \in A)) w.

Definition mg_minor (G : mgraph) (H : sgraph) : Prop :=
  exists phi : H -> {set G},
    [/\ (forall x : H, phi x != set0),
        (forall x y : H, x != y -> [disjoint phi x & phi y]),
        (forall x : H, mg_branch_connected (phi x))
      & (forall x y : H, x -- y -> exists e : edge G,
           ((source e \in phi x) && (target e \in phi y)) ||
           ((source e \in phi y) && (target e \in phi x)))].

(** The Petersen graph on [ 'I_10 ]: outer 5-cycle [0..4], spokes [i ~ i+5],
    inner pentagram on [5..9]. *)
Definition pedges : seq (nat * nat) :=
  [:: (0,1); (1,2); (2,3); (3,4); (4,0);
      (0,5); (1,6); (2,7); (3,8); (4,9);
      (5,7); (7,9); (9,6); (6,8); (8,5) ]%N.
Definition pconn (a b : nat) : bool := ((a, b) \in pedges) || ((b, a) \in pedges).
Definition padj (x y : 'I_10) : bool := (x != y) && pconn (val x) (val y).

Lemma padj_sym : symmetric padj.
Proof. by move=> x y; rewrite /padj /pconn eq_sym orbC. Qed.

Lemma padj_irrefl : irreflexive padj.
Proof. by move=> x; rewrite /padj eqxx. Qed.

Definition petersen : sgraph := SGraph padj_sym padj_irrefl.

(** ** Row 6 — Tutte's 4-flow conjecture *)
(** Corpus row: opg:4_flow_conjecture
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/4_flow_conjecture/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/4_flow_conjecture.json
    English statement: (Open Problem Garden, "4-flow conjecture")
      Every bridgeless multigraph with at least one edge that has no Petersen graph minor
      has a nowhere-zero 4-flow: an integer weighting phi of the edges with
      1 <= |phi e| <= 3 on every edge whose out-sum equals its in-sum at every vertex.
    Definitions: [bridgeless G] - no edge e is such that every walk between its endpoints
      uses e (cycle-theory/theories/foundations/connectivity.v); [mg_minor G H] - there are
      pairwise disjoint nonempty vertex sets of G, one per vertex of H, each connected by
      walks staying inside it, with an edge of G between the sets of any two adjacent
      vertices of H (D1.v); [mg_branch_connected] - internal connectivity of a branch set
      (D1.v); [petersen] - the Petersen graph on ten vertices given by an explicit edge
      list, outer 5-cycle, spokes and inner pentagram (D1.v); [has_nz_kflow] (D1.v).
    Notes: the minor is taken with H a simple graph and G a multigraph; the branch sets
      must be connected in G restricted to them, and adjacency only requires one joining
      edge in either direction. *)
Definition four_flow_statement : Prop :=
  forall G : mgraph,
    (0 < #|edge G|)%N -> bridgeless G -> ~ mg_minor G petersen ->
    has_nz_kflow G 4.

(** ** Row 7 — Tutte's 5-flow conjecture *)
(** Corpus row: opg:5_flow_conjecture
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/5_flow_conjecture/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/5_flow_conjecture.json
    English statement: (Open Problem Garden, "5-flow conjecture")
      Every bridgeless multigraph with at least one edge has a nowhere-zero 5-flow: an
      integer weighting phi of the edges with 1 <= |phi e| <= 4 on every edge whose sum
      over the edges leaving a vertex equals the sum over the edges entering it, at every
      vertex.
    Definitions: [bridgeless G] - no edge is a bridge, that is, a cut edge: an edge that
      every UNDIRECTED walk between its endpoints must use
      (cycle-theory/theories/foundations/connectivity.v);
      [has_nz_kflow G k] - nowhere-zero integer k-flow, [iconservative] plus
      [int_bounded k] (D1.v).
    Notes: "bridgeless" is the textbook "no cut edge".
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
      deletion separates its ends is a bridge). *)
Definition five_flow_statement : Prop :=
  forall G : mgraph,
    (0 < #|edge G|)%N -> bridgeless G -> has_nz_kflow G 5.

(** ================================================================= *)
(** ** Unit-vector (S^2) flows *)

Section UnitVector.
Variable R : rcfType.

(** A unit vector of [R^3] (a point of [S^2]). *)
Definition sphere_vec (x : 'rV[R]_3) : bool := \sum_(i < 3) (x ord0 i) ^+ 2 == 1.

(** Vector flow conservation (Kirchhoff, componentwise). *)
Definition vconservative (G : mgraph) (phi : edge G -> 'rV[R]_3) : Prop :=
  forall v : G, \sum_(e | source e == v) phi e = \sum_(e | target e == v) phi e.

End UnitVector.

(** ** Row 8 — Unit-vector flows (primary conjecture) *)
(** Corpus row: opg:unit_vector_flows
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/unit_vector_flows/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/unit_vector_flows.json
    English statement: (Open Problem Garden, "Unit vector flows")
      For every real-closed field R and every bridgeless multigraph G with at least one
      edge there is an assignment of a unit vector of R^3, that is, a row vector whose
      three coordinates have squares summing to 1, to each edge of G, such that at every
      vertex the componentwise sum of the vectors on the edges leaving the vertex equals
      the componentwise sum on the edges entering it.
    Definitions: [sphere_vec x] - the three coordinates of the row vector x have squares
      summing to 1, a point of the unit sphere (D1.v); [vconservative phi] - componentwise
      Kirchhoff conservation at every vertex (D1.v); [bridgeless] (cycle-theory/theories/
      foundations/connectivity.v).
    Notes: the original conjecture is the case R = R, the real numbers; it is stated here
      over an arbitrary real-closed field so that it stays first-order and axiom-free.
      Unit vectors are nonzero, so "nowhere-zero" is automatic and is not stated
      separately. The corpus row carries a second conjecture, about a labelling q of the
      sphere; it is formalized just below as [unit_vector_flows_q_statement], which owns no
      corpus row of its own. *)
Definition unit_vector_flows_statement : Prop :=
  forall (R : rcfType) (G : mgraph),
    (0 < #|edge G|)%N -> bridgeless G ->
    exists phi : edge G -> 'rV[R]_3,
      (forall e : edge G, sphere_vec (phi e)) /\ vconservative phi.

(** No corpus row: this is the SECOND conjecture printed on the corpus row
    opg:unit_vector_flows, whose formal_name is the preceding
    [unit_vector_flows_statement]; the row owns only one formal name, so this companion
    statement has none. It says: for every real-closed field R there is a labelling q of
    the unit sphere of R^3 by integers with 1 <= |q x| <= 4, opposite on antipodal points,
    such that any three unit vectors summing to the zero vector, that is, three points
    equidistant on a great circle, receive labels summing to zero. *)
Definition unit_vector_flows_q_statement : Prop :=
  forall R : rcfType, exists q : 'rV[R]_3 -> int,
    [/\ (forall x, sphere_vec x -> (q x != 0) && (`|q x| <= 4)%R),
        (forall x, sphere_vec x -> q (- x) = - q x)
      & (forall a b c, sphere_vec a -> sphere_vec b -> sphere_vec c ->
           a + b + c = 0 -> q a + q b + q c = 0)].

(** ================================================================= *)
(** ** Row 9 — 5-local-tensions on embedded graphs *)
(** OPEN.

    Source: "There exists a fixed constant [c] so that every embedded (loopless)
    graph with edge-width [>= c] has a 5-local-tension."

    A surface embedding is modelled as a rotation system: a permutation [sigma]
    of the darts ([edge G * bool]; the involution [dflip] pairs the two darts of
    an edge).  Faces are the orbits of [sigma o dflip].  A cycle is contractible
    when its edge set lies in the GF(2)-span of the facial boundaries; the
    edge-width is the length of a shortest noncontractible circuit. *)

Section Embedding.
Variable G : mgraph.

Definition dart := (edge G * bool)%type.
Definition dflip (d : dart) : dart := (d.1, ~~ d.2).

Lemma dflip_inj : injective dflip.
Proof. by move=> [e b] [e' b'] [] -> /negb_inj ->. Qed.

Definition dalpha : {perm dart} := perm dflip_inj.

Variable sigma : {perm dart}.

(** Faces = orbits of [sigma o dflip]. *)
Definition facemap : {perm dart} := (sigma * dalpha)%g.
Definition faces : {set {set dart}} := porbits facemap.

(** Direction sign of a dart relative to the reference orientation. *)
Definition dsign (d : dart) : int := if d.2 then 1 else -1.

(** Boundary of a face [O] as a GF(2) edge vector: the edges with exactly one
    dart in [O]. *)
Definition fbound (O : {set dart}) : {set edge G} :=
  [set e : edge G | ((e, true) \in O) (+) ((e, false) \in O)].

(** GF(2) symmetric difference and contractible cycles (sums of face
    boundaries). *)
Definition symd (A B : {set edge G}) : {set edge G} := (A :|: B) :\: (A :&: B).
Definition contractible (C : {set edge G}) : Prop :=
  exists g : {set dart} -> bool,
    C = \big[symd/set0]_(O in faces | g O) fbound O.

(** Edge-width [>= c]: every noncontractible circuit has at least [c] edges. *)
Definition edge_width_geq (c : nat) : Prop :=
  forall C : {set edge G}, is_circuit C -> ~ contractible C -> (c <= #|C|)%N.

(** A nowhere-zero [k]-local-tension: an integer edge weighting with
    [1 <= |t e| <= k-1] whose signed sum around every face is zero. *)
Definition local_tension (k : nat) (t : edge G -> int) : Prop :=
  (forall e : edge G, (1 <= `|t e|)%R /\ (`|t e| <= (k.-1)%:R)%R) /\
  (forall O : {set dart}, O \in faces -> \sum_(d in O) dsign d * t d.1 = 0).

Definition has_5_local_tension : Prop := exists t, local_tension 5 t.

End Embedding.

(** Corpus row: opg:5_local_tensions
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/5_local_tensions/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/5_local_tensions.json
    English statement: (Open Problem Garden, "5-local-tensions")
      There exists a natural number c such that for every loopless multigraph G and every
      rotation system on G, that is, a permutation of the darts of G, if the embedding has
      edge-width at least c, meaning that every noncontractible circuit uses at least c
      edges, then G has a nowhere-zero 5-local-tension: an integer weighting t of the edges
      with 1 <= |t e| <= 4 on every edge whose signed sum around every face is zero.
    Definitions: [dart] - a pair of an edge and a Boolean, the two directions of an edge,
      and [dflip], [dalpha] - the involution exchanging them (D1.v); [facemap] - the
      permutation sigma * dalpha, and [faces] - its orbits, the faces of the embedding
      (D1.v); [dsign d] - the direction sign of a dart, 1 or -1 (D1.v); [fbound O] - the
      boundary of a face as the set of edges having exactly one dart in O (D1.v); [symd] -
      symmetric difference of edge sets and [contractible C] - C is a symmetric-difference
      sum of face boundaries, that is, lies in the GF(2)-span of the facial boundaries
      (D1.v); [edge_width_geq c] - every circuit that is not contractible has at least c
      edges (D1.v); [local_tension k t] - 1 <= |t e| <= k - 1 on every edge and the signed
      sum of t over the darts of every face is zero, with [has_5_local_tension] its case
      k = 5 (D1.v); [is_circuit C] - a nonempty connected 2-regular edge set
      (cycle-theory/theories/foundations/connectivity.v); [loopless G] - no edge joins a
      vertex to itself (base/theories/base.v).
    Notes: the surface embedding is modelled combinatorially by a rotation system rather
      than by a topological surface; contractibility is the algebraic GF(2) notion, not the
      homotopy notion. The constant c is existentially quantified, as in the source; the
      source's parenthetical guess that c = 4 probably suffices is not formalized. *)
Definition five_local_tensions_statement : Prop :=
  exists c : nat,
    forall (G : mgraph) (sigma : {perm (edge G * bool)}),
      loopless G -> edge_width_geq sigma c -> has_5_local_tension sigma.

(** ================================================================= *)
(** ** Row 10 — Jaeger's modular orientation conjecture *)
(** OPEN.

    Source: "Every [4k]-edge-connected graph can be oriented so that
    indegree(v) - outdegree(v) ≡ 0 (mod [2k+1]) for every vertex [v]."

    An orientation [o : edge G -> bool] keeps ([true]) or reverses ([false])
    each edge's reference direction. *)
Definition otail (G : mgraph) (o : edge G -> bool) (e : edge G) : G :=
  if o e then source e else target e.
Definition ohead (G : mgraph) (o : edge G -> bool) (e : edge G) : G :=
  if o e then target e else source e.
Definition imbalance (G : mgraph) (o : edge G -> bool) (v : G) : int :=
  ((#|[set e | ohead o e == v]|)%:R - (#|[set e | otail o e == v]|)%:R)%R.

(** Corpus row: opg:jaegers_modular_orientation_conjecture
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/jaegers_modular_orientation_conjecture/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/jaegers_modular_orientation_conjecture.json
    English statement: (Open Problem Garden, "Jaeger's modular orientation conjecture")
      For every positive natural number k and every multigraph G with at least one edge
      that is 4k-edge-connected, there is an orientation of the edges of G such that at
      every vertex v the indegree of v minus the outdegree of v is an integer multiple of
      2k+1, that is, is congruent to 0 modulo 2k+1.
    Definitions: [otail o e] and [ohead o e] - the tail and the head of edge e under the
      orientation o, which keeps the intrinsic source-to-target direction when [o e] is
      true and reverses it otherwise (D1.v); [imbalance o v] - the number of edges with
      head v minus the number of edges with tail v, as an integer (D1.v);
      [edge_connected G k] - deleting fewer than k edges keeps the graph connected
      (cycle-theory/theories/foundations/connectivity.v).
    Notes: an orientation is a Boolean choice per edge on top of the intrinsic
      [source]/[target] orientation of [mgraph]; divisibility by 2k+1 is expressed as the
      existence of an integer q with imbalance = (2k+1) * q. The guard [0 < k] excludes
      k = 0, where the modulus would be 1 and the statement trivial. *)
Definition jaegers_modular_orientation_statement : Prop :=
  forall (k : nat) (G : mgraph),
    (0 < #|edge G|)%N -> (0 < k)%N -> edge_connected G (4 * k)%N ->
    exists o : edge G -> bool,
      forall v : G, exists q : int, imbalance o v = ((2 * k + 1)%N)%:R * q.

(** ================================================================= *)
(** ** Flow polynomial *)

(** Component relation of a spanning subgraph [(V, S)] and its component count. *)
Definition erel (G : mgraph) (S : {set edge G}) : rel G :=
  fun x y => [exists e, (e \in S) &&
    (((source e == x) && (target e == y)) ||
     ((source e == y) && (target e == x)))].
Definition ncomp (G : mgraph) (S : {set edge G}) : nat := n_comp (erel S) [set: G].

(** Cycle-space dimension (nullity) of [(V, S)]: [|S| - |V| + c(S)]. *)
Definition nullity (G : mgraph) (S : {set edge G}) : nat :=
  (#|S| + ncomp S - #|G|)%N.

(** Flow polynomial [Phi(G,x) = sum_{S ⊆ E} (-1)^{|E\S|} x^{nullity S}]: for
    integer [k] it counts nowhere-zero [k]-flows. *)
Definition flow_poly_eval (G : mgraph) (x : rat) : rat :=
  \sum_(S : {set edge G}) (-1) ^+ (#|edge G| - #|S|) * x ^+ nullity S.
Definition flow_poly (G : mgraph) : {poly int} :=
  \sum_(S : {set edge G}) (-1) ^+ (#|edge G| - #|S|) *: 'X^(nullity S).

(** ** Row 11 — Half-integral flow-polynomial values *)
(** Corpus row: opg:half_integral_flow_polynomial_values
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/half_integral_flow_polynomial_values/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/half_integral_flow_polynomial_values.json
    English statement: (Open Problem Garden, "Half-integral flow polynomial values")
      For every multigraph G with at least one vertex that is 2-edge-connected, that is,
      connected and with no bridge, the flow polynomial of G evaluated at the rational
      number 11/2 = 5.5 is strictly positive, where the flow polynomial at x is the sum
      over all subsets S of the edge set of (-1) to the power |E| - |S| times x to the
      power of the nullity of S, the nullity being |S| plus the number of connected
      components of the spanning subgraph with edge set S minus the number of vertices.
    Definitions: [erel S] - adjacency through an edge of S, and [ncomp S] - the number of
      connected components of the spanning subgraph with edge set S (D1.v); [nullity S] -
      the cycle-space dimension |S| + c(S) - |V| (D1.v); [flow_poly_eval G x] - the flow
      polynomial evaluated at a rational x (D1.v); [two_edge_connected G] - connected and
      bridgeless (cycle-theory/theories/foundations/connectivity.v).
    Notes: for a positive integer k the same expression counts the nowhere-zero k-flows of
      G, which is how the source introduces the polynomial; this identity is not proved
      here, so the statement is about the stated alternating sum. [nullity] uses truncated
      natural subtraction, which is harmless because |S| + c(S) >= |V| always holds for a
      spanning subgraph. *)
Definition half_integral_flow_polynomial_values_statement : Prop :=
  forall G : mgraph,
    (0 < #|G|)%N -> two_edge_connected G ->
    (0 < flow_poly_eval G (11%:R / 2%:R))%R.

(** ** Row 13 — Real roots of the flow polynomial *)
(** Corpus row: opg:real_roots_of_the_flow_polynomial
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/real_roots_of_the_flow_polynomial/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/real_roots_of_the_flow_polynomial.json
    English statement: (Open Problem Garden, "Real roots of the flow polynomial")
      For every multigraph G whose flow polynomial is not the zero polynomial, for every
      real-closed field F and every element z of F, if z is a root of the image in F of the
      flow polynomial of G, then z <= 4.
    Definitions: [flow_poly G] - the flow polynomial with integer coefficients, the sum
      over all edge subsets S of (-1) to the power |E| - |S| times the monomial X to the
      power of the nullity of S (D1.v); [nullity], [ncomp], [erel] (D1.v).
    Notes: "real roots" are modelled as roots in an arbitrary real-closed field, the
      integer coefficients being mapped into it with [map_poly]; the original statement is
      the case of the real numbers. The nonzero-polynomial hypothesis is exactly the
      source's "nonzero flow polynomials". *)
Definition real_roots_of_the_flow_polynomial_statement : Prop :=
  forall G : mgraph, flow_poly G != 0 ->
    forall (F : rcfType) (z : F),
      root (map_poly (fun n : int => n%:~R : F) (flow_poly G)) z -> (z <= 4%:R)%R.

(** ================================================================= *)
(** ** Group / B-flows and the Cayley homomorphism problem *)

Section CayleyGraph.
Variables (M : finGroupType) (B : {set M}).

Definition cradj (x y : M) : bool :=
  (x != y) && (((x^-1 * y)%g \in B) || ((y^-1 * x)%g \in B)).

Lemma cradj_sym : symmetric cradj.
Proof. by move=> x y; rewrite /cradj eq_sym orbC. Qed.

Lemma cradj_irrefl : irreflexive cradj.
Proof. by move=> x; rewrite /cradj eqxx. Qed.

Definition cayley : sgraph := SGraph cradj_sym cradj_irrefl.

End CayleyGraph.

(** A [B]-flow of [G] in the abelian group [M]: each edge weight lies in [B] and
    the group-products around each vertex balance. *)
Definition Bflow (M : finGroupType) (G : mgraph) (B : {set M})
    (phi : edge G -> M) : Prop :=
  (forall e : edge G, phi e \in B) /\
  (forall v : G, (\prod_(e | source e == v) phi e)%g
               = (\prod_(e | target e == v) phi e)%g).

(** ** Row 12 — A homomorphism problem for flows *)
(** Corpus row: opg:a_homomorphism_problem_for_flows
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/a_homomorphism_problem_for_flows/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/a_homomorphism_problem_for_flows.json
    English statement: (Open Problem Garden, "A homomorphism problem for flows")
      Let M and M' be finite abelian groups, B a subset of M and B' a subset of M', each
      closed under taking inverses, that is, equal to the set of inverses of its elements.
      If there is a graph homomorphism from the Cayley graph of M with connection set B to
      the Cayley graph of M' with connection set B', then every multigraph that has a
      B-flow has a B'-flow, where a B-flow assigns to each edge an element of B so that at
      every vertex the product of the values on the edges leaving the vertex equals the
      product of the values on the edges entering it.
    Definitions: [cayley B] - the Cayley graph of the group on the vertex set of all group
      elements, with x adjacent to y when x is different from y and x inverse times y, or y
      inverse times x, lies in B (D1.v); [Bflow B phi] - every edge value lies in B and the
      products at source-side and target-side balance at every vertex (D1.v);
      [base.is_hom f] - a homomorphism of simple graphs, qualified to avoid the
      [mgraph] notion of the same name (base/theories/base.v).
    Notes: groups are written multiplicatively, so the source's condition B = -B becomes
      "B equals the image of B under inversion"; abelianness is stated as [abelian [set: M]]
      on the whole group. The groups are restricted to FINITE groups
      ([finGroupType]) whereas the source says only "abelian groups"; the Rocq statement is
      therefore weaker than the source for infinite groups. *)
Definition a_homomorphism_problem_for_flows_statement : Prop :=
  forall (M M' : finGroupType) (B : {set M}) (B' : {set M'}),
    abelian [set: M] -> abelian [set: M'] ->
    B = [set (x^-1)%g | x in B] -> B' = [set (x^-1)%g | x in B'] ->
    (* [base.is_hom] qualified explicitly: both base's sgraph hom and
       mgraph's [is_hom] are in scope; the qualifier makes the intended
       sgraph homomorphism robust to import-order edits. *)
    (exists f : cayley B -> cayley B', base.is_hom f) ->
    forall G : mgraph,
      (exists phi : edge G -> M, Bflow B phi) ->
      (exists psi : edge G -> M', Bflow B' psi).

(** ================================================================= *)
(** ** Row 14 — Circular flow number of regular class-1 graphs *)
(** Corpus row: opg:circular_flow_number_of_regular_class_1_graphs
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/circular_flow_number_of_regular_class_1_graphs/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/circular_flow_number_of_regular_class_1_graphs.json
    English statement: (Open Problem Garden, "Circular flow number of regular class 1
      graphs")
      For every integer t >= 1 and every LOOPLESS multigraph G with at least one vertex in
      which every vertex has degree exactly 2t+1, if G is class 1, that is, its chromatic
      index equals its maximum degree, then the circular flow number of G is at most
      2 + 2/t: for every rational r > 2 + 2/t there is a rational weighting phi of the
      edges with 1 <= |phi e| <= r - 1 on every edge whose out-sum equals its in-sum at
      every vertex.
    Definitions: [loopless G] - no edge joins a vertex to itself (coq-graph-theory mgraph,
      re-exported by base/theories/base.v); [mreg G d] - every vertex has multigraph degree
      d (D1.v); [mDelta G] - the maximum multigraph degree, and [is_class1 G] - the
      chromatic index equals [mDelta G] (D1.v); [chromatic_index G] - the chromatic number
      of the line graph of G (base/theories/base.v); [circular_flow_number_le G c] - a
      nowhere-zero rational r-flow for every rational r > c, with [has_nz_rflow] and
      [rconservative] (D1.v); [mdeg] - the degree counting ARC ENDS, so a loop contributes
      2, which on this loopless carrier agrees with the incidence count
      (cycle-theory/theories/foundations/connectivity.v).
    Notes: the corpus status is PARTIAL, known for some regularities, open in general. As
      in the sibling row on (2t+1)-graphs, the infimum F_c(G) is encoded by "for every
      rational r above the bound there is a nowhere-zero r-flow". The guard [0 < #|G|]
      excludes the empty graph.
      LOOPLESS GUARD (2026-09-23, second-reader prescription): the hypothesis [loopless G]
      was ADDED to the body, and it is what the source means by a class-1 graph. The source
      defines class 1 by "the edge chromatic number equals the maximum degree", and a graph
      with a loop has no proper edge colouring at all, so its edge chromatic number is
      undefined and loopful graphs are outside the source's class. The encoding did not
      exclude them: base's [line_graph] makes a LOOP non-adjacent to ITSELF (adjacency is
      [(e1 != e2) && share_endpoint e1 e2]), so [chromatic_index] stays FINITE on a loopful
      carrier and [is_class1] can hold there. Since the degree repair of 2026-09-23 gives a
      loop TWO arc ends, such carriers also satisfy [mreg G 3] and so entered the class:
      four vertices x, y, u, v with three parallel edges x-y, a loop at u, an edge u-v and a
      loop at v is 3-regular, has chromatic index 3 = [mDelta] (three parallel edges force
      3, and {a, loop at u, loop at v} / {b, u-v} / {c} is a proper 3-colouring of the line
      graph) and so was class 1 -- yet it has NO nowhere-zero r-flow for any r: at u the
      loop occurs in both Kirchhoff sums and cancels, so [rconservative] forces
      phi(u-v) = 0, contradicting 1 <= |phi(u-v)|. The row was therefore SPURIOUSLY
      refutable, by a graph the source excludes rather than by the real (published)
      counterexamples of Mattiolo-Steffen. The guard is machine-checked to have teeth and to
      be non-vacuous: [grounding_D1.class1_3reg_loopful_Gcl] (that carrier is [mreg _ 3] and
      [is_class1] but NOT [loopless]) and [grounding_D1.loopless_class1_3reg_G3p] (the
      loopless 3-regular class-1 triple edge). The SIBLING row
      [circular_flow_numbers_of_r_graphs_statement] needs no such guard: its
      [is_2t1_graph G t] hypothesis IMPLIES looplessness, which is a theorem, not a reading
      ([grounding_D1.is_2t1_loopless], from [grounding_D1.mdeg_cut]: degree = cut + twice
      the loops, and the odd cut [ [set v] ] already uses up all 2t+1 of them). See
      meta/X211-X229_faithfulness_audit.md and meta/STATEMENT_IMPROVEMENTS.md. *)
Definition circular_flow_number_of_regular_class_1_graphs_statement : Prop :=
  forall (t : nat) (G : mgraph),
    (1 <= t)%N -> (0 < #|G|)%N -> loopless G ->
    mreg G (2 * t + 1)%N -> is_class1 G ->
    circular_flow_number_le G (2%:R + 2%:R / t%:R).

(** ================================================================= *)
(** ** Row 15 — Three 4-flows conjecture *)
(** Corpus row: opg:three_4_flows_conjecture
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/three_4_flows_conjecture/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/three_4_flows_conjecture.json
    English statement: (Open Problem Garden, "The three 4-flows conjecture")
      For every bridgeless multigraph G with at least one edge there are three pairwise
      disjoint sets of edges A1, A2, A3 whose union is the whole edge set, such that for
      each i the graph obtained from G by deleting A_i has a nowhere-zero 4-flow: an
      integer weighting of the edges that vanishes on A_i, satisfies 1 <= |phi e| <= 3 on
      every edge outside A_i, and whose out-sum equals its in-sum at every vertex.
    Definitions: [has_nz_kflow_del G A k] - a flow supported off A, conservative on the
      whole vertex set, zero on A and with 1 <= |phi e| <= k - 1 off A (D1.v);
      [iconservative] (D1.v); [bridgeless] (cycle-theory/theories/foundations/
      connectivity.v).
    Notes: edge deletion is modelled without building a subgraph: the flow lives on G and
      is required to be zero exactly on the deleted set, which is equivalent to a
      nowhere-zero 4-flow of G minus A_i since conservation at every vertex is unaffected
      by edges carrying weight zero. *)
Definition three_4_flows_statement : Prop :=
  forall G : mgraph,
    (0 < #|edge G|)%N -> bridgeless G ->
    exists A1 A2 A3 : {set edge G},
      [/\ [disjoint A1 & A2], [disjoint A1 & A3], [disjoint A2 & A3],
          A1 :|: A2 :|: A3 = [set: edge G]
        & [/\ has_nz_kflow_del A1 4, has_nz_kflow_del A2 4
            & has_nz_kflow_del A3 4]].

(** ================================================================= *)
(** ** Row 5 — Approximation ratio for k-outerplanar / treewidth graphs *)
(** OPEN (Problem).

    Source: "Is the approximation ratio for Maximum Edge-Disjoint Paths (MaxEDP)
    or Maximum Integer Multiflow (MaxIMF) bounded by a constant in k-outerplanar
    or tree-width graphs?"  Formalized (planarity-free) as a bounded
    integrality gap on the bounded-treewidth class: for each treewidth bound
    [w] there is a constant [c] so that any fractional multiflow value is within
    a factor [c] of some integral edge-disjoint routing. *)

(** [P] contains an [s]-[t] walk (routes the demand [(s,t)]). *)
Definition routes (G : mgraph) (P : {set edge G}) (s t : G) : Prop :=
  exists w : seq (edge G), uwalk s t w /\ all (fun e => e \in P) w.

(** An integral edge-disjoint routing of distinct demands of [dem]. *)
Definition edp_feasible (G : mgraph) (dem : seq (G * G))
    (L : seq ((G * G) * {set edge G})) : Prop :=
  uniq (map (fun t => t.1) L) /\
  (forall t, t \in L -> t.1 \in dem /\ routes t.2 t.1.1 t.1.2) /\
  (forall t s, t \in L -> s \in L -> t <> s -> [disjoint t.2 & s.2]).

(** A fractional multiflow: weighted demand-paths obeying unit edge capacities. *)
Definition frac_feasible (G : mgraph) (dem : seq (G * G))
    (L : seq (((G * G) * {set edge G}) * rat)) : Prop :=
  (forall t, t \in L ->
     [/\ t.1.1 \in dem, (0 <= t.2)%R & routes t.1.2 t.1.1.1 t.1.1.2]) /\
  (forall e : edge G, (\sum_(t <- L | e \in t.1.2) t.2 <= 1)%R).
Definition frac_value (G : mgraph)
    (L : seq (((G * G) * {set edge G}) * rat)) : rat := \sum_(t <- L) t.2.

(** Treewidth [<= w] of the underlying simple graph of [G]. *)
Definition vskel_rel (G : mgraph) (x y : G) : bool :=
  (x != y) && [exists e, ((source e == x) && (target e == y)) ||
                          ((source e == y) && (target e == x))].

Lemma vskel_sym (G : mgraph) : symmetric (@vskel_rel G).
Proof.
move=> x y; rewrite /vskel_rel eq_sym; congr (_ && _).
by apply/existsP/existsP=> -[e He]; exists e; rewrite orbC.
Qed.

Lemma vskel_irrefl (G : mgraph) : irreflexive (@vskel_rel G).
Proof. by move=> x; rewrite /vskel_rel eqxx. Qed.

Definition vskel (G : mgraph) : sgraph := SGraph (@vskel_sym G) (@vskel_irrefl G).

Definition mtreewidth_le (G : mgraph) (w : nat) : Prop :=
  exists (T : forest) (D : T -> {set vskel G}), sdecomp T (vskel G) D /\ (width D <= w)%N.

(** Corpus row: opg:approximation_ratio_for_k_outerplanar_graphs
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/approximation_ratio_for_k_outerplanar_graphs/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/approximation_ratio_for_k_outerplanar_graphs.json
    English statement: (Open Problem Garden, "Approximation ratio for k-outerplanar
      graphs")
      For every natural number w there is a rational constant c >= 1 such that, for every
      multigraph G whose underlying simple graph has treewidth at most w and every list of
      demands, each a pair of vertices, and for every feasible fractional multiflow, that
      is, a list of demand-path pairs with nonnegative rational weights obeying unit
      capacity on each edge, there is an integral routing of pairwise distinct demands by
      pairwise edge-disjoint edge sets such that the total value of the fractional
      multiflow is at most c times the number of demands routed integrally.
    Definitions: [routes P s t] - the edge set P contains an undirected walk from s to t
      (D1.v); [edp_feasible dem L] - L routes pairwise distinct demands taken from [dem] by
      pairwise disjoint edge sets (D1.v); [frac_feasible dem L] - every entry is a demand
      of [dem] with a nonnegative weight and a routing edge set, and for every edge the
      total weight of the entries using it is at most 1 (D1.v); [frac_value L] - the sum of
      the weights (D1.v); [vskel G] - the underlying simple graph of the multigraph G, and
      [mtreewidth_le G w] - it has a tree decomposition of width at most w (D1.v);
      [sdecomp], [width], [forest] (coq-graph-theory treewidth); [uwalk]
      (base/theories/base.v).
    Notes: PROXY ENCODING. The source asks a question, whether the approximation ratio for
      Maximum Edge Disjoint Paths or Maximum Integer Multiflow is bounded by a constant on
      k-outerplanar or bounded-treewidth graphs; the Rocq statement is the corresponding
      bounded integrality gap on the bounded-treewidth class, with no planarity and no
      k-outerplanarity, and no computation model, so it is an affirmative-answer
      formalization rather than the question itself. The integral routing is compared
      against the fractional optimum through the number of routed demands, which is the
      MaxEDP objective with unit demands. *)
Definition approximation_ratio_for_k_outerplanar_graphs_statement : Prop :=
  forall w : nat, exists c : rat, (1 <= c)%R /\
    forall (G : mgraph) (dem : seq (G * G)),
      mtreewidth_le G w ->
      forall L : seq (((G * G) * {set edge G}) * rat),
        frac_feasible dem L ->
        exists L' : seq ((G * G) * {set edge G}),
          edp_feasible dem L' /\ (frac_value L <= c * (size L')%:R)%R.
