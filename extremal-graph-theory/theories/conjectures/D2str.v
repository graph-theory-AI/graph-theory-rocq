(** * Extremal.conjectures.D2str — milestone D2str (namespace Extremal, plan v4)

    Statement-only formalizations (axiom-free: no Conjecture/Axiom/Parameter/
    Admitted) of five OPEN problems.  Each row gets one [Definition
    <formal_name> : Prop]; the carrier type is chosen PER ROW from its
    [rocq_idiom] (NOT a blanket [sgraph]).

    CARRIERS:
      - Row 1 (linear hypergraphs of incidence-poset dimension 3): a finite
        vertex type [T : finType] with a hyperedge family [E : {set {set T}}];
        the geometric conclusion lives in the plane [R * R] over an arbitrary
        ordered field [R : realFieldType].
      - Row 2 (geodesic cycles / Tutte): [G : sgraph] with a real edge-length
        assignment [ell : G -> G -> R] ([R : realFieldType]).
      - Row 3 (nearly spanning regular subgraphs): [G : sgraph] with a regular
        subgraph carried by a vertex set [S : {set G}] + an edge relation
        [adj : rel G]; ε–N (eventual) formulation with ε = p/q.
      - Row 4 (simultaneous partition of hypergraphs): two r-uniform families
        [E1 E2 : {set {set T}}] over [T : finType] with a part map
        [part : T -> 'I_r]; ε–N (eventual) formulation for the [o(m_i)] slack.
      - Row 5 (covering powers of cycles): the power [graph_power (cycle_graph n) k]
        (an [sgraph]); Ω(k) as a uniform linear lower bound.

    IMPORT ORDER: [base] (which re-exports all_boot + the undirected vocabulary
    and OWNS [graph_power], [regular]) is imported first; the mathcomp algebra
    layer is imported AFTER [base] so its canonical order/ring instances win.
    No multigraph [edge]/[source]/[target] API is needed (edges are modelled by
    the [sgraph] adjacency [--] / vertex SUBSETS), so [mgraph] is NOT imported.

    REUSE FROM base: [graph_power] (Row 5), [regular] (Row 3), [k_connected]
    (Row 2 — base owns the Whitney form, used verbatim).  Everything else is
    AREA-SPECIFIC and defined locally; the one construct that could migrate later
    is [cycle_graph] (a generic cycle family), tagged [@MOVE-to-base] below — it
    stays local until a 2nd area consumes it (only Row 5 uses it here).

    PARTIAL / FAITHFULNESS NOTES:
      - Row 1: the incidence poset is taken on the FULL ground type [T + {set T}]
        (subsets ∉ E sit as isolated points).  Isolated points never change a
        poset's order dimension across the "≤ 3" threshold (they are realised by
        any ≥2 linear extensions), so [incidence_poset_dim_le E 3] is faithful to
        the textbook incidence-poset dimension.  The plane is an arbitrary ordered
        field [R] rather than ℝ specifically; triangles/segments are convex hulls
        of 2/3 points via convex combinations, and "intersection hypergraph" is
        the points-in-regions incidence representation (v ∈ e ⟺ point v ∈ region e).
      - Row 2: weighted shortest walks are [shortest_walk] (minimal [ell]-length
        among ALL G-walks).  A cycle is [ell]-geodesic when, between any two of its
        vertices, SOME arc of the cycle is a shortest walk (the standard
        isometric/geodesic-cycle property).  A peripheral cycle is induced +
        non-separating ([connected (~: V(C))]).
      - Rows 3,4 use the EVENTUAL ε–N form (ratios cross-multiplied, nat
        truncated subtraction avoided), never an informal o/O token.
      - Row 5: Ω(k) is the asymptotic-in-n lower bound, so the n-regime is an
        EXISTENTIALLY-quantified growth threshold [g : nat -> nat] (n ≥ g k),
        NOT the bare [2k < n] guard (which is refutable via complete / cocktail-
        party near-complete powers — see the Row 5 comment). *)

From GTBase Require Import base.
From mathcomp Require Import all_algebra.

Import GRing.Theory Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ================================================================= *)
(** ** Generic finite-poset order dimension (used by Row 1)

    [le] is a finite partial order ([rel X]).  A linear extension is a total
    order containing [le]; a realizer is a list of linear extensions whose
    intersection is exactly [le]; [poset_dim_le le d] = a realizer of size ≤ d
    exists.  [rel X] is not an eqType, so realizer membership is index-based. *)

Definition is_linear_order (X : finType) (l : rel X) : Prop :=
  [/\ reflexive l, antisymmetric l, transitive l & total l].

Definition order_extends (X : finType) (le l : rel X) : Prop :=
  forall x y, le x y -> l x y.

Definition realizer (X : finType) (le : rel X) (ls : seq (rel X)) : Prop :=
  (forall i, i < size ls ->
     is_linear_order (nth (fun _ _ => false) ls i) /\
     order_extends le (nth (fun _ _ => false) ls i)) /\
  (forall x y, le x y <->
     (forall i, i < size ls -> (nth (fun _ _ => false) ls i) x y)).

Definition poset_dim_le (X : finType) (le : rel X) (d : nat) : Prop :=
  exists ls : seq (rel X), size ls <= d /\ realizer le ls.

(** ================================================================= *)
(** ** Plane objects (used by Row 1): triangles and segments as convex hulls *)

Inductive plane_obj (R : realFieldType) : Type :=
| PSeg of (R * R) & (R * R)
| PTri of (R * R) & (R * R) & (R * R).

Section Geom.
Variable R : realFieldType.
Local Open Scope ring_scope.

(** A point on the segment [a b]: a convex combination of the two endpoints. *)
Definition in_seg (a b p : R * R) : Prop :=
  exists t : R,
    [/\ 0 <= t, t <= 1,
        p.1 = a.1 + t * (b.1 - a.1) &
        p.2 = a.2 + t * (b.2 - a.2)].

(** A point in the (filled) triangle [a b c]: a convex combination (barycentric
    coordinates) of the three vertices. *)
Definition in_tri (a b c p : R * R) : Prop :=
  exists l1 l2 l3 : R,
    [/\ 0 <= l1, 0 <= l2, 0 <= l3, l1 + l2 + l3 = 1 &
        p.1 = l1 * a.1 + l2 * b.1 + l3 * c.1 /\
        p.2 = l1 * a.2 + l2 * b.2 + l3 * c.2].

Definition in_obj (o : plane_obj R) (p : R * R) : Prop :=
  match o with
  | PSeg a b => in_seg a b p
  | PTri a b c => in_tri a b c p
  end.

End Geom.

(** ================================================================= *)
(** ** Row 1 — Linear hypergraphs with incidence-poset dimension ≤ 3  (OPEN)

    Source: "Conjecture Any linear hypergraph with incidence poset of dimension
    at most 3 is the intersection hypergraph of a family of triangles and
    segments in the plane."

    Carrier: vertices [T : finType], hyperedges [E : {set {set T}}].  "Linear" =
    any two distinct hyperedges share at most one vertex.  The incidence poset is
    [inc_le E] on [T + {set T}] (vertices below the hyperedges containing them).
    "Intersection hypergraph of triangles and segments" = [plane_represents]: a
    point map [pt : T -> R*R] and a region map [obj : {set T} -> plane_obj R] with
    [v ∈ e ⟺ pt v ∈ obj e].  Guard: [E != set0] (non-vacuous geometry). *)

Definition linear_hypergraph (T : finType) (E : {set {set T}}) : Prop :=
  forall e f : {set T}, e \in E -> f \in E -> e != f -> #|e :&: f| <= 1.

(** The incidence poset of [(T,E)] on [T + {set T}]: a vertex [v] is below a
    hyperedge [e ∈ E] iff [v ∈ e]; vertices and hyperedges are otherwise pairwise
    incomparable (each comparable only to itself). *)
Definition inc_le (T : finType) (E : {set {set T}}) : rel (T + {set T}) :=
  fun x y =>
    match x, y with
    | inl v, inl w => v == w
    | inl v, inr e => (e \in E) && (v \in e)
    | inr e, inr f => e == f
    | inr _, inl _ => false
    end.

Definition incidence_poset_dim_le (T : finType) (E : {set {set T}}) (d : nat) : Prop :=
  poset_dim_le (inc_le E) d.

(** The hypergraph is the intersection hypergraph of a family of triangles and
    segments: a points-in-regions incidence representation in the plane [R*R]. *)
Definition plane_represents (R : realFieldType) (T : finType) (E : {set {set T}})
  : Prop :=
  exists (pt : T -> R * R) (obj : {set T} -> plane_obj R),
    forall e : {set T}, e \in E ->
      forall v : T, (v \in e) <-> in_obj (obj e) (pt v).

(** Corpus row: opg:linear_hypergraphs_with_dimension_3
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/linear_hypergraphs_with_dimension_3/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/linear_hypergraphs_with_dimension_3.json
    English statement: (Open Problem Garden, "Linear Hypergraphs with Dimension 3")
      Over every ordered field R, every non-empty linear hypergraph (any two distinct
      hyperedges share at most one vertex) whose incidence poset has order dimension at most 3
      is the intersection hypergraph of a family of triangles and segments in the plane: there
      are a point for each vertex and a triangle or segment for each hyperedge such that a
      vertex lies in a hyperedge exactly when its point lies in that region.
    Definitions: [linear_hypergraph E] - distinct hyperedges meet in at most one vertex (D2str.v);
      [inc_le E] - the incidence order on T + {set T}: a vertex is below a hyperedge of E
      containing it, and vertices and hyperedges are otherwise comparable only to themselves
      (D2str.v); [is_linear_order], [order_extends], [realizer], [poset_dim_le le d] - a
      realizer is a list of linear extensions whose intersection is exactly le, and the order
      dimension is at most d when a realizer of length at most d exists (D2str.v);
      [incidence_poset_dim_le E d] (D2str.v); [plane_obj R] - a segment or a triangle given by
      its 2 or 3 corner points (D2str.v); [in_seg], [in_tri], [in_obj] - membership as a convex
      combination of the corners (D2str.v); [plane_represents R E] - the points-in-regions
      representation above (D2str.v).
    Notes: the incidence poset is taken on the FULL ground type T + {set T}, so subsets that are
      not hyperedges sit as isolated points. Isolated points never change a poset's order
      dimension across the "at most 3" threshold (they are realised by any two or more linear
      extensions), so this is faithful to the textbook incidence-poset dimension. The plane is
      an arbitrary ordered field rather than the reals specifically; triangles and segments are
      filled convex hulls. The guard E != set0 keeps the geometry non-vacuous. Since [rel X] is
      not an eqType, realizer membership is index-based. *)
Definition linear_hypergraphs_with_dimension_3_statement : Prop :=
  forall (R : realFieldType) (T : finType) (E : {set {set T}}),
    E != set0 ->
    linear_hypergraph E ->
    incidence_poset_dim_le E 3 ->
    plane_represents R E.

(** ================================================================= *)
(** ** Row 2 — Geodesic cycles and Tutte's theorem  (OPEN Problem)

    Source: "Problem If G is a 3-connected finite graph, is there an assignment
    of lengths ℓ : E(G) → ℝ⁺ to the edges of G, such that every ℓ-geodesic cycle
    is peripheral?"

    Carrier: [G : sgraph].  [k_connected G 3] = 3-connectivity.  An edge-length
    assignment [ell : G -> G -> R] (any [R : realFieldType]) is positive on edges
    and symmetric ([edge_length]).  A cycle is [ell]-geodesic when between any two
    of its vertices SOME cyclic arc is a shortest (minimal-[ell]-length) walk.  A
    peripheral cycle is induced and non-separating. *)

(** Cyclic edge relation of a vertex sequence [c]: consecutive (cyclically). *)
Definition cyc_edge (G : sgraph) (c : seq G) : rel G :=
  fun x y => ((x, y) \in zip c (rot 1 c)) || ((y, x) \in zip c (rot 1 c)).

(** A walk [u :: p] all of whose steps are cycle edges of [c]. *)
Definition on_cycle_walk (G : sgraph) (c : seq G) (u : G) (p : seq G) : bool :=
  all (fun e => cyc_edge c e.1 e.2) (zip (u :: p) p).

Section Weighted.
Variable R : realFieldType.
Variable G : sgraph.
Implicit Type ell : G -> G -> R.
Local Open Scope ring_scope.

(** [ell]-length of the walk [u :: p] (sum of [ell] over consecutive vertices). *)
Definition wlen ell (u : G) (p : seq G) : R :=
  \sum_(e <- zip (u :: p) p) ell e.1 e.2.

(** A positive, symmetric edge-length assignment ([ℓ : E → ℝ⁺]). *)
Definition edge_length ell : Prop :=
  (forall x y : G, x -- y -> 0 < ell x y) /\
  (forall x y : G, ell x y = ell y x).

(** [p] is a shortest [u]–[v] walk: a [u]–[v] walk of minimal [ell]-length. *)
Definition shortest_walk ell (u v : G) (p : seq G) : Prop :=
  [/\ path (--) u p, last u p = v &
      forall q : seq G, path (--) u q -> last u q = v -> wlen ell u p <= wlen ell u q].

(** An [ell]-geodesic cycle: a cycle such that between any two of its vertices
    some cyclic arc realises the [ell]-distance (is a shortest walk). *)
Definition geodesic_cycle ell (c : seq G) : Prop :=
  ucycle (--) c /\
  forall u v : G, u \in c -> v \in c ->
    exists p : seq G, shortest_walk ell u v p /\ on_cycle_walk c u p.

End Weighted.

(** [k]-connectivity is base's [k_connected] (Whitney form: [k < #|G|] and every
    vertex set of size [< k] leaves [[set: G] :\: S] connected); reused verbatim. *)

(** Induced (chordless) cycle: every G-edge between cycle vertices is a cycle
    edge. *)
Definition induced_cycle (G : sgraph) (c : seq G) : Prop :=
  ucycle (--) c /\
  forall x y : G, x \in c -> y \in c -> x -- y -> cyc_edge c x y.

(** Peripheral cycle: induced and non-separating (its complement is connected). *)
Definition peripheral_cycle (G : sgraph) (c : seq G) : Prop :=
  induced_cycle c /\ connected (~: [set x in c]).

(** Corpus row: opg:geodesic_cycles_and_tuttes_theorem
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/geodesic_cycles_and_tuttes_theorem/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/geodesic_cycles_and_tuttes_theorem.json
    English statement: (Open Problem Garden, "Geodesic cycles and Tutte's Theorem")
      Over every ordered field R, every 3-connected finite graph G admits a positive symmetric
      edge-length assignment ell such that every ell-geodesic cycle of G is peripheral, i.e.
      induced and non-separating.
    Definitions: [cyc_edge c] - two vertices are cyclically consecutive in the list c (D2str.v);
      [on_cycle_walk c u p] - every step of the walk u :: p is a cycle edge of c (D2str.v);
      [wlen ell u p] - the ell-length of the walk u :: p (D2str.v); [edge_length ell] - ell is
      symmetric and strictly positive on edges (D2str.v); [shortest_walk ell u v p] - p is a
      u-v walk of minimal ell-length among all u-v walks (D2str.v); [geodesic_cycle ell c] - c
      is a uniform cycle and between any two of its vertices SOME cyclic arc is a shortest walk
      (D2str.v); [induced_cycle c] - every edge of G between cycle vertices is a cycle edge
      (D2str.v); [peripheral_cycle c] - induced and with connected complement (D2str.v);
      [k_connected G 3] - base's Whitney form: 3 < |V(G)| and deleting fewer than 3 vertices
      keeps the rest connected (GTBase).
    Notes: "ell-geodesic" is the standard isometric-cycle property: between any two cycle vertices
      one of the two arcs realises the ell-distance, the distance being taken over ALL walks of
      G, not only those on the cycle. Lengths live in an arbitrary ordered field rather than
      the positive reals. *)
Definition geodesic_cycles_and_tuttes_theorem_statement : Prop :=
  forall (R : realFieldType) (G : sgraph),
    k_connected G 3 ->
    exists ell : G -> G -> R,
      edge_length ell /\
      (forall c : seq G, geodesic_cycle ell c -> peripheral_cycle c).

(** ================================================================= *)
(** ** Row 3 — Nearly spanning regular subgraphs  (OPEN)

    Source: "Conjecture For every ε > 0 and every positive integer k, there
    exists r₀ = r₀(ε,k) so that every simple r-regular graph G with r ≥ r₀ has a
    k-regular subgraph H with |V(H)| ≥ (1−ε)|V(G)|."

    Carrier: [G : sgraph].  A [k]-regular subgraph [H] is carried by a vertex set
    [S : {set G}] and an edge relation [adj : rel G] (symmetric, irreflexive,
    [adj]-edges are G-edges within [S], every vertex of [S] has [adj]-degree [k]).
    ε–N form: ε = p/q ([0 < p], [0 < q]); the bound [|V(H)| ≥ (1−ε)|V(G)|] is
    [q * |S| ≥ (q − p) * |V(G)|] (nat truncated subtraction handles ε ≥ 1). *)

Definition k_regular_subgraph (G : sgraph) (S : {set G}) (adj : rel G) (k : nat)
  : Prop :=
  [/\ symmetric adj, irreflexive adj,
      (forall x y : G, adj x y -> x -- y),
      (forall x y : G, adj x y -> (x \in S) && (y \in S)) &
      (forall v : G, v \in S -> #|[set u in S | adj v u]| = k)].

(** Corpus row: opg:nearly_spanning_regular_subgraphs
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/nearly_spanning_regular_subgraphs/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/nearly_spanning_regular_subgraphs.json
    English statement: (Open Problem Garden, "Nearly spanning regular subgraphs")
      For every positive rational eps = p/q and every k > 0 there is r0 such that every
      r-regular graph G with r >= r0 has a k-regular subgraph carried by a vertex set S with
      (q - p) * |V(G)| <= q * |S|, i.e. |S| >= (1 - eps) * |V(G)|.
    Definitions: [k_regular_subgraph G S adj k] - adj is a symmetric irreflexive relation whose pairs are
      edges of G with both endpoints in S, and every vertex of S has exactly k adj-neighbours
      in S (D2str.v); [regular G r] - every vertex of G has degree r (GTBase).
    Notes: the subgraph is carried by a vertex set S together with an explicit edge relation adj,
      rather than by an induced subgraph, because a k-regular subgraph need not be induced. eps
      is a ratio of positive naturals; the nat truncated subtraction q - p makes the conclusion
      trivially true when eps >= 1, which matches the intended content. *)
Definition nearly_spanning_regular_subgraphs_statement : Prop :=
  forall (p q k : nat), 0 < p -> 0 < q -> 0 < k ->
    exists r0 : nat,
      forall (r : nat) (G : sgraph), r0 <= r -> regular G r ->
        exists (S : {set G}) (adj : rel G),
          k_regular_subgraph S adj k /\
          ((q - p) * #|[set: G]| <= q * #|S|)%N.

(** ================================================================= *)
(** ** Row 4 — Simultaneous partition of two hypergraphs  (OPEN Problem)

    Source: "Problem Let H₁ and H₂ be two r-uniform hypergraphs on the same
    vertex set V.  Does there always exist a partition of V into r classes
    V₁,…,V_r such that for both i = 1,2, at least r!·m_i/r^r − o(m_i) hyperedges
    of H_i meet each of the classes V₁,…,V_r?"

    Carrier: vertices [T : finType], two r-uniform families [E1 E2], a part map
    [part : T -> 'I_r].  A hyperedge "meets each class" = is [rainbow] (hits every
    part).  m_i = [#|E_i|].  ε–N (eventual) form for the [−o(m_i)] slack: for each
    [r > 0] and ε = a/b > 0 there is a threshold [N] beyond which (for both i) the
    rainbow count satisfies [rainbow_i ≥ r!·m_i/r^r − ε·m_i], cross-multiplied by
    [b·r^r] and stated with [+] (no nat subtraction):
      [b·r^r·rainbow_i + a·r^r·m_i ≥ b·r!·m_i]. *)

Definition uniform_hypergraph (T : finType) (E : {set {set T}}) (r : nat) : Prop :=
  forall e : {set T}, e \in E -> #|e| = r.

(** A hyperedge meets every one of the [r] parts (a rainbow / transversal edge). *)
Definition rainbow (T : finType) (r : nat) (part : T -> 'I_r) (e : {set T}) : bool :=
  [forall j : 'I_r, [exists v, (v \in e) && (part v == j)]].

(** Corpus row: opg:simultaneous_partition_of_hypergraphs
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/simultaneous_partition_of_hypergraphs/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/simultaneous_partition_of_hypergraphs.json
    English statement: (Open Problem Garden, "Simultaneous partition of hypergraphs")
      For every r > 0 and every positive rational eps = a/b there is a threshold N such that
      for any two r-uniform hypergraphs E1, E2 on the same finite vertex set, each with at
      least N hyperedges, there is a partition of the vertices into r classes for which, for
      both i = 1 and i = 2, the number of hyperedges of E_i meeting every class satisfies
      b * r^r * rainbow_i + a * r^r * m_i >= b * r! * m_i, i.e.
      rainbow_i >= r! * m_i / r^r - eps * m_i.
    Definitions: [uniform_hypergraph E r] - every hyperedge has exactly r vertices (D2str.v);
      [rainbow r part e] - the hyperedge e contains a vertex of every one of the r parts
      (D2str.v); [factorial] - MathComp factorial.
    Notes: the o(m_i) slack of the source is rendered in eventual epsilon-N form with the threshold
      N depending only on r and eps, uniform in the vertex type and the two hypergraphs. The
      inequality is cross-multiplied by b * r^r and the subtraction is moved to the other side,
      so no nat subtraction occurs. A "partition into r classes" is a total map to 'I_r;
      classes are allowed to be empty, in which case no hyperedge is rainbow. *)
Definition simultaneous_partition_of_hypergraphs_statement : Prop :=
  forall (r a b : nat), 0 < r -> 0 < a -> 0 < b ->
    exists N : nat,
      forall (T : finType) (E1 E2 : {set {set T}}),
        uniform_hypergraph E1 r -> uniform_hypergraph E2 r ->
        N <= #|E1| -> N <= #|E2| ->
        exists part : T -> 'I_r,
          (b * (r ^ r) * #|[set e in E1 | rainbow part e]| + a * (r ^ r) * #|E1|
             >= b * (factorial r) * #|E1|)%N /\
          (b * (r ^ r) * #|[set e in E2 | rainbow part e]| + a * (r ^ r) * #|E2|
             >= b * (factorial r) * #|E2|)%N.

(** ================================================================= *)
(** ** Row 5 — Covering powers of cycles with equivalence subgraphs  (OPEN)

    Source: "Conjecture Given k and n, the graph C_n^k has equivalence covering
    number Ω(k)."

    Carrier: the power graph [graph_power (cycle_graph n) k] (an [sgraph]; reuses
    base's [graph_power]).  An equivalence subgraph is an equivalence relation
    whose nontrivial pairs are edges (a disjoint union of cliques sitting inside
    G); a cover is a family of them covering every edge; the equivalence covering
    number eq(G) is the minimum cover size.  Ω(k) = a uniform linear lower bound
    in the genuine asymptotic regime (n large RELATIVE to k): constants
    [cnum,cden > 0], a growth threshold [g : nat -> nat] and a base point [k0]
    with [cnum·k ≤ cden·eq] for all [k ≥ k0] and all [n ≥ g k].  The free [g]
    captures "for n sufficiently large depending on k" — a bare guard like
    [2k < n] (or even [2k+1 < n]) is NOT faithful, since near-complete powers
    such as [C_{2k+1}^k = K_{2k+1}] (eq = 1) or the cocktail-party
    [C_{2k+2}^k] (eq = O(log k)) violate any linear bound; [g] must be allowed to
    grow past them. *)

(** The cycle [C_n] on ['I_n]: [x] and [y] adjacent iff cyclically consecutive.
    [@MOVE-to-base]: generic cycle family, migrate when a 2nd area needs it. *)
(** [cyc_rel]/[cycle_graph] now come from [GTBase.base] (cross-area finite
    invariant), imported via [base]; base's [cyc_rel] is the same relation. *)

(** An equivalence subgraph of [G]: an equivalence relation all of whose
    nontrivial related pairs are edges of [G]. *)
Definition equivalence_graph (G : sgraph) (e : rel G) : Prop :=
  [/\ reflexive e, symmetric e, transitive e &
      forall x y : G, x != y -> e x y -> x -- y].

(** [es] is an equivalence cover of [G]: each entry is an equivalence subgraph and
    every edge of [G] is covered by some entry. *)
Definition eq_covers (G : sgraph) (es : seq (rel G)) : Prop :=
  (forall i, i < size es -> equivalence_graph (nth (fun _ _ => false) es i)) /\
  (forall x y : G, x -- y ->
     exists2 i, i < size es & (nth (fun _ _ => false) es i) x y).

(** [m] is the equivalence covering number eq(G): the minimum cover size. *)
Definition is_eq_cover_number (G : sgraph) (m : nat) : Prop :=
  (exists es : seq (rel G), eq_covers es /\ size es = m) /\
  (forall es : seq (rel G), eq_covers es -> m <= size es).

(** Corpus row: opg:covering_powers_of_cycles_with_equivalence_subgraphs
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/covering_powers_of_cycles_with_equivalence_subgraphs/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/covering_powers_of_cycles_with_equivalence_subgraphs.json
    English statement: (Open Problem Garden, "Covering powers of cycles with equivalence subgraphs")
      There are positive naturals cnum, cden, a growth threshold g and a base point k0 such
      that for every k >= k0, every n >= g k and every m that is the equivalence covering number
      of the k-th power of the n-cycle, cnum * k <= cden * m; that is, eq(C_n^k) is Omega(k).
    Definitions: [equivalence_graph G e] - e is an equivalence relation all of whose non-trivial related
      pairs are edges of G, i.e. a disjoint union of cliques of G (D2str.v); [eq_covers G es] -
      every entry of the list es is such an equivalence subgraph and every edge of G is
      related by some entry (D2str.v); [is_eq_cover_number G m] - m is the minimum length of
      such a cover (D2str.v); [graph_power G k] - the distance power, x and y adjacent when
      they are at distance at most k (GTBase); [cycle_graph n] - C_n on 'I_n (GTBase).
    Notes: this row is recorded as PARTIAL. Omega(k) is an asymptotic-in-n lower bound, so the
      n-regime is an EXISTENTIALLY quantified growth threshold g with n >= g k, NOT a bare
      guard such as 2k < n: near-complete powers like C_{2k+1}^k = K_{2k+1} (covering number 1)
      or the cocktail-party graph C_{2k+2}^k (covering number O(log k)) violate any linear
      bound, so g must be allowed to grow past them. The constant is the ratio cnum/cden.
      Because g is existentially quantified with no growth constraint, the statement is
      formally weaker than the source conjecture (ledger). *)
Definition covering_powers_of_cycles_with_equivalence_subgraphs_statement : Prop :=
  exists cnum cden : nat,
    [/\ 0 < cnum, 0 < cden &
        exists (g : nat -> nat) (k0 : nat),
          forall (k n m : nat),
            k0 <= k -> g k <= n ->
            is_eq_cover_number (graph_power (cycle_graph n) k) m ->
            (cnum * k <= cden * m)%N].
