(** * Hom.conjectures.U3 — milestone U3 (namespace Hom, plan v4)

    Statement-only formalizations (axiom-free: no Conjecture/Axiom/Parameter/
    Admitted) of ten open / solved / disproved problems in graph
    HOMOMORPHISM theory: tensor-product chromatic number (Hedetniemi),
    homomorphisms to odd cycles, cores of Cayley / strongly-regular graphs,
    endomorphism counts of trees, longest cycles/paths, fractional powers and
    the weak pentagon problem.

    CARRIER TYPES are chosen per row from the source statement: most rows live
    over [sgraph] (simple finite graphs); the Cayley-graph row lives over the
    finite group [{ffun 'I_k -> M}] (the [k]-th power of an abelian group [M]).

    Imports.  [GTBase.base] is the SOLE graph import: it re-exports the
    coq-graph-theory undirected vocabulary ([sgraph], [x -- y], [N(x)], [χ],
    [ω], [α], [clique], [connected], ['K_n], ['K_n,m], [≃]/[diso], [ucycle],
    [path]) AND owns the cross-area primitives reused here verbatim:
    [tensor_product] (×, the product Hedetniemi is about), [homs_to]/[is_hom]
    (graph homomorphism), [is_core] (graph core), [girth_geq], [regular] (whence
    cubic = [regular _ 3]), [common_nbr], [Delta] (Δ).  [mathcomp fingroup] is
    additionally imported for the abelian-group / Cayley-graph row only (it is
    NOT graph vocabulary, so it does not duplicate base's surface).

    AREA-SPECIFIC new primitives introduced below (none belongs in base yet —
    each is specific to homomorphism statements): [cycle_graph]/[C5]
    (odd-cycle targets), [path_graph], [star_graph], [bipartite_rel],
    [triangle_free], [k_connected], [longest_cycle], [chord], [is_path],
    [longest_path], [hom_ffun]/[endo_count], [hom_equiv], [strongly_regular],
    [pcayley]/[pconn_set].  [graph_power]/[subdivision]/[frac_power] are the
    pure colouring-free [sgraph] constructions promoted from chromatic-theory/U1
    (tagged [@MOVE-to-base]: base candidates once a 2nd area needs them). *)

From GTBase Require Export base.
From mathcomp Require Import fingroup.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Area constructions: cycle / path / star graphs *)

(** The [n]-vertex cycle graph [C_n] on ['I_n]: distinct [i],[j] are adjacent
    iff one is the cyclic successor of the other (mod [n]).  The [i != j] guard
    makes the relation irreflexive for every [n] (including the degenerate
    [n ≤ 2]); for [n ≥ 3] this is the genuine cycle.  [C5] = [cycle_graph 5]
    is Hedetniemi/pentagon's target; [cycle_graph (2*k+1)] is the odd cycle
    [C_{2k+1}]. *)
(** [cyc_rel]/[cycle_graph] now live in [GTBase.base] (promoted as a cross-area
    finite invariant, reused by extremal-theory); imported via [base] above. *)

Definition C5 : sgraph := cycle_graph 5.

(** The [n]-vertex path graph [P_n] on ['I_n]: [i],[j] adjacent iff their
    indices are consecutive integers (no modular wrap, so it is a path, not a
    cycle). *)
Section PathGraph.
Variable n : nat.
Definition pth_rel (i j : 'I_n) : bool :=
  ((val i).+1 == val j) || ((val j).+1 == val i).
Lemma pth_sym : symmetric pth_rel.
Proof. by move=> i j; rewrite /pth_rel orbC. Qed.
Lemma pth_irrefl : irreflexive pth_rel.
Proof. by move=> i; rewrite /pth_rel orbb (gtn_eqF (ltnSn _)). Qed.
Definition path_graph : sgraph := SGraph pth_sym pth_irrefl.
End PathGraph.

(** The [n]-vertex star graph [K_{1,n-1}] (one centre, [n-1] leaves) — a tree.
    Uses base's re-exported ['K_1, m] notation ([= KB 1 m]) rather than the bare
    [KB] constant, to stay on the documented base vocabulary surface. *)
Definition star_graph (n : nat) : sgraph := 'K_1, n.-1.

(** Corpus row: opg:hedetniemis_conjecture
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/hedetniemis_conjecture/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/hedetniemis_conjecture.json
    English statement: (Open Problem Garden, "Hedetniemi's Conjecture")
      For all finite simple graphs G and H, the chromatic number of the tensor
      (direct, categorical) product of G and H equals the smaller of the
      chromatic numbers of G and of H.
    Definitions: [tensor_product G H] - the tensor/direct/categorical product:
      vertices are pairs, (p1,p2) is adjacent to (q1,q2) iff p1 -- q1 in G and
      p2 -- q2 in H (base/theories/base.v); the chromatic number is the library
      [chi] of coq-graph-theory's coloring.v, applied here to [set: _], the full
      vertex set.
    Notes: DISPROVED by Shitov (2019): there are finite G, H with chi(G x H)
      strictly below min(chi G, chi H).  What is stated here is the historical
      EQUALITY (statement only); refuting it is optional applications/ work. *)
Definition hedetniemis_statement : Prop :=
  forall G H : sgraph,
    χ([set: tensor_product G H]) = minn (χ([set: G])) (χ([set: H])).

(** Corpus row: opg:pentagon_problem
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/pentagon_problem/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/pentagon_problem.json
    English statement: (Open Problem Garden, "Pentagon problem")
      There is a girth threshold g such that every 3-regular graph all of whose
      cycles have length at least g admits a homomorphism to the 5-cycle C5.
    Definitions: [C5] - the 5-cycle, [cycle_graph 5] (this file, U3.v);
      [cycle_graph n] - the cycle C_n on 'I_n, i adjacent to j iff one index is
      the cyclic successor of the other (base/theories/base.v); [regular G 3] -
      every vertex has exactly three neighbours (base.v); [girth_geq G g] -
      every genuine cycle (a ucycle of size > 2) has length at least g (base.v);
      [homs_to G H] - there exists an adjacency-preserving map from G to H
      (base.v).
    Notes: the source is a Question ("is it true that for large enough g ... ?")
      and the body asserts the affirmative, with the quantifier order
      "exists g, forall G" that "for large enough g" calls for.  Acyclic cubic
      graphs satisfy [girth_geq] for every g, so they are covered too. *)
Definition pentagon_statement : Prop :=
  exists g : nat, forall G : sgraph,
    regular G 3 -> girth_geq G g -> homs_to G C5.

(** ** Row 3 — Chords of longest cycles
    OPEN.

    Source: "If G is a 3-connected graph, every longest cycle in G has a chord."

    [k_connected G k]: more than [k] vertices, and deleting any set of fewer
    than [k] vertices leaves the rest connected (standard vertex
    [k]-connectivity, stated self-containedly via [connected (~: S)]).
    [longest_cycle G c]: [c] is a genuine cycle ([ucycle], [2 < size]) of
    maximum length.  [chord G c]: an edge [x -- y] joining two cycle vertices
    that are NOT cyclically consecutive in [c] — consecutivity is exactly
    membership in [zip c (rot 1 c)], the list of cycle edges. *)
(* [k_connected] now from graph-theory-base (uses [set: G] :\: S = ~: S). *)

Definition longest_cycle (G : sgraph) (c : seq G) : Prop :=
  [/\ ucycle (--) c, 2 < size c &
      forall c' : seq G, ucycle (--) c' -> size c' <= size c].

Definition chord (G : sgraph) (c : seq G) : Prop :=
  exists x y : G,
    [/\ x \in c, y \in c, x -- y,
        (x, y) \notin zip c (rot 1 c) & (y, x) \notin zip c (rot 1 c)].

(** Corpus row: opg:chords_of_longest_cycles
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/chords_of_longest_cycles/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/chords_of_longest_cycles.json
    English statement: (Open Problem Garden, "Chords of longest cycles")
      In every 3-connected graph G, every longest cycle has a chord: if the
      vertex sequence c is a cycle of G of maximum length, then some two
      vertices x, y lying on c are adjacent in G without being consecutive
      on c.
    Definitions: [k_connected G 3] - G has more than three vertices and deleting
      any set of fewer than three vertices leaves the rest connected
      (base/theories/base.v); [longest_cycle c] - c is a ucycle of size greater
      than two whose size is maximum among all ucycles of G (this file, U3.v);
      [chord c] - two vertices of c that are adjacent in G and form neither of
      the ordered pairs listed by [zip c (rot 1 c)], the list of the cycle's own
      consecutive pairs (this file, U3.v).
    Notes: cycles are [seq] of vertices with MathComp's [ucycle] (closed walk,
      no repeated vertex); the size > 2 guard in [longest_cycle] discards the
      degenerate empty and two-element ucycle artefacts, so in a forest the
      hypothesis is unsatisfiable and the row is vacuous there, as intended. *)
Definition chords_of_longest_cycles_statement : Prop :=
  forall G : sgraph, k_connected G 3 ->
    forall c : seq G, longest_cycle c -> chord c.

(** ** Row 4 — Cores of Cayley graphs
    OPEN.

    Source: "Let M be an abelian group.  Is the core of a Cayley graph (on
    some power of M) a Cayley graph (on some power of M)?"

    CARRIER: the [k]-th power of [M] is the finite type [{ffun 'I_k -> M}],
    carrying the pointwise group structure of [M].  Its Cayley graph with
    connection set [S] ([pcayley S]) makes distinct [f],[g] adjacent iff the
    pointwise "difference" [pdiff f g = (i ↦ f i · (g i)⁻¹) ∈ S] (symmetrised
    so the [sgraph] laws hold for any [S]; the genuine Cayley graph is
    recovered when [S] is a [pconn_set] — identity-free, inverse-closed).  We
    use [M]'s group operations directly (M : finGroupType), which sidesteps
    needing a packed finGroupType instance for [{ffun 'I_k -> M}].  "The core of
    G is a Cayley graph on a power of M" is stated without a core OPERATOR as:
    there is a power [m] and connection set [S'] whose Cayley graph is a core
    ([is_core]) and is homomorphically equivalent to G ([hom_equiv]) — i.e. it
    IS the core of G up to isomorphism. *)
Section Cayley.
Variables (M : finGroupType) (k : nat).
Implicit Types (f g : {ffun 'I_k -> M}) (S : {set {ffun 'I_k -> M}}).

(** Pointwise group structure on the power [M^k = {ffun 'I_k -> M}]. *)
Definition pone : {ffun 'I_k -> M} := [ffun _ => 1%g].
Definition pinv f : {ffun 'I_k -> M} := [ffun i => (f i)^-1%g].
Definition pdiff f g : {ffun 'I_k -> M} := [ffun i => (f i * (g i)^-1)%g].

Definition pcayley_rel (S : {set {ffun 'I_k -> M}}) : rel {ffun 'I_k -> M} :=
  fun f g => (f != g) && ((pdiff f g \in S) || (pdiff g f \in S)).
Lemma pcayley_sym S : symmetric (pcayley_rel S).
Proof. by move=> f g; rewrite /pcayley_rel eq_sym orbC. Qed.
Lemma pcayley_irrefl S : irreflexive (pcayley_rel S).
Proof. by move=> f; rewrite /pcayley_rel eqxx. Qed.
Definition pcayley S : sgraph := SGraph (pcayley_sym S) (pcayley_irrefl S).

(** A valid Cayley connection set on the power: identity-free, inverse-closed. *)
Definition pconn_set S : Prop :=
  (pone \notin S) /\ (forall f, f \in S -> pinv f \in S).
End Cayley.

(** Homomorphic equivalence: homomorphisms both ways.  A generic cross-area
    companion to base's [homs_to]/[is_core], already reused by Rows 4 and 6 here
    ([@MOVE-to-base]: migrate to base alongside [homs_to]/[is_core] once a 2nd
    area needs it, so it is never redefined). *)
Definition hom_equiv (G H : sgraph) : Prop := homs_to G H /\ homs_to H G.

(** Corpus row: opg:cores_of_cayley_graphs
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/cores_of_cayley_graphs/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/cores_of_cayley_graphs.json
    English statement: (Open Problem Garden, "Cores of Cayley graphs")
      For every finite abelian group M, every exponent k and every admissible
      connection set S inside the k-th power of M, the core of the Cayley graph
      of S is again a Cayley graph on a power of M: there are an exponent m and
      an admissible connection set S' inside the m-th power of M such that the
      Cayley graph of S' is a core and is homomorphically equivalent to the
      Cayley graph of S.
    Definitions: [pcayley S] - the Cayley graph on the power {ffun 'I_k -> M},
      distinct f, g adjacent iff the pointwise quotient of one by the other lies
      in S (symmetrised, this file, U3.v); [pconn_set S] - S is an admissible
      connection set: identity-free and closed under pointwise inverse (U3.v);
      [is_core G] - every endomorphism of G is bijective
      (base/theories/base.v); [hom_equiv G H] - homomorphisms exist in both
      directions (U3.v).
    Notes: there is no core OPERATOR in the development, so "the core of G is a
      Cayley graph" is rendered as "some Cayley graph on a power of M is a core
      and is homomorphically equivalent to G"; for finite graphs the core is
      unique up to isomorphism, so this is the intended reading.  The group is a
      [finGroupType], i.e. FINITE, where the source says only "abelian group";
      the power M^k is the finite type {ffun 'I_k -> M} carrying M's pointwise
      operations rather than a packed group instance. *)
Definition cores_of_cayley_graphs_statement : Prop :=
  forall M : finGroupType, abelian [set: M] ->
  forall (k : nat) (S : {set {ffun 'I_k -> M}}), pconn_set S ->
    exists (m : nat) (S' : {set {ffun 'I_m -> M}}),
      [/\ pconn_set S', is_core (pcayley S') & hom_equiv (pcayley S) (pcayley S')].

(** Corpus row: opg:chromatic_number_of_frac_3_3_power_of_graph
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/chromatic_number_of_frac_3_3_power_of_graph/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/chromatic_number_of_frac_3_3_power_of_graph.json
    English statement: (Open Problem Garden, "Chromatic number of 3/3-power of
      graph") For every graph G whose maximum degree is at least two, the
      chromatic number of G^(3/3) - the third power of the 3-subdivision of G -
      is at most twice the maximum degree of G plus one.
    Definitions: [frac_power G m n] - G^(m/n), defined as
      [graph_power (subdivision G n) m] (base/theories/base.v);
      [subdivision G n] - each edge replaced by a path with n-1 internal
      vertices (base.v); [graph_power G m] - distinct vertices adjacent iff one
      is within distance m of the other (base.v); [Delta G] - maximum degree
      (base.v); the chromatic number is the library [chi] applied to [set: _].
    Notes: [subdivision G n] degenerates for n <= 1; here n = 3, inside the
      meaningful regime.  The hypothesis Delta(G) >= 2 is the source's. *)

Definition chromatic_number_of_frac_3_3_power_of_graph_statement : Prop :=
  forall G : sgraph, 2 <= Delta G ->
    χ([set: frac_power G 3 3]) <= 2 * Delta G + 1.

(** ** Row 6 — Cores of strongly-regular graphs
    OPEN.

    Source: "Does every strongly regular graph have either itself or a complete
    graph as a core?"

    [strongly_regular G]: there are parameters [k],[l],[m] with [G] [k]-regular,
    every adjacent pair sharing [l] common neighbours and every non-adjacent
    distinct pair sharing [m].  The conjecture: the core of [G] is either [G]
    itself ([is_core G]) or a complete graph (G is hom-equivalent to ['K_n],
    whose core is ['K_n]). *)
Definition srg (G : sgraph) (k l m : nat) : Prop :=
  [/\ regular G k,
      (forall x y : G, x -- y -> #|common_nbr x y| = l)
    & (forall x y : G, x != y -> ~~ x -- y -> #|common_nbr x y| = m)].

Definition strongly_regular (G : sgraph) : Prop :=
  exists k l m : nat, srg G k l m.

(** Corpus row: opg:cores_of_strongly_regular_graphs
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/cores_of_strongly_regular_graphs/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/cores_of_strongly_regular_graphs.json
    English statement: (Open Problem Garden, "Cores of strongly regular graphs")
      Every strongly regular graph G - one for which there are parameters k, l,
      m with G k-regular, any two adjacent vertices having exactly l common
      neighbours and any two distinct non-adjacent vertices exactly m common
      neighbours - either is its own core or is homomorphically equivalent to a
      complete graph.
    Definitions: [srg G k l m] and [strongly_regular G] - the parameter
      conditions above, with the parameters existentially quantified (this file,
      U3.v); [is_core G] - every endomorphism of G is bijective
      (base/theories/base.v); [hom_equiv G H] - homomorphisms both ways (U3.v);
      ['K_n] - the complete graph (coq-graph-theory sgraph.v); [regular],
      [common_nbr] (base.v).
    Notes: as in the Cayley row there is no core operator, so "has a complete
      graph as core" is rendered as "is homomorphically equivalent to some
      'K_n", which is equivalent since 'K_n is its own core.  The source is a
      Question and the body asserts the affirmative. *)
Definition cores_of_strongly_regular_graphs_statement : Prop :=
  forall G : sgraph, strongly_regular G ->
    is_core G \/ exists n : nat, hom_equiv G 'K_n.

(** Corpus row: opg:mapping_planar_graphs_to_odd_cycles
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/mapping_planar_graphs_to_odd_cycles/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/mapping_planar_graphs_to_odd_cycles.json
    English statement: (Open Problem Garden, "Mapping planar graphs to odd
      cycles") For every graph G and every k >= 1, if G is planar and every
      cycle of G has length at least 4k, then G admits a homomorphism to the odd
      cycle on 2k+1 vertices.
    Definitions: [wagner_planar G] - G has neither K5 nor K3,3 as a minor, which
      by Wagner's theorem is exactly planarity (base/theories/base.v; used
      opaquely here, minor is not imported); [girth_geq G (4*k)] - every genuine
      cycle has length at least 4k (base.v); [cycle_graph (2*k+1)] - the odd
      cycle C_(2k+1) (base.v); [homs_to] (base.v).
    Notes: the guard 0 < k is a modelling addition; for k = 0 the target would
      be the one-vertex loopless graph, to which no graph with an edge maps, so
      the source implicitly assumes k >= 1.  [wagner_planar] captures planarity
      but no embedding, faces or genus; this row needs none.  This row states
      the same mathematics as the v2 studies row Jaeger's conjecture, formalised
      separately in X22.v. *)
Definition mapping_planar_graphs_to_odd_cycles_statement : Prop :=
  forall (G : sgraph) (k : nat),
    0 < k -> wagner_planar G -> girth_geq G (4 * k) ->
    homs_to G (cycle_graph (2 * k + 1)).

(** ** Row 8 — Three longest paths share a vertex
    OPEN.

    Source: "Do any three longest paths in a connected graph have a vertex in
    common?"

    A path is a duplicate-free walk [is_path s] ([uniq] + consecutive
    adjacency); [longest_path s] is one of maximum length.  The [0 < #|G|]
    guard rules out the empty graph (whose only path is [[::]], for which "a
    common vertex" is vacuously impossible). *)
Definition is_path (G : sgraph) (s : seq G) : bool :=
  uniq s && (if s is x :: p then path (--) x p else true).

Definition longest_path (G : sgraph) (s : seq G) : Prop :=
  is_path s /\ forall t : seq G, is_path t -> size t <= size s.

(** Corpus row: opg:do_any_three_longest_paths_in_a_connected_graph_have_a_vertex_in_common
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/do_any_three_longest_paths_in_a_connected_graph_have_a_vertex_in_common/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/do_any_three_longest_paths_in_a_connected_graph_have_a_vertex_in_common.json
    English statement: (Open Problem Garden, "Do any three longest paths in a
      connected graph have a vertex in common?") For every nonempty connected
      graph G and any three longest paths of G, some vertex lies on all three.
      A path is a duplicate-free vertex sequence whose consecutive vertices are
      adjacent, and it is longest when no path of G is longer.
    Definitions: [is_path s] - [uniq s] together with consecutive adjacency
      along s (this file, U3.v); [longest_path s] - s is a path of maximum size
      (U3.v); [connected [set: G]] - connectedness of the full vertex set
      (coq-graph-theory connectivity.v).
    Notes: the guard 0 < #|G| excludes the empty graph, whose only path is the
      empty sequence and where no common vertex can exist.  The source is
      phrased as a question; the body asserts the affirmative answer. *)
Definition do_any_three_longest_paths_in_a_connected_graph_have_statement : Prop :=
  forall G : sgraph, 0 < #|G| -> connected [set: G] ->
    forall s1 s2 s3 : seq G,
      longest_path s1 -> longest_path s2 -> longest_path s3 ->
      exists v : G, [/\ v \in s1, v \in s2 & v \in s3].

(** ** Row 9 — Extremal number of tree endomorphisms
    OPEN.

    Source: "An endomorphism of a graph is an edge-preserving self-map of the
    vertex set.  Among all n-vertex trees, the star has the most endomorphisms
    and the path has the least."

    [hom_ffun f]: [f : {ffun G -> G}] is an endomorphism; [endo_count G] counts
    them.  Compared against the [n]-vertex [path_graph] (least) and
    [star_graph] (most).

    [hom_ffun] is the BOOLEAN REFLECTION of base's Prop-valued [is_hom] (a
    boolean predicate is required to index the cardinal [#|[set f | ...]|],
    which the Prop-valued [is_hom] cannot serve directly); the two notions
    provably coincide — see [hom_ffunP] in grounding_U3.v
    ([reflect (is_hom f) (hom_ffun f)]).  It is therefore a reflection of
    base's homomorphism vocabulary, not an independent redefinition. *)
Definition hom_ffun (G : sgraph) (f : {ffun G -> G}) : bool :=
  [forall x, forall y, (x -- y) ==> (f x -- f y)].

Definition endo_count (G : sgraph) : nat :=
  #|[set f : {ffun G -> G} | hom_ffun f]|.

(** Corpus row: opg:extremal_problem_on_the_number_of_tree_endomorphism
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/extremal_problem_on_the_number_of_tree_endomorphism/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/extremal_problem_on_the_number_of_tree_endomorphism.json
    English statement: (Open Problem Garden, "Extremal problem on the number of
      tree endomorphism") For every n >= 1 and every tree T on exactly n
      vertices, the n-vertex path has at most as many endomorphisms as T, and T
      has at most as many endomorphisms as the n-vertex star.  An endomorphism
      is a self-map of the vertex set sending adjacent vertices to adjacent
      vertices.
    Definitions: [hom_ffun f] - the BOOLEAN reflection of base's Prop-valued
      [is_hom] for a finite function f : {ffun G -> G} (this file, U3.v; the two
      coincide, see [hom_ffunP] in grounding_U3.v); [endo_count G] - the number
      of such f (U3.v); [path_graph n] - the path P_n on 'I_n, indices adjacent
      iff consecutive with no wrap-around (U3.v); [star_graph n] - the star
      ['K_1, n.-1] (U3.v); [is_tree [set: T]] - T is connected and acyclic
      (coq-graph-theory connectivity.v).
    Notes: the boolean reflection is needed because the cardinal [#|[set f |
      ...]|] must be indexed by a boolean predicate; it is a reflection of
      base's homomorphism vocabulary, not an independent notion.  The guard
      0 < n excludes the empty tree. *)
Definition extremal_problem_on_the_number_of_tree_endomorphism_statement : Prop :=
  forall (n : nat) (T : sgraph),
    0 < n -> is_tree [set: T] -> #|T| = n ->
    (endo_count (path_graph n) <= endo_count T)
      /\ (endo_count T <= endo_count (star_graph n)).

(** ** Row 10 — The weak pentagon problem
    OPEN.

    Source: "If G is a cubic graph not containing a triangle, then the edges of
    G can be coloured by five colours so that the complement of every colour
    class is bipartite."

    [triangle_free]: no three mutually adjacent vertices.  An edge 5-colouring
    is a symmetric [col : G -> G -> 'I_5]; the complement of colour class [c] is
    the relation [x -- y && col x y != c], required [bipartite_rel] (admits a
    2-colouring [G -> bool] separating its edges). *)
(* [triangle_free] now from graph-theory-base (identical definition). *)

Definition bipartite_rel (G : sgraph) (r : rel G) : Prop :=
  exists f : G -> bool, forall x y : G, r x y -> f x != f y.

(** Corpus row: opg:weak_pentagon_problem
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/weak_pentagon_problem/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/weak_pentagon_problem.json
    English statement: (Open Problem Garden, "Weak pentagon problem")
      For every cubic triangle-free graph G there is a symmetric assignment of
      one of five colours to every pair of vertices such that, for each colour
      c, the relation "x is adjacent to y and the pair {x,y} does not have
      colour c" - the complement of colour class c - is bipartite, i.e. admits a
      two-valued vertex labelling giving different labels to the two ends of
      every such pair.
    Definitions: [regular G 3] - cubic (base/theories/base.v);
      [triangle_free G] - no three mutually adjacent vertices (base.v);
      [bipartite_rel G r] - there is f : G -> bool with f x != f y whenever
      r x y (this file, U3.v; the relation-level form of base's [bipartite]).
    Notes: an edge 5-colouring is rendered as a symmetric function
      [col : G -> G -> 'I_5] on ORDERED pairs; its values on non-adjacent pairs
      and on the diagonal are unconstrained and irrelevant, since the colour is
      only ever read under the guard x -- y. *)
Definition weak_pentagon_statement : Prop :=
  forall G : sgraph, regular G 3 -> triangle_free G ->
    exists col : G -> G -> 'I_5,
      (forall x y : G, col x y = col y x) /\
      forall c : 'I_5,
        @bipartite_rel G (fun x y => (x -- y) && (col x y != c)).
