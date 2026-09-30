(** * Chromatic.conjectures.U1 — milestone U1 (namespace Chromatic, plan v4)

    Statement-only formalizations (axiom-free: no Conjecture/Axiom/Parameter/
    Admitted) of nine open/partial/solved problems on graph colouring.

    PRE-G3 MODE: [graph-theory-base] is not a live library yet (the repo's
    [base/] directory holds only a README scaffold, no [.v] files), so the CORE
    undirected vocabulary is imported DIRECTLY from coq-graph-theory here.
    Cross-area primitives that should MOVE to graph-theory-base once G3 lands
    are tagged [@MOVE-to-base] below; we make no claim of base reuse yet.

    CORE API used (verified to load on switch `digraph`, Rocq 9.1.1 +
    coq-graph-theory):
      - [G : sgraph]; [x -- y] adjacency; [N(x)] open neighbourhood ({set G});
      - [χ(A)] = [chi_mem (mem A)] : subset-relative chromatic number (nat),
        whole-graph value [χ([set: G])]; the induced subgraph on [A] is the
        carrier, so removing vertices is [χ(A :\: S)];
      - [ω(A)] = [omega_mem (mem A)] : subset-relative clique number (nat);
      - [clique A] : Prop; [connected A] : Prop; ['K_n] = [complete n] : sgraph;
      - [F ≃ G] = [diso F G] : Type (isomorphism data — wrapped in [inhabited]
        to land in Prop);
      - [ucycle (--) c] / [ucycleb (--) c] : (boolean) cycle predicate on
        [c : seq G] (a cycle = closed walk with distinct vertices). *)

(** G3: cross-area primitives now come from graph-theory-base (GTBase.base), which also
    re-exports the coq-graph-theory undirected vocabulary (sgraph, --, N, χ, ω, clique,
    connected, 'K_n, ≃, ucycle).  The Δ / ceil_div / common_nbr / regular / girth_geq
    definitions formerly inlined here (tagged @MOVE-to-base) were moved verbatim to base/.
    Re-EXPORTED so files importing U1 (grounding_U1, implications_U1) get the base vocabulary. *)
From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Row 1 — Double-critical graph conjecture
    PARTIAL (verified for k ≤ 5; open for k ≥ 6).

    Source: "A connected simple graph G is double-critical if removing any pair
    of adjacent vertices lowers the chromatic number by two.  Conjecture: K_n
    is the only n-chromatic double-critical graph."

    New AREA primitive: [double_critical]. *)
Definition double_critical (G : sgraph) : Prop :=
  forall x y : G, x -- y -> χ([set: G] :\: [set x; y]) + 2 = χ([set: G]).

(** Corpus row: opg:double_critical_graph_conjecture
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/double_critical_graph_conjecture/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/double_critical_graph_conjecture.json
    English statement: (Erdos and Lovasz 1966; Open Problem Garden, "Double-critical graph conjecture")
      For every finite simple graph G with at least one vertex whose vertex set is connected and
      which is double-critical, and for every n, if the chromatic number of G equals n then G is
      isomorphic to the complete graph on n vertices.
    Definitions: [double_critical G] - for every edge xy of G, deleting both endpoints drops the
      chromatic number by exactly two, written chi(V(G) minus {x,y}) + 2 = chi(V(G)) (this file);
      everything else is coq-graph-theory / GTBase vocabulary, chi(A) being the chromatic number of
      the subgraph induced on A, ['K_n] the complete graph and [G ~ H] graph isomorphism.
    Notes: The isomorphism [G ~ 'K_n] is isomorphism DATA, a Type, so it is wrapped in [inhabited]
      to land in Prop. Double-criticality is written in addition form to avoid truncated nat
      subtraction. The nonemptiness guard [0 < #|G|] is an addition to the corpus text, which only
      says connected. *)
Definition double_critical_graph_statement : Prop :=
  forall (G : sgraph) (n : nat),
    0 < #|G| -> connected [set: G] -> double_critical G ->
    χ([set: G]) = n -> inhabited (G ≃ 'K_n).

(** ** Row 2 — Three-chromatic (0,2)-graphs
    OPEN.

    Source: "Are there any (0,2)-graphs with chromatic number exactly three?
    A (0,2)-graph: every two distinct vertices have either 0 or exactly 2
    common neighbours."

    New AREA primitive: the (0,2) property [zero_two_graph]. *)
Definition zero_two_graph (G : sgraph) : Prop :=
  forall u v : G, u != v ->
    #|common_nbr u v| = 0 \/ #|common_nbr u v| = 2.

(** Corpus row: opg:three_chromatic_0_2_graphs
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/three_chromatic_0_2_graphs/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/three_chromatic_0_2_graphs.json
    English statement: (Open Problem Garden, "Three-chromatic (0,2)-graphs")
      There exists a finite simple graph in which any two distinct vertices have either no common
      neighbour or exactly two common neighbours, and whose chromatic number is exactly three.
    Definitions: [zero_two_graph G] - any two distinct vertices of G have 0 or exactly 2 common
      neighbours (this file); [common_nbr u v] - the intersection of the two open neighbourhoods
      (GTBase base/theories/base.v); chi is the coq-graph-theory chromatic number.
    Notes: The corpus row is a QUESTION, "Are there any (0,2)-graphs with chromatic number exactly
      three?"; the Rocq body commits to the affirmative answer, i.e. it is the existential statement
      whose truth would answer the question yes. A refutation of the question would refute this
      definition, so the encoding is the positive reading of the open problem. *)
Definition three_chromatic_0_2_graphs_statement : Prop :=
  exists G : sgraph, zero_two_graph G /\ χ([set: G]) = 3.

(** ** Row 3 — Cycles in graphs of large chromatic number
    PARTIAL (special cases proven; general open).

    Source: "If chi(G)>k, then G contains at least (k+1)(k-1)!/2 cycles of
    length 0 mod k."

    New AREA primitives: [n_cycles_len] (count of cycles of a fixed length)
    and [count_cycles_mod].  A cycle of length [L] is encoded as a closed walk
    [t : L.-tuple G] satisfying [ucycleb]; each undirected cycle is counted
    [2L] times (L rotations × 2 orientations), so we divide by [2 * L].  The
    statement is the conjecture multiplied through by 2 (so [(k+1)(k-1)!/2 ≤ c]
    becomes [(k+1)(k-1)! ≤ 2c], avoiding the halving).

    The [2 < L] filter restricts the count to GENUINE cycles: in a simple graph
    a closed walk with [size ≤ 2] is the empty walk ([ucycleb [::]] reduces to
    [true]) or a single edge ([ucycleb [x; y]] reduces to [x -- y]), neither of
    which is a cycle.  The [2 < k] guard pins the conjecture to its meaningful
    open regime: for [k = 1] take [G := 'K_2] ([χ = 2 > 1] but no genuine
    cycle, so the count is 0 and [2 * 0! = 2 ≤ 0] is FALSE), and for [k = 2]
    take a 5-cycle ([χ = 3 > 2], no even genuine cycle, count 0, again false).
    With [2 < k] the smallest [L] with [k %| L] and [0 < L] is [L = k ≥ 3], so
    the [2 < L] guard is automatically met and the [size 2] edge artefact never
    contributes. *)
Definition n_cycles_len (G : sgraph) (L : nat) : nat :=
  #|[set t : L.-tuple G | ucycleb (--) (val t)]| %/ (2 * L).

Definition count_cycles_mod (G : sgraph) (k : nat) : nat :=
  \sum_(L < #|G|.+1 | (2 < L) && (k %| L)) n_cycles_len G L.

(** Corpus row: opg:cycles_in_graphs_of_large_chromatic_number
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/cycles_in_graphs_of_large_chromatic_number/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/cycles_in_graphs_of_large_chromatic_number.json
    English statement: (Open Problem Garden, "Cycles in Graphs of Large Chromatic Number")
      For every integer k greater than 2 and every finite simple graph G whose chromatic number is
      greater than k, the number of cycles of G whose length is a positive multiple of k is at least
      (k+1) times (k-1) factorial, divided by two; the Rocq body states the doubled, division-free
      form (k+1) * (k-1)! <= 2 * (number of such cycles).
    Definitions: [count_cycles_mod G k] - the sum, over lengths L with L < #|G|+1, 2 < L and k
      dividing L, of [n_cycles_len G L] (this file); [n_cycles_len G L] - the number of L-tuples of
      vertices that form a closed walk with pairwise distinct vertices, as tested by the coq-graph-
      theory boolean [ucycleb], divided by 2*L so that the L rotations and 2 orientations of one
      undirected cycle are counted once (this file).
    Notes: Load-bearing modelling choices inherited from the file header: the [2 < L] filter drops
      the empty walk and the single-edge walk, which [ucycleb] also accepts but which are not
      cycles; the [2 < k] guard pins the conjecture to its meaningful regime, since for k = 1 the
      complete graph on 2 vertices and for k = 2 the 5-cycle are counterexamples to the unguarded
      reading; the division by 2*L is truncating nat division; the cycle lengths are bounded by #|G|
      which is harmless since a cycle has at most #|G| vertices. *)
Definition cycles_in_graphs_of_large_chromatic_number_statement : Prop :=
  forall (k : nat) (G : sgraph),
    2 < k -> k < χ([set: G]) ->
    (k.+1) * (k.-1)`! <= 2 * count_cycles_mod G k.

(** ** Row 4 — High-girth low-degree 4-chromatic graphs
    OPEN.

    Source: "Do there exist 4-regular 4-chromatic graphs of arbitrarily high
    girth?"

    Uses AREA primitives [regular] and [girth_geq]. *)
(** Corpus row: opg:high_girth_low_degree_4_chromatic_graphs
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/high_girth_low_degree_4_chromatic_graphs/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/high_girth_low_degree_4_chromatic_graphs.json
    English statement: (Open Problem Garden, "4-regular 4-chromatic graphs of high girth")
      For every g there exists a finite simple graph that is 4-regular, has chromatic number exactly
      4, and has girth at least g; that is, 4-regular 4-chromatic graphs of arbitrarily high girth
      exist.
    Definitions: [regular G 4] - every vertex has exactly 4 neighbours (GTBase
      base/theories/base.v); [girth_geq G g] - every cycle of G, that is every [ucycle] of size
      greater than 2, has length at least g (GTBase base/theories/base.v); chi is the coq-graph-
      theory chromatic number.
    Notes: The corpus row is the QUESTION "Do there exist 4-regular 4-chromatic graphs of
      arbitrarily high girth?"; the Rocq body is the affirmative answer. [girth_geq] carries its own
      [2 < size c] guard so that acyclic graphs satisfy it for every g. *)
Definition high_girth_low_degree_4_chromatic_graphs_statement : Prop :=
  forall g : nat, exists G : sgraph,
    [/\ regular G 4, χ([set: G]) = 4 & girth_geq G g].

(** ** Row 5 — Erdős–Faber–Lovász conjecture
    SOLVED for all large n (Kang–Kelly–Kühn–Methuku–Osthus, 2023); stated here
    as a Definition only.

    Source: "If G is a simple graph which is the union of k pairwise
    edge-disjoint complete graphs, each with k vertices, then chi(G) = k."

    New AREA primitive: [edge_disjoint_clique_union].  "Pairwise edge-disjoint"
    is encoded as: distinct cliques share at most one vertex (two shared
    vertices would be a shared edge). *)
Definition edge_disjoint_clique_union (G : sgraph) (k : nat) : Prop :=
  exists cliqs : 'I_k -> {set G},
    [/\ (forall i, #|cliqs i| = k),
        (forall i, clique (cliqs i)),
        (forall i j, i != j -> #|cliqs i :&: cliqs j| <= 1),
        (forall x : G, exists i, x \in cliqs i)
      & (forall x y : G, x -- y -> exists i, (x \in cliqs i) && (y \in cliqs i))].

(** Corpus row: opg:erdos_faber_lovasz_conjecture
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/erdos_faber_lovasz_conjecture/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/erdos_faber_lovasz_conjecture.json
    English statement: (Erdos, Faber and Lovasz 1972; Open Problem Garden, "Erdos-Faber-Lovasz conjecture")
      For every k, if a finite simple graph G is the union of k cliques, each with exactly k
      vertices, any two of which share at most one vertex, and if every vertex and every edge of G
      lies in one of these cliques, then the chromatic number of G is exactly k.
    Definitions: [edge_disjoint_clique_union G k] - there is a family of k vertex sets, indexed by
      ['I_k], each of size k, each a [clique], pairwise meeting in at most one vertex, covering
      every vertex and containing both ends of every edge (this file); [clique] and chi are coq-
      graph-theory vocabulary.
    Notes: "Pairwise edge-disjoint" is encoded as "distinct cliques share at most one vertex",
      since two shared vertices of two cliques would be a shared edge; this is faithful for the
      complete graphs of the source. The conclusion is the equality chi(G) = k, as in the corpus
      text, not merely the upper bound. The row is SOLVED for all large k, Kang, Kelly, Kuhn,
      Methuku and Osthus 2023; the Rocq body is the full unrestricted conjecture and is stated only,
      not proved. *)
Definition erdos_faber_lovasz_statement : Prop :=
  forall (k : nat) (G : sgraph),
    edge_disjoint_clique_union G k -> χ([set: G]) = k.

(** ** Row 6 — Borodin–Kostochka conjecture
    OPEN.

    Source: "Every graph with maximum degree Delta >= 9 has chromatic number at
    most max{Delta-1, omega}." *)
(** Corpus row: opg:the_borodin_kostochka_conjecture
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/the_borodin_kostochka_conjecture/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/the_borodin_kostochka_conjecture.json
    English statement: (Borodin and Kostochka 1977; Open Problem Garden, "The Borodin-Kostochka Conjecture")
      Every finite simple graph whose maximum degree is at least 9 has chromatic number at most the
      maximum of Delta(G) - 1 and the clique number omega(G).
    Definitions: [Delta G] - the maximum over vertices of the size of the open neighbourhood
      (GTBase base/theories/base.v); chi and omega are the subset-relative chromatic and clique
      numbers of coq-graph-theory, taken here on the full vertex set.
    Notes: The truncated nat subtraction [Delta G - 1] is harmless under the guard 9 <= Delta G. *)
Definition the_borodin_kostochka_statement : Prop :=
  forall G : sgraph,
    9 <= Delta G -> χ([set: G]) <= maxn (Delta G - 1) ω([set: G]).

(** ** Row 7 — Vertex colouring of graph fractional powers
    PARTIAL (special cases proven; general open).

    Source: "G^{m/n} := (G^{1/n})^m, where G^{1/n} is the n-subdivision
    (replace each edge by a path of length n) and G^m the m-th power (join
    vertices at distance <= m).  Conjecture: for connected G with Delta(G)>=3
    and integer m>1, for any n>m, chi(G^{m/n}) = omega(G^{m/n})."

    New AREA primitives: [graph_power], [subdivision], [frac_power].  Both
    constructions are produced as genuine [sgraph]s; their edge relations are
    made symmetric/irreflexive by construction (an OR with the reversed
    relation), so the [sgraph] proofs are immediate.

    [@MOVE-to-base] [graph_power], [subdivision] and [frac_power] are pure,
    colouring-free [sgraph] constructions (m-th power and n-subdivision of an
    arbitrary graph) reused across structural/topological areas; they are base
    candidates once G3 lands, tracked here only because base does not exist
    yet.  NB on the boundary: [subdivision G n] degenerates to an edgeless
    graph for [n ≤ 1] (no internal vertices); Row 7's guard [1 < m < n] keeps
    [n ≥ 3], but a future base move should document/repair the [n ≤ 1] corner. *)

(** *** Powers / subdivisions / fractional powers — PROMOTED to graph-theory-base.
    [graph_power], [subdivision], [frac_power] (and their helpers ball/reach_le/oedge/…)
    now live in base/ — reused here via `From GTBase Require Export base` — because a second
    area (homomorphism-theory/U3) also uses them. No local definitions remain. *)

(** Corpus row: opg:vertex_coloring_of_graph_fractional_powers
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/vertex_coloring_of_graph_fractional_powers/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/vertex_coloring_of_graph_fractional_powers.json
    English statement: (Iradmusa; Open Problem Garden, "Vertex Coloring of graph fractional powers")
      For every finite simple graph G whose vertex set is connected and whose maximum degree is at
      least 3, and for all m and n with 1 < m and m < n, the fractional power G^(m/n), defined as
      the m-th power of the n-subdivision of G, satisfies chi = omega on its full vertex set.
    Definitions: [frac_power G m n] - the m-th power of the n-subdivision of G (GTBase
      base/theories/base.v); [subdivision G n] - replace every edge by a path with n edges (GTBase
      base.v); [graph_power H m] - join two distinct vertices when one is in the m-ball of the other
      (GTBase base.v); [Delta], chi, omega and [connected] are GTBase / coq-graph-theory vocabulary.
    Notes: [subdivision G n] degenerates to an edgeless graph for n <= 1, but the guard 1 < m < n
      forces n >= 3, so the degenerate corner is unreachable from this statement. The corpus text
      spells out the definitions of power, subdivision and fractional power before the conjecture
      proper; the Rocq body encodes only the conjecture, with the source hypotheses connected, Delta
      >= 3, m > 1, n > m. *)
Definition vertex_coloring_of_graph_fractional_powers_statement : Prop :=
  forall (G : sgraph) (m n : nat),
    connected [set: G] -> 3 <= Delta G -> 1 < m -> m < n ->
    χ([set: frac_power G m n]) = ω([set: frac_power G m n]).

(** ** Row 8 — Melnikov's valency-variety problem
    OPEN.

    Source: "The valency-variety w(G) of a graph G is the number of different
    degrees in G.  Is the chromatic number of any graph G with at least two
    vertices greater than ceil( floor(w(G)/2) / (|V(G)| - w(G)) )?"

    New AREA primitive: [valency_variety] (number of distinct vertex degrees). *)
Definition valency_variety (G : sgraph) : nat :=
  size (undup [seq #|N(x)| | x <- enum [set: G]]).

(** Corpus row: opg:melnikovs_valency_variety_problem
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/melnikovs_valency_variety_problem/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/melnikovs_valency_variety_problem.json
    English statement: (Melnikov; Open Problem Garden, "Melnikov's valency-variety problem")
      For every finite simple graph G with at least two vertices, the chromatic number of G is
      strictly greater than the ceiling of the quotient of the floor of w(G)/2 by |V(G)| - w(G),
      where w(G), the valency-variety, is the number of distinct vertex degrees of G.
    Definitions: [valency_variety G] - the number of distinct values of #|N(x)| over the vertices
      of G, computed as the size of the duplicate-free list of degrees (this file); [ceil_div a b] -
      the ceiling of a/b with the mathcomp convention ceil_div a 0 = 0 (GTBase
      base/theories/base.v).
    Notes: The corpus row is a QUESTION, "Is the chromatic number ... greater than ...?"; the Rocq
      body asserts the inequality, i.e. the affirmative answer. Both the inner halving and the outer
      division are nat operations, so the inner floor and the outer ceiling are exactly the floor
      and ceiling of the source. The denominator |V(G)| - w(G) is a truncated nat subtraction and
      would give ceil_div _ 0 = 0 if w(G) = |V(G)|; that case does not occur for #|G| >= 2, since a
      graph never realises all of 0, ..., #|G|-1 as degrees. *)
Definition melnikovs_valency_variety_statement : Prop :=
  forall G : sgraph, 2 <= #|G| ->
    ceil_div (valency_variety G %/ 2) (#|G| - valency_variety G)
      < χ([set: G]).

(** ** Row 9 — Reed's ω, Δ and χ conjecture
    OPEN.

    Source: "Conjecture: chi(G) <= ceil( (1/2)(Delta(G)+1) + (1/2)omega(G) )
    for every graph G."  Stated in the doubled, subtraction-free form
    [2·chi ≤ (Δ+1) + ω + 1]. *)
(** Corpus row: opg:reeds_omega_delta_and_chi_conjecture
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/reeds_omega_delta_and_chi_conjecture/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/reeds_omega_delta_and_chi_conjecture.json
    English statement: (Reed 1998; Open Problem Garden, "Reed's omega, delta, and chi conjecture")
      Every finite simple graph G with at least one vertex satisfies 2 * chi(G) <= (Delta(G) + 1) +
      omega(G) + 1, the doubled and subtraction-free form of chi(G) <= ceiling of half of (Delta(G)
      + 1 + omega(G)).
    Definitions: [Delta G] - maximum degree (GTBase base/theories/base.v); chi and omega are the
      coq-graph-theory chromatic and clique numbers on the full vertex set.
    Notes: The doubled form is equivalent to the source inequality by parity: with a := Delta(G) +
      1 + omega(G), chi <= ceil(a/2) holds iff 2*chi <= a+1, because 2*chi is even and so 2*chi <=
      a+1 is equivalent to 2*chi <= a when a is even. The guard 0 < #|G| excludes the empty graph,
      where Delta is 0 by convention. *)
Definition reeds_omega_delta_and_chi_statement : Prop :=
  forall G : sgraph, 0 < #|G| ->
    2 * χ([set: G]) <= Delta G + 1 + ω([set: G]) + 1.
