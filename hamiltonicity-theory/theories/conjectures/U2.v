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
(** ** Row 1 — Hamiltonian paths and cycles in vertex-transitive graphs  (OPEN)

    Source: "Problem: Does every connected vertex-transitive graph have a
    Hamiltonian path ?"

    Carrier: [sgraph].  New AREA primitives: [hamiltonian_path], [vertex_transitive].
    Guard [0 < #|G|] excludes the empty graph (whose empty seq is vacuously a
    "Hamiltonian path"). *)
Definition hamiltonian_paths_and_cycles_in_vertex_transitive_gr_statement : Prop :=
  forall G : sgraph,
    0 < #|G| -> connected [set: G] -> vertex_transitive G ->
    exists s : seq G, hamiltonian_path G s.

(** ** Row 2 — Hamiltonicity of Cayley graphs  (OPEN)

    Source: "Question: Is every Cayley graph Hamiltonian?"

    Carrier: the [cayley_graph] of a [finGroupType].  New AREA primitives:
    [cayley_graph], [is_hamiltonian] (hamiltonicity).  Guards pin the meaningful
    open form (Lovász/Babai circle): the connection set is symmetric and
    generates the group (so the Cayley graph is connected), and the group has at
    least 3 elements (so a Hamilton cycle is non-degenerate). *)
Definition hamiltonicity_of_cayley_graphs_statement : Prop :=
  forall (gT : finGroupType) (S : {set gT}),
    2 < #|gT| -> symmetric_set S -> <<S>>%g = [set: gT] ->
    is_hamiltonian (cayley_graph S).

(** ** Row 3 — 4-connected graphs are not uniquely Hamiltonian  (OPEN)

    Source: "Conjecture: Every 4-connected graph with a Hamilton cycle has a
    second Hamilton cycle."

    Carrier: [sgraph].  "Second Hamilton cycle" = a Hamilton cycle with a
    DIFFERENT edge set (so genuinely distinct, not a rotation/reflection). *)
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
  simple_edge_set G.

Definition hamilton_decomposition_into_two (G : sgraph) : Prop :=
  exists c1 c2 : seq G,
    [/\ hamiltonian_cycle G c1, hamiltonian_cycle G c2,
        [disjoint cycle_edges G c1 & cycle_edges G c2]
      & cycle_edges G c1 :|: cycle_edges G c2 = edge_set G].

Definition decomposing_the_prism_of_a_3_connected_cubic_planar_statement : Prop :=
  forall (G : sgraph),
    wagner_planar G -> k_connected G 3 -> regular G 3 ->
    hamilton_decomposition_into_two (cartesian_product G 'K_2).

(** ** Row 6 — Every 4-connected toroidal graph has a Hamilton cycle  (OPEN)
    Now uses the real [toroidal] (embeds in the orientable genus-1 surface, i.e.
    [embeds_in_genus G 1]) from the Track-A combinatorial embedding foundation
    ([Topological.foundations.embedding]) — non-vacuous (every graph has an
    embedding, so planar graphs are toroidal); [k_connected] from base.

    Source: "Conjecture: Every 4-connected toroidal graph has a Hamilton cycle." *)
Definition every_4_connected_toroidal_graph_has_a_hamilton_cycl_statement : Prop :=
  forall G : sgraph, toroidal G -> k_connected G 4 -> is_hamiltonian G.

(** ** Row 7 — Every prism over a 3-connected planar graph is Hamiltonian  (OPEN)
    Planarity is the combinatorial [wagner_planar] (no K5/K3,3 minor) from base.

    Source: "Conjecture: If G is a 3-connected planar graph, then G□K_2 has a
    Hamilton cycle." *)
Definition every_prism_over_a_3_connected_planar_graph_is_hamil_statement : Prop :=
  forall (G : sgraph),
    wagner_planar G -> k_connected G 3 -> is_hamiltonian (cartesian_product G 'K_2).

(** ** Row 8 — Barnette's conjecture  (OPEN)
    Planarity is the combinatorial [wagner_planar] (no K5/K3,3 minor) from base.

    Source: "Conjecture: Every 3-connected cubic planar bipartite graph is
    Hamiltonian."  Cubic = [regular G 3] (base); bipartite = [bipartite G]. *)
Definition barnettes_statement : Prop :=
  forall (G : sgraph),
    wagner_planar G -> k_connected G 3 -> regular G 3 -> bipartite G -> is_hamiltonian G.

(** ** Row 9 — Hamiltonian cycles in line graphs  (OPEN)

    Source: "Conjecture: Every 4-connected line graph is hamiltonian."

    Carrier: the [line_graph G].  New AREA primitive: [line_graph] (line-graph). *)
Definition hamiltonian_cycles_in_line_graphs_statement : Prop :=
  forall G : sgraph,
    k_connected (line_graph G) 4 -> is_hamiltonian (line_graph G).
