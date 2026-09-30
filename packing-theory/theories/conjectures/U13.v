(** * Packing.conjectures.U13 — milestone U13 (namespace Packing, plan v4)

    Statement-only formalizations (axiom-free: no Conjecture/Axiom/Parameter/
    Admitted) of two open domination problems.

    CARRIERS ARE CHOSEN PER ROW (no blanket [sgraph] imposed by fiat, but both
    rows are genuinely about simple undirected graphs, so both carriers ARE
    [sgraph], as dictated by each row's [rocq_idiom]):

      - Row 1 [domination_in_cubic_graphs]: [sgraph]; cubic = [regular G 3]
        (base), 3-connected = [k_connected G 3] (base), the ceiling ⌈|G|/3⌉ =
        [ceil_div #|G| 3] (base), and the domination number is the cardinality
        of a minimum dominating set.
      - Row 2 [domination_in_plane_triangulations]: [sgraph]; PLANARITY-GATED /
        BLOCKED (G2 gate) — see below.

    REUSED FROM GraphTheory core ([dom]): [dom.dominating] (a vertex set whose
    closed neighbourhood is everything).  REUSED FROM base (NOT redefined):
    [regular] (cubic = 3-regular), [k_connected] (Whitney k-connectivity, which
    itself carries the guard [k < #|G|]), [ceil_div] (⌈a/b⌉ = (a+b-1) %/ b).

    AREA primitive introduced here (domination specific): [is_domination_number]
    — the relational "γ(G) = m" (m is the least cardinality of a dominating
    set), built on top of GraphTheory's [dom.dominating].  This mirrors the
    relational min/max idiom used elsewhere in this namespace ([is_min_fvs],
    [is_wsat], [is_max_cycle_packing] in U9): the statement quantifies over the
    witness [m] constrained by [is_domination_number G m], which is exactly the
    idiom's [domnum G <= …].

    PLANARITY G2-GATE (Row 2, [requires_planarity=true]): the planar / Four-
    Colour layer is NOT installed on this switch.  "Plane triangulation" is
    therefore modelled as an ABSTRACT predicate [plane_triangulation :
    sgraph -> Prop] quantified INSIDE the [Prop] — never a top-level
    Axiom/Parameter (that would contaminate Print Assumptions).  Because the
    real geometric notion of a plane triangulation is unavailable, this
    predicate is a placeholder: the row TYPE-CHECKS and is axiom-free, but is
    BLOCKED — it does not yet state the genuine geometric conjecture.  Row 1 is
    unaffected and models its statement fully. *)

From GTBase Require Export base.
From Topological.foundations Require Import embedding.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ================================================================= *)
(** ** Shared domination primitive (area-specific) *)

(** [m] is the domination number γ(G): the least cardinality over all dominating
    sets (a dominating set [D] being one whose closed neighbourhood [NS[D]] is
    the whole vertex set, i.e. GraphTheory's [dom.dominating D]).  Stated
    relationally: some dominating set realises [m], and every dominating set has
    at least [m] vertices.  Well-defined on every graph since [[set: G]] is
    always dominating, but we do not need that fact to state the conjectures. *)
Definition is_domination_number (G : sgraph) (m : nat) : Prop :=
  (exists D : {set G}, dom.dominating D /\ #|D| = m) /\
  (forall D : {set G}, dom.dominating D -> m <= #|D|).

(** ================================================================= *)
(** Corpus row: opg:domination_in_cubic_graphs
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/domination_in_cubic_graphs/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/domination_in_cubic_graphs.json
    English statement: (Open Problem Garden, "Domination in cubic graphs")
      For every simple graph G and every natural number m, if G is 3-regular, G is
      3-connected, and m is the domination number of G, then m is at most the ceiling
      of |V(G)| divided by 3.
    Definitions: [is_domination_number G m] — some dominating set of G has exactly m
      vertices and every dominating set of G has at least m vertices (this file);
      [dom.dominating D] — the closed neighbourhood of D is the whole vertex set
      (coq-graph-theory dom.v); [regular G 3] — every vertex has exactly three
      neighbours (GTBase base); [k_connected G 3] — Whitney 3-connectivity, which
      itself carries the guard 3 < |V(G)| (GTBase base); [ceil_div a b] — (a+b-1) %/ b
      (GTBase base).
    Notes: "gamma(G) <= k" is rendered relationally: the statement quantifies over a
      witness m constrained by [is_domination_number G m] rather than over a defined
      gamma function (gamma(G) <= k iff the unique domination number m satisfies
      m <= k). [k_connected G 3] also supplies the non-triviality guard 3 < |V(G)|. *)
Definition domination_in_cubic_graphs_statement : Prop :=
  forall (G : sgraph) (m : nat),
    regular G 3 -> k_connected G 3 ->
    is_domination_number G m ->
    m <= ceil_div #|G| 3.

(** Corpus row: opg:domination_in_plane_triangulations
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/domination_in_plane_triangulations/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/domination_in_plane_triangulations.json
    English statement: (Open Problem Garden, "Domination in plane triangulations")
      There is an order threshold n0 such that for every simple graph G, every
      embedding E of G and every natural number m: if G is connected, E is a genus-0
      (planar) rotation-system embedding all of whose faces are triangles, G has at
      least n0 vertices, and m is the domination number of G, then m is at most the
      floor of |V(G)| divided by 4.
    Definitions: [is_domination_number G m] — some dominating set of G has exactly m
      vertices and every dominating set has at least m (this file); [embedding],
      [planar_embedding E], [triangulation E] — rotation-system embedding, Euler genus
      0, every face a triangle (Topological.foundations.embedding); [dom.dominating],
      [connected [set: G]] — coq-graph-theory.
    Notes: "plane triangulation" is the real combinatorial notion (Wave 1 Track-A
      embedding foundation), not an abstract placeholder. "Sufficiently large" is an
      existential order threshold n0, which doubles as the non-triviality guard, and
      "dominating set of size <= (1/4)|V(G)|" is rendered as m <= |V(G)| %/ 4 (floor
      division). The connectedness guard is load-bearing, not cosmetic: [euler_genus]
      is the connected-map Euler relation over truncating nat arithmetic, so without it
      disconnected pseudo-planar instances slip in (c >= 2 disjoint triangles satisfy
      2+E-V-F = 2-2c <= 0, hence genus 0, yet need gamma = n/3 > n/4, making the
      unguarded statement provably false — caught by the Track-A review); plane
      triangulations are connected by definition, so the guard is faithful.  Vertex-count
      convention: [emV] counts every vertex including isolated ones (embedding.v fix
      2026-09-23, mirroring base/theories/surface.v); this does not move the statement,
      whose order threshold [n0] is existential and now simply has to exceed 1. *)
Definition domination_in_plane_triangulations_statement : Prop :=
  exists n0 : nat,
    forall (G : sgraph) (E : embedding G) (m : nat),
      connected [set: G] ->
      planar_embedding E -> triangulation E -> n0 <= #|G| ->
      is_domination_number G m ->
      m <= #|G| %/ 4.
