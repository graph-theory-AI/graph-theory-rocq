(** * Extremal.conjectures.implications_D2chr — milestone D2chr dependency-graph EDGES

    Machine-checked implication / refutation EDGES between the nine committed
    D2chr conjecture statements (see [D2chr.v]).  As in the sibling
    [implications_D2str.v] / [implications_D2tur.v] layers, every SCHEDULED edge
    is a *relative* theorem: a [Qed]-closed [Theorem A_statement -> B_statement]
    provable WITHOUT resolving (proving or refuting) either endpoint.  This file
    is axiom-free: no [Conjecture]/[Axiom]/[Parameter]/[Admitted]; bridge facts
    that would need resolving a conjecture are carried as EXPLICIT hypotheses,
    never asserted, and a genuinely false edge is left to FAIL the [Qed] gate
    rather than forced.

    The nine D2chr nodes are:
      • [fractional_hadwiger_statement]                                    (Row 1)
      • [mixing_circular_colourings_0_statement]                           (Row 2)
      • [list_chromatic_number_and_maximum_degree_of_bipartit_statement]   (Row 3)
      • [monochromatic_vertex_colorings_inherited_from_perfec_statement]   (Row 4)
      • [choosability_of_graph_powers_statement]                           (Row 5)
      • [circular_choosability_of_planar_graphs_statement]                 (Row 6)
      • [star_chromatic_index_of_complete_graphs_statement]                (Row 7)
      • [circular_chromatic_number_of_triangle_free_planar_gr_statement]   (Row 8)
      • [circular_colouring_the_orthogonality_graph_statement]             (Row 9)

    ════════════════════════════════════════════════════════════════════════════
    RESULT:  no verified-literature edge is internal to D2chr.
    ════════════════════════════════════════════════════════════════════════════

    The §6 verified-literature edge table (OPG_FULL_FORMALIZATION_PLAN.md v4)
    lists ONLY cycle / edge-colouring edges (Petersen-colouring, Berge–Fulkerson,
    CDC, Tutte 4-flow); none of its endpoints is a D2chr node.  D2chr collects ten
    PAIRWISE-INDEPENDENT open problems in fractional / circular / list colouring
    and the fractional Hadwiger number: each row asks its own existential meta-
    question (best constant / bounding function / attained value), and no row's
    statement is a logical specialisation of another under the faithful [D2chr.v]
    formulations.  Below, the three temptations a reader might raise are recorded
    for the extractor as candidate / refuted-direction annotations and shown NOT
    to close.

    ────────────────────────────────────────────────────────────────────────────
    (1) Row 6 ⟹ Row 8  — "a bound on circular choosability of planar graphs
        bounds the circular chromatic number of the triangle-free cubic planar
        subclass".  CANDIDATE, refuted by the constant gap.
    ────────────────────────────────────────────────────────────────────────────

    The genuine inequality behind the temptation is  cch(G) ≥ χ_c(G)  (every
    circularly-t-choosable graph is (p,q)-colourable for all p ≥ t·q, by taking
    FULL lists — the [cch_gives_pq_colouring] lemma below makes exactly this
    mechanism precise and [Qed]-closes it).  So if Row 6 delivers a least upper
    bound [B] on cch over all (Wagner-)planar graphs, one gets χ_c(G) ≤ B for
    every planar G that HAS a circular-choosability value.

    This does NOT yield Row 8's bound [20/7]:
      • Row 8 demands  χ_c ≤ 20/7 ≈ 2.857  on triangle-free cubic planar graphs,
        whereas the planar circular-choosability bound [B] of Row 6 is known to be
        ≥ 4 (there exist planar graphs with cch ≥ 4); deriving [20/7] from a bound
        [B ≥ 4] is impossible, so the relative theorem cannot close;
      • Row 6 only constrains planar graphs that POSSESS an [is_circular_choosability]
        value, giving no handle on an arbitrary triangle-free cubic planar [G].
    Hence Row 6 ⟹ Row 8 is recorded as a candidate annotation (proved=false) and
    deliberately left unscheduled; the [Qed] gate rejects it.

    ────────────────────────────────────────────────────────────────────────────
    (2) Row 8 ⟷ Row 9  — both ask for a circular chromatic VALUE, via the shared
        [is_circular_chromatic].  No edge.
    ────────────────────────────────────────────────────────────────────────────

    Row 8 bounds χ_c on FINITE triangle-free cubic (Wagner-)planar [sgraph]s; Row 9
    pins χ_c = 4 of the INFINITE orthogonality graph on nonzero 3-vectors of a
    real-closed field with perpendicularity adjacency.  The two share only the
    [is_circular_chromatic] primitive; their carriers, adjacencies and hypotheses
    are disjoint (planar finite cubic vs. infinite non-planar geometric), and
    neither value/bound transports to the other.  Not an edge in either direction.

    ────────────────────────────────────────────────────────────────────────────
    (3) Row 3 ⟹ Row 5  — both bound a list/choice number via [is_choice_number].
        No edge.
    ────────────────────────────────────────────────────────────────────────────

    Row 3 seeks a constant [c] with  ch(G) ≤ c·log Δ  (encoded [2^ch ≤ Δ^c]) for
    BIPARTITE graphs; Row 5 seeks an [o(k²)] function [f] with  ch(G²) ≤ f(χ(G²))
    for the SQUARE [G²] of an arbitrary graph.  They share the [is_choice_number]
    primitive but quantify over disjoint graph families (bipartite [G] vs. squares
    [G²]) with incomparable parameters (log of max degree vs. a quadratic-order
    function of the chromatic number); neither hypothesis class contains the other
    and neither bound implies the other.  Not an edge in either direction.

    ────────────────────────────────────────────────────────────────────────────
    The remaining rows (1 fractional Hadwiger, 2 mixing-threshold rationality,
    4 perfect-matching monochromatic weights, 7 star chromatic index of K_n) carry
    no textbook implication to or from any other D2chr node: they live on disjoint
    objects (clique-minor LP relaxation; recolouring-graph connectivity; signed
    perfect-matching sums; star edge colourings) with no shared reduction.  Hence
    ZERO D2chr-internal verified-literature edges; the three annotations below are
    recorded for [meta/build_edge_graph.py] and deliberately left unscheduled.

    Citations.  X. Zhu, "Circular choosability of graphs", J. Graph Theory 48
    (2005) 210–218 (cch(G) ≥ χ_c(G), and planar cch lower bounds ≥ 4); the row
    problems are independent OPG entries (problems manifest, plan v4 §6). *)

From GTBase Require Export base.
From Extremal.conjectures Require Import D2chr.
From mathcomp Require Import all_algebra.
Import GRing.Theory Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.

(** ── Supporting lemma (NOT a node edge) ─────────────────────────────────────
    The exact mechanism cch(G) ≥ χ_c(G) underlying temptation (1): a circularly
    [t]-choosable graph is [(p,q)]-colourable whenever [p ≥ t·q], obtained by
    handing [t_pq_choosable] the FULL palette list [L v = [set: 'I_p]] (whose
    size [p] meets the [t·q] threshold).  This is a genuine [Qed]-closed fact
    provable without resolving any conjecture; it substantiates why the Row 6 ⟹
    Row 8 candidate is mathematically motivated — and, by exposing that it only
    yields χ_c ≤ t (≥ 4 for planar), why it nevertheless cannot reach Row 8's
    [20/7].  It is a sub-component relation, not a node-to-node edge, so it is
    NOT emitted as an [@EDGE]. *)
Lemma cch_gives_pq_colouring (G : sgraph) (t : rat) (p q : nat) :
  circularly_t_choosable G t -> (0 < q)%N -> t * q%:Q <= p%:Q ->
  exists c : G -> 'I_p,
    pq_colouring (fun x y : G => x -- y) p q (fun v => (c v : nat)).
Proof.
move=> Hcch Hq Hle.
have Hcard : forall v : G, t * q%:Q <= (#|[set: 'I_p]|)%:Q.
  by move=> v; rewrite cardsT card_ord.
have [c [Hpq _]] := Hcch p q Hq (fun _ : G => [set: 'I_p]) Hcard.
by exists c.
Qed.

(** ── Machine-readable edge records (extracted by meta/build_edge_graph.py) ───
    Each [from]/[to] is the exact [_statement] Definition name from [D2chr.v].
    All three are NON-edges under the faithful formulations: none is scheduled as
    a [Theorem] and none is asserted. *)

(*@EDGE from=circular_choosability_of_planar_graphs_statement to=circular_chromatic_number_of_triangle_free_planar_gr_statement kind=implies status=refuted-direction cite="X. Zhu, Circular choosability of graphs, JGT 48 (2005) 210-218 (cch >= chi_c, planar cch >= 4); OPG_FULL_FORMALIZATION_PLAN.md v4 §6" note="REFUTED-DIRECTION (metadata wave M, 2026-09-24): self-described refuted by the Qed gate (cch >= chi_c gives B >= 4 > 20/7). Earlier note: Candidate refuted by the Qed gate: the real relation cch(G) >= chi_c(G) (lemma cch_gives_pq_colouring) only gives chi_c(G) <= B for planar G that possess a circular-choosability value, but Row 6's least planar cch bound B is >= 4 > 20/7, so it cannot yield Row 8's 20/7 bound (and gives no handle on an arbitrary triangle-free cubic planar G). Not stated." *)

(*@EDGE from=circular_chromatic_number_of_triangle_free_planar_gr_statement to=circular_colouring_the_orthogonality_graph_statement kind=implies status=refuted-direction proved=false cite="OPG_FULL_FORMALIZATION_PLAN.md v4 §6 edge policy; independent OPG circular-colouring entries" note="Non-edge. Both ask for a circular chromatic value via is_circular_chromatic, but on disjoint carriers: Row 8 bounds chi_c on FINITE triangle-free cubic Wagner-planar sgraphs; Row 9 pins chi_c=4 of the INFINITE orthogonality graph on nonzero 3-vectors of a real-closed field. Disjoint vertex types, adjacencies and hypotheses; no value/bound transports. Neither direction holds. Not stated." *)

(*@EDGE from=list_chromatic_number_and_maximum_degree_of_bipartit_statement to=choosability_of_graph_powers_statement kind=implies status=refuted-direction proved=false cite="OPG_FULL_FORMALIZATION_PLAN.md v4 §6 edge policy; independent OPG list-colouring entries" note="Non-edge. Both bound a choice number via is_choice_number, but over disjoint families with incomparable parameters: Row 3 wants ch(G) <= c*log(Delta) for BIPARTITE G; Row 5 wants ch(G^2) <= f(chi(G^2)) with f = o(k^2) for the SQUARE of an arbitrary G. Neither hypothesis class contains the other and neither bound implies the other. Neither direction holds. Not stated." *)
