(** * Packing.conjectures.implications_U9 — internal implication spine for U9

    Qed-closed RELATIVE theorems [Theorem A_implies_B : A_statement -> B_statement]
    between the thirteen open-problem nodes of milestone U9, each provable WITHOUT
    resolving either endpoint, plus the machine-readable [@EDGE] annotations that
    [meta/build_edge_graph.py] extracts.

    EDGE POLICY (plan §6): schedule ONLY 'verified-literature' edges; a verified
    edge MUST carry a real [Theorem A_implies_B] closing with [Qed].  'candidate'
    edges are re-derived under the Qed gate before promotion and appear here as the
    annotation ONLY (no theorem).  A genuinely false edge must FAIL to compile — it
    is never forced.

    FINDING.  U9's thirteen nodes are MUTUALLY INDEPENDENT open problems over
    different carriers and object levels:

      R1  cubic 3-connected P3-partition          (sgraph, vertex partition)
      R2  Tuza triangle-packing vs edge-transversal (sgraph, factor-2 duality)
      R3  friendly partitions of regular graphs    (sgraph, vertex bipartition)
      R4  partitioning edge-connectivity {A,B}     (mgraph, edge split)
      R5  Bollobás–Eldridge–Catlin packing         (sgraph pair, Δ condition)
      R6  Lovász induced-path removal               (sgraph, k-connectivity)
      R7  Jones cc ≤ 2·cp (planar)                  (sgraph, FVS/cycle duality)
      R8  odd-cycle edge-transversal (triangle-free)(sgraph, ≤ n²/25 edges)
      R9  matching-cut from girth + low avg-degree  (sgraph, edge cut)
      R10 Kriesell edge-disjoint Steiner trees      (mgraph, tree packing)
      R11 hypercube matchings → Hamilton cycle      (hypercube, extension)
      R12 wsat(K_n, Q_3) well-defined               (edge sets over 'I_n)
      R13 T-join packing ≥ (2/3)·minTcut − c        (mgraph graft, join packing)

    No node is a logical weakening, specialization, or refutation of another: the
    hypotheses constrain disjoint graph classes and the conclusions assert
    existence of incomparable objects.  Consequently there is NO internal
    verified-literature implication edge, and §6's verified table lists none for
    U9.  The single §6-cited U9-relevant relation — Tuza ⟹ fractional relaxation,
    "and relation to Jones" — links R2 and R7 only as a STRUCTURAL ANALOGY (both
    are factor-2 covering ≤ 2·packing dualities), NOT a logical implication: from a
    triangle-edge transversal bound one cannot derive the cycle/feedback-vertex-set
    bound (different objects, different ambient class), so the candidate edge
    R2 ⟹ R7 does not close under Qed and is recorded as the annotation only,
    proved=false.

    This file therefore declares the U9 edge set to be EMPTY of verified
    implications and records the one literature-suggested candidate. *)

From GraphTheory Require Import mgraph.
From GTBase Require Import base.
From Packing.conjectures Require Import U9.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ================================================================= *)
(** ** Verified-literature edges: NONE.

    Plan §6's verified-literature table carries no U9-internal edge, and the
    independence analysis above re-confirms this: there is no pair (A,B) of U9
    nodes with a Qed-closable [A_statement -> B_statement] that does not resolve
    an endpoint.  No [Theorem _implies_] is scheduled. *)

(** ================================================================= *)
(** ** Candidate edge (annotation only — NOT scheduled, does not close).

    Tuza's triangle packing/transversal duality (R2) and Jones' planar
    feedback-vertex-set / cycle-packing duality (R7) are the two factor-2
    covering–packing dualities in U9.  §6 records "Tuza ⟹ fractional relaxation
    (and relation to Jones)" as a CANDIDATE.  Within U9 this touches R2 and R7
    only, and the relation is a structural ANALOGY, not a logical implication: the
    transversal/packing objects (triangle edges) and the FVS/cycle objects live in
    different ambient classes, so no [triangle_packing_vs_triangle_edge_transversal_statement
    -> jones_statement] derivation exists without resolving an endpoint.  Recorded
    as candidate, proved=false; the Qed gate must re-derive an exact common
    strengthening before any promotion. *)

(*@EDGE from=triangle_packing_vs_triangle_edge_transversal_statement to=jones_statement kind=implies status=refuted-direction cite="Tuza, Conjecture on triangle packing/covering, in Finite and Infinite Sets (1981); F. Jones / D. Chen, Jones' conjecture on planar cc <= 2 cp" note="REFUTED-DIRECTION (metadata wave M, 2026-09-24): structural analogy only, two object levels; not a logical implication. Earlier note: Structural analogy only: both are factor-2 covering<=2*packing dualities (Tuza: triangle-edge transversal <= 2*triangle-packing; Jones: feedback-vertex-set <= 2*cycle-packing on planar graphs). Not a logical implication across the two object levels; does not close under Qed without resolving an endpoint. Candidate per plan v4 §6 (Tuza -> fractional relaxation / relation to Jones)." *)
