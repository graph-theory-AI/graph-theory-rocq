(** * Cycle.conjectures.X228 -- flow-pair row (wave X228, 2026-09-23) *)

(** The cycle-theory share of the multi-package wave X228: one FLOW row,
    Conjecture 6.1 of the 2025 Workshop on Cycles and Colourings problem
    collection (arXiv:2511.02892), the "1/2-flow-pair" conjecture.

    CARRIER: an undirected MULTIGRAPH, coq-graph-theory's [mgraph], exactly as
    the fifteen flow rows of [D1.v]; edges carry an intrinsic reference
    orientation ([source]/[target]) and a k-flow is an INTEGER edge weighting
    that may be negative, absorbing the choice of orientation, with Kirchhoff
    conservation at every vertex.  The row reuses [D1.v]'s [iconservative] and
    the [bridgeless] predicate of [Cycle.foundations.connectivity] (the
    UNDIRECTED, cut-edge notion), so that the
    corpus implication edge e174 to [five_flow_statement] (D1.v, Tutte's 5-flow
    conjecture) is stated between comparable objects.

    IMPORT ORDER: [mgraph] before [base] (base ships an undirected [line_graph]
    the multigraph one would otherwise shadow), and the mathcomp algebra layer
    AFTER [base] so its canonical [int] order instances win -- the order used by
    [D1.v]. *)

From mathcomp Require Import all_boot.
From GraphTheory Require Import mgraph sgraph treewidth.
From GTBase Require Export base.
From Cycle.foundations Require Export connectivity.
From mathcomp Require Import all_algebra all_fingroup.
From Cycle.conjectures Require Export D1.

Import GRing.Theory Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope ring_scope.

(** ** Local x228 vocabulary ***********************************************)

(** A [k]-FLOW (not necessarily nowhere-zero): an integer edge weighting that is
    Kirchhoff-conservative at every vertex and bounded by [k-1] in absolute
    value.  This is the flow notion the source's [phi_2] and [phi_4] use; it is
    strictly weaker than [D1.has_nz_kflow], which additionally forbids the
    value zero. *)
Definition x228_kflow (G : mgraph) (k : nat) (phi : edge G -> int) : Prop :=
  iconservative phi /\ forall e : edge G, `|phi e| <= (k.-1)%:R.

(** [G] has a 1/2-flow-pair: a 2-flow and a 4-flow such that on every edge where
    the 2-flow vanishes the 4-flow has absolute value at least 2. *)
Definition x228_half_flow_pair (G : mgraph) : Prop :=
  exists phi2 phi4 : edge G -> int,
    [/\ @x228_kflow G 2 phi2,
        @x228_kflow G 4 phi4
      & forall e : edge G, phi2 e = 0 -> 2%:R <= `|phi4 e|].

(** ** X228 statements *****************************************************)

(** Corpus row: arxiv:2511.02892#06
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/2511.02892__06/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/2511.02892__06.json
    English statement: (Workshop on Cycles and Colourings 2025 problem collection,
      arXiv:2511.02892, Conjecture 6.1)
      Every multigraph with at least one edge in which no edge is a bridge carries two
      integer weightings of its edges, one of absolute value at most 1 and one of absolute
      value at most 3, each of which has, at every vertex, the same total weight on the
      edges leaving the vertex as on the edges entering it, and such that on every edge
      where the first weighting is zero the second has absolute value at least 2.
    Definitions: [x228_kflow G k phi] - phi is Kirchhoff-conservative and bounded by k - 1
      in absolute value, a k-flow in which the value zero is allowed (X228.v);
      [x228_half_flow_pair G] - such a 2-flow and 4-flow with the stated compatibility
      (X228.v); [iconservative phi] - at every vertex the sum of phi over the edges with
      that vertex as source equals the sum over the edges with it as target (D1.v);
      [bridgeless G] - no edge is a bridge (cut edge), an edge that every UNDIRECTED walk
      between its endpoints must use (cycle-theory/theories/foundations/connectivity.v).
    Notes: a "k-flow" here ALLOWS the value zero; only the compatibility condition makes the
      pair nowhere-zero in the combined sense, so [x228_kflow] is deliberately weaker than
      [D1.has_nz_kflow]. "Bridgeless" is the corpus text's hypothesis; the guard
      [0 < #|edge G|] excludes the edgeless graph, exactly as in [five_flow_statement].
      Orientations are absorbed into the sign of the weighting on the intrinsic
      source-to-target orientation of the multigraph edges, the convention of D1.v. The
      source's "|phi_4(e)| >= 2" is the integer inequality [2%:R <= `|phi4 e|].
      REPAIRED (foundation repair, 2026-09-23): the flow part of the row was
      already faithful - a k-flow allowing the value zero and bounded by k-1 is
      exactly what the source's "(5 phi_2 + phi_4)/2 is a circular 5-flow"
      needs - and the HYPOTHESIS is now faithful too, with the row's body
      unchanged. [bridgeless] (cycle-theory/theories/foundations/connectivity.v)
      is stated with the UNDIRECTED [uwalk] of GTBase.base ([ueseparates]), so
      it is the textbook "no cut edge". Under the previous DIRECTED reading
      (coq-graph-theory's [eseparates] over [walk]) every arc u -> v needed an
      alternative DIRECTED route u -> ... -> v, which forced out-degree at least
      2 at the tail and in-degree at least 2 at the head of every non-loop edge,
      so no snark was in the hypothesis class although the source's own evidence
      is "verified for all cyclically 4-edge-connected snarks up to 34
      vertices". Witnesses of the repaired notion:
      [grounding_X212.x212_bridgeless_Tri] (the cyclically oriented triangle IS
      bridgeless) and [grounding_X212.x212_not_bridgeless_G1] (a genuine cut
      edge IS a bridge). The corpus edge e174 of implications_X228.v is
      unaffected in form - its proof never unfolds [bridgeless], it only passes
      the hypothesis to [five_flow_statement] (D1.v), which now carries the same
      repaired hypothesis.
      UNBLOCKED (second-reader re-read, 2026-09-23): confirmed by independent
      back-translation. The row is also immune to the LOOP defect that keeps
      [bm-026] blocked ([connectivity.subdeg] counts a loop once, so a single
      loop is not an [even_subgraph]): the conclusion here is about integer
      flows, and on the one-vertex one-loop multigraph every weighting is
      [iconservative] (the loop sits on both sides of Kirchhoff), so
      [phi2 = 0], [phi4 = 2] satisfies it. PASS. See
      meta/X211-X229_faithfulness_audit.md and
      meta/STATEMENT_IMPROVEMENTS.md. *)
Definition half_flow_pair_statement : Prop :=
  forall G : mgraph,
    (0 < #|edge G|)%N -> bridgeless G -> x228_half_flow_pair G.
