(** * Digraph.conjectures.X216 -- Bondy-Murty Appendix A digraph rows (wave X216, 2026-09-23) *)

From HB Require Import structures.
From mathcomp Require Import all_boot.
From mathcomp Require Import all_algebra.
From Digraph Require Import prelude digraph oriented dipath strong.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.

(** ** Local x216 vocabulary ***********************************************

    Arc weights.  Neither coq-graph-theory, nor [GTBase.base]/[GTBase.common],
    nor the package foundations carry weighted arcs on a [diGraphType]; the
    closest neighbours are [GTBase.dom]'s vertex weights (undirected) and
    [unvd.v]'s rational [density].  Following the [unvd.v] precedent we take
    weights in [rat] (the corpus text says "positive weight function"; every
    real weighting can be replaced by a rational one for the purpose of the
    two inequalities below -- see the [Notes:] of the statement).

    A weight function is a plain [w : D -> D -> rat]; only its values on ARCS
    are ever read ([x216_win]/[x216_wout]/[x216_cycle_weight] sum over arcs
    and over consecutive pairs of a directed cycle, which are arcs). *)

(** [x216_win w v] = w^-(v), the total weight of the arcs entering [v]. *)
Definition x216_win (D : diGraphType) (w : D -> D -> rat) (v : D) : rat :=
  \sum_(u : D | u --> v) w u v.

(** [x216_wout w v] = w^+(v), the total weight of the arcs leaving [v]. *)
Definition x216_wout (D : diGraphType) (w : D -> D -> rat) (v : D) : rat :=
  \sum_(u : D | v --> u) w v u.

(** The weight of a directed cycle [c] (a [dicycle] of core/dipath.v: a
    nonempty duplicate-free vertex sequence which is a [cycle] for the arc
    relation): the sum of [w z (next c z)] over its vertices, i.e. the sum of
    the weights of its arcs, each arc taken once. *)
Definition x216_cycle_weight (D : diGraphType) (w : D -> D -> rat)
    (c : seq D) : rat :=
  \sum_(z <- c) w z (next c z).

(** ** X216 statements *****************************************************)

(** Corpus row: bm:bm-070
    Site: https://graph-theory-ai.github.io/graph-conjectures/bm/bm-070/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/bondy_murty_reviews/bm-070.json
    English statement: (Bondy and Murty, Graph Theory, Appendix A, unsolved problem 70,
      weighted Caccetta-Haggkvist conjecture, after Bollobas and Scott)
      Let D be a finite digraph with at least one vertex and no loops, and let w assign a
      rational weight to every ordered pair of vertices, positive on every arc. If D is
      strongly connected and, for every vertex v, the total weight of the arcs entering v is
      at least 1 and the total weight of the arcs leaving v is at least 1, then D has a
      directed cycle the sum of whose arc weights is at least 1.
    Definitions: [x216_win w v] and [x216_wout w v] - the total weight of the arcs entering
      resp. leaving v (this file); [x216_cycle_weight w c] - the sum of w over the arcs of the
      directed cycle c, written as the sum of w z (next c z) over the vertices z of c (this
      file); [strongb] - strong connectivity, every vertex reaches every other along arcs
      (invariants/strong.v); [dicycle c] - c is a nonempty duplicate-free vertex sequence
      that is a directed cycle (core/dipath.v).
    Notes: Three modelling choices. (1) Weights are RATIONAL, not real: the hypotheses and
      the conclusion are finitely many linear inequalities with rational data on the
      unknowns, and a real weighting satisfying them can be perturbed to a rational one, so
      the two readings agree; this follows the rational convention of conjectures/unvd.v.
      (2) The looplessness guard is LOAD-BEARING and is the "digraph" of the source read as
      loopless: with loops allowed the statement is FALSE, witnessed by two vertices u, v
      carrying a loop of weight 3/4 each and the two arcs u->v, v->u of weight 1/4 each --
      every vertex then has w^- = w^+ = 1 and the digraph is strongly connected, yet the
      three directed cycles have weights 3/4, 3/4 and 1/2, all below 1 (see
      [x216_loopless_guard_has_teeth] in grounding_X216.v). (3) The guard 0 < #|D| is also
      load-bearing: the empty digraph is vacuously strongly connected and satisfies every
      degree hypothesis but has no directed cycle at all. Second-reader readback 2026-09-23:
      choice (1) holds in the direction that matters -- the hypotheses are closed and the
      negated conclusion is open, so a REAL counterexample perturbs upwards to a rational one
      (any rational w' >= w close enough to w keeps w'^- , w'^+ >= 1 and all cycle weights
      below 1) -- and (2) and (3) are confirmed. One residual, deliberate gap: [diGraphType]
      carries no parallel arcs, so the statement quantifies over SIMPLE loopless digraphs;
      merging parallel arcs only raises cycle weights, so a multi-arc counterexample need not
      survive the merge, and in that (corpus-wide) sense the encoding is marginally weaker
      than a multigraph reading of "digraph". *)
Definition weighted_caccetta_haggkvist_statement : Prop :=
  forall (D : diGraphType) (w : D -> D -> rat),
    (0 < #|D|)%N ->
    (forall v : D, ~~ (v --> v)) ->
    strongb D ->
    (forall u v : D, u --> v -> 0 < w u v) ->
    (forall v : D, 1 <= x216_win w v) ->
    (forall v : D, 1 <= x216_wout w v) ->
    exists c : seq D, dicycle c /\ 1 <= x216_cycle_weight w c.
