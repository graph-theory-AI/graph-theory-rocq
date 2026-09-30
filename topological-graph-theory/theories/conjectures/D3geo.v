(** * D3 metric-geometry rows landed via the finite-geometry foundation.

    Track-A metric-geometry preflight outcome: the one row justifying a small
    finite-geometry primitive (the [orient] determinant sign) is
    small_universal_point_sets — a faithful finite/combinatorial encoding over
    an abstract ordered field (points as a [seq], straight-line crossing via
    [orient], planarity via base [wagner_planar]).  The great-circle,
    surface-drawing and obstacle-number rows stay BLOCKED (genuine spherical /
    continuous / arbitrary-closed-set geometry). *)

From GTBase Require Export base.
From mathcomp Require Import all_algebra.
From Topological.foundations Require Import geometry.
Import GRing.Theory Num.Theory.
Set Implicit Arguments.
Unset Strict Implicit.

(** Corpus row: opg:small_universal_point_sets_for_planar_graphs
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/small_universal_point_sets_for_planar_graphs/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/small_universal_point_sets_for_planar_graphs.json
    English statement: (Open Problem Garden, "Universal point sets for planar graphs")
      A set P of points of the plane is n-universal when every n-vertex planar graph can be
      drawn with each vertex at a distinct point of P and every edge a non-crossing straight
      line segment; the question is whether there is an n-universal set of size O(n).  The
      Rocq body asserts it positively, and over every real-closed field R: there is a
      constant c such that for every n some list P of points of R x R has length at most
      c * n and is n-universal.
    Definitions: [pt R] - a point, i.e. a pair of elements of R
      (topological-graph-theory/theories/foundations/geometry.v); [n_universal P n] - every
      graph with no K5 and no K3,3 minor on exactly n vertices has a straight-line planar
      drawing all of whose vertex positions lie in P (same file);
      [straightline_planar pos] - [pos] is injective, no vertex lies between the endpoints of
      a non-incident edge, and no two vertex-disjoint edges share ANY point of their closed
      segments (same file, via the [orient] determinant sign); [wagner_planar] - planarity as
      no K5 and no K3,3 minor (base/theories/base.v).
    Notes: FAITHFUL finite/combinatorial encoding; the only modelling choices are these.
      (1) The field is quantified as [forall R : rcfType] rather than fixed to the reals: for
      each fixed pair (c,n) the body is a first-order sentence in the language of ordered
      fields (finitely many graphs, [orient]-sign atoms), so by Tarski-Seidenberg it has the
      same truth value in every real-closed field, and the outer arithmetic quantifiers agree
      too - a proof and a disproof both transfer to R = the reals.  A bare [realFieldType]
      quantifier would range over non-real-closed fields such as the rationals and be a
      priori strictly stronger.  (2) Non-crossing is the FULL closed-segment test
      ([seg_meet]), not merely a proper crossing.  (3) No general-position side condition is
      imposed, matching the source (grids are universal candidates but are not in general
      position).  (4) "O(n)" is one constant c uniform in n, with c allowed to depend on R.
      The great-circle, surface-drawing and obstacle-number rows of the same milestone stay
      blocked in D3D6_unblocked.v because their geometry is spherical/continuous/arbitrary
      closed sets rather than straight-line. *)
Definition small_universal_point_sets_for_planar_graphs_statement : Prop :=
  forall R : rcfType,
    exists c : nat,
      forall n : nat,
        exists P : seq (pt R),
          (size P <= c * n)%N /\ n_universal P n.
