(** * Topological.conjectures.X103 -- v2 simultaneous embeddability row *)

From Stdlib Require Import ZArith.
From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Open Scope Z_scope.

(** ** Local X103 vocabulary ***********************************************)

Definition x103_point := (Z * Z)%type.

Definition x103_px (p : x103_point) : Z :=
  match p with (x, _) => x end.

Definition x103_py (p : x103_point) : Z :=
  match p with (_, y) => y end.

Definition x103_cross (a b c : x103_point) : Z :=
  (x103_px b - x103_px a) * (x103_py c - x103_py a) -
  (x103_py b - x103_py a) * (x103_px c - x103_px a).

Definition x103_between_coord (a b c : Z) : Prop :=
  (a <= c <= b) \/ (b <= c <= a).

Definition x103_on_segment (a b c : x103_point) : Prop :=
  x103_cross a b c = 0 /\
  x103_between_coord (x103_px a) (x103_px b) (x103_px c) /\
  x103_between_coord (x103_py a) (x103_py b) (x103_py c).

Definition x103_opposite_or_zero (a b : Z) : Prop :=
  (a <= 0 <= b) \/ (b <= 0 <= a).

Definition x103_segments_intersect
    (a b c d : x103_point) : Prop :=
  (x103_opposite_or_zero (x103_cross a b c) (x103_cross a b d) /\
   x103_opposite_or_zero (x103_cross c d a) (x103_cross c d b)) \/
  x103_on_segment a b c \/ x103_on_segment a b d \/
  x103_on_segment c d a \/ x103_on_segment c d b.

Definition x103_crossing_free_drawing
    (G : sgraph) (place : G -> x103_point) : Prop :=
  injective place /\
  forall x y u v : G,
    x -- y ->
    u -- v ->
    [&& x != u, x != v, y != u & y != v] ->
    ~ x103_segments_intersect (place x) (place y) (place u) (place v).

Definition x103_same_point_set
    (G H : sgraph) (placeG : G -> x103_point) (placeH : H -> x103_point)
    : Prop :=
  (forall x : G, exists y : H, placeG x = placeH y) /\
  forall y : H, exists x : G, placeH y = placeG x.

Definition x103_common_point_set_embedding (G H : sgraph) : Prop :=
  exists (placeG : G -> x103_point) (placeH : H -> x103_point),
    x103_crossing_free_drawing placeG /\
    x103_crossing_free_drawing placeH /\
    x103_same_point_set placeG placeH.

Definition x103_simultaneously_embeddable (G H : sgraph) : Prop :=
  x103_common_point_set_embedding G H.

(** ** X103 statements *****************************************************)

(** Corpus row: studies:std_brass_et_al_simultaneous_embeddability_problem
    Site: none
    Review: none
    English statement: (Brass, Cenek, Duncan, Efrat, Erten, Ismailescu, Kobourov, Lubiw,
      Mitchell 2007, "simultaneous embeddability problem", studies slice)
      Is there a pair of planar graphs of the same order that is not simultaneously
      embeddable?  The Rocq body asserts it positively: there exist two finite simple graphs
      G and H, both with no K5 and no K3,3 minor, with the same number of vertices, such that
      G and H have no simultaneous straight-line embedding on a common point set.
    Definitions: [x103_point] - a pair of integers, i.e. a point with integer coordinates
      (this file); [x103_cross], [x103_on_segment], [x103_segments_intersect] - the standard
      orientation-determinant tests for two CLOSED segments meeting, including the collinear
      overlap cases (this file); [x103_crossing_free_drawing G place] - [place] is injective
      and no two edges with four distinct endpoints have intersecting segments (this file);
      [x103_same_point_set] - the two placements have the same image (this file);
      [x103_simultaneously_embeddable G H] - both graphs have a crossing-free straight-line
      drawing on one and the same point set (this file); [wagner_planar] -
      base/theories/base.v.
    Notes: PROXY choices.  (1) Points have INTEGER coordinates; the source speaks of the real
      plane.  Restricting to the integer grid is harmless for the positive direction (a
      simultaneous embedding on the reals can be perturbed to a rational, hence integer,
      one), but the statement asserted here is the NEGATIVE one, so the integer restriction
      makes it a priori WEAKER than the source question: a pair with no integer common point
      set could still have a real one.  (2) The crossing-free condition only forbids
      intersections between edges with four DISTINCT endpoints, so a vertex lying in the
      interior of a non-incident edge is not forbidden (unlike
      [geometry.straightline_planar], which does forbid it).  (3) "Same order" is written
      with [Nat.eq] on the cardinalities.  (4) This file duplicates the segment-intersection
      vocabulary of topological-graph-theory/theories/foundations/geometry.v over Z instead
      of reusing it over an [rcfType]; see the ledger. *)
Definition two_planar_graphs_not_simultaneously_embeddable_statement : Prop :=
  exists G H : sgraph,
    [/\ wagner_planar G,
        wagner_planar H,
        Nat.eq #|G| #|H|
      & ~ x103_simultaneously_embeddable G H].
