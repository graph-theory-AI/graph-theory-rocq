(** * GTMisc.conjectures.X101 -- v2 planar proper-orientation row *)

From GTBase Require Export base.
From GTMisc.conjectures Require Import X82.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** X101 statements *****************************************************)

(** Corpus row: studies:std_bounded_proper_orientation_number_of_planar_grap_436
    Site: none
    Review: none
    English statement: (Araujo, Havet, Linhares Sales and Silva, "Bounded proper orientation
      number of planar graphs")
      There is a natural number C such that every planar finite simple graph G admits an
      orientation of its edges in which adjacent vertices have different in-degrees and every
      in-degree is at most C.
    Definitions: [x82_orientation_of G D] - D orients every edge of G exactly one way and
      relates no non-adjacent pair (graph-theory-misc/theories/conjectures/X82.v);
      [x82_indegree D v] - the number of vertices sending an arc to v (same file);
      [x82_proper_orientation D] - adjacent vertices receive distinct in-degrees (same file);
      [x82_proper_orientation_bound G k] - some proper orientation of G has all in-degrees at
      most k, i.e. the proper orientation number of G is at most k (same file);
      [wagner_planar] - combinatorial Wagner planarity, no K5 and no K3,3 minor (GTBase).
    Notes: the source asks which classes have bounded proper orientation number and, in
      particular, whether planar graphs do; the Rocq body is the positive answer for the
      planar case, the constant C being chosen before the graph.  The companion outerplanar
      row is graph-theory-misc/theories/conjectures/X82.v. *)
Definition planar_bounded_proper_orientation_number_statement : Prop :=
  exists C : nat,
    forall G : sgraph,
      wagner_planar G ->
      x82_proper_orientation_bound G C.
