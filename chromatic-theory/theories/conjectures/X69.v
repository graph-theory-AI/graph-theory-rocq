(** * Chromatic.conjectures.X69 -- v2 Havel problem row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X69 vocabulary ************************************************)

Definition x69_triangle (G : sgraph) (T : {set G}) : Prop :=
  #|T| = 3 /\ clique T.

Definition x69_triangles_distance_at_least (G : sgraph) (d : nat) : Prop :=
  forall A B : {set G},
    x69_triangle A ->
    x69_triangle B ->
    A != B ->
    forall a b : G, a \in A -> b \in B -> b \notin ball d.-1 a.

(** ** X69 statements ******************************************************)

(** Corpus row: studies:std_havel_s_problem
    Site: none
    Review: none
    English statement: (Havel, studies slice of the corpus)
      There is a constant d > 0 such that every planar finite simple graph in which any two distinct
      triangles are at distance at least d has chromatic number at most 3.
    Definitions: [x69_triangle T] - T is a 3-element clique (this file);
      [x69_triangles_distance_at_least G d] - for any two distinct triangles and any vertices a in
      one and b in the other, b is not within distance d-1 of a (this file); [ball], [wagner_planar]
      (GTBase base/theories/base.v).
    Notes: This row has no site or review page in the corpus, hence the literal "none" above. The
      corpus row is a QUESTION; the Rocq body is its affirmative reading. The distance condition is
      imposed on every pair of vertices of two distinct triangles, which is the intended reading of
      "the distance between the two triangles is at least d". *)
Definition havel_distant_triangles_three_colourable_statement : Prop :=
  exists d : nat,
    0 < d /\
    forall G : sgraph,
      wagner_planar G ->
      x69_triangles_distance_at_least G d ->
      χ([set: G]) <= 3.
