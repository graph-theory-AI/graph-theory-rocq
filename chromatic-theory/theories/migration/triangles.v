(** A19 triangles (chromatic): X69's frozen cardinality-first triangle, its distance chain and the Havel row.
    Baseline, hashes and exact substitutions are recorded in meta/migration_reports/triangles.spec.json.
    - [Legacy]: X69's [#|T| = 3 /\ clique T] equals [GTBase.triangles.triangle T] (clique first) by
      [triangle_card_firstE], an iff (the conjunction order differs), not a conversion.
    - [X69Legacy]: the chain and the row over the frozen triangle: one positive d before all planar graphs, all pairs
      of distinct triangles and vertices, the ball of radius d.-1.  X69 has no older frozen history, so this row is
      also its complete row. *)
From Corelib Require Import Setoid Morphisms.
From GTBase Require Import base triangles.
From Chromatic.conjectures Require Import X69.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Legacy.

Definition x69_triangle (G : sgraph) (T : {set G}) : Prop :=
  #|T| = 3 /\ clique T.

End Legacy.

Module X69Legacy.

Definition x69_triangles_distance_at_least (G : sgraph) (d : nat) : Prop :=
  forall A B : {set G},
    Legacy.x69_triangle A ->
    Legacy.x69_triangle B ->
    A != B ->
    forall a b : G, a \in A -> b \in B -> b \notin ball d.-1 a.

Definition havel_distant_triangles_three_colourable_statement : Prop :=
  exists d : nat,
    0 < d /\
    forall G : sgraph,
      wagner_planar G ->
      X69Legacy.x69_triangles_distance_at_least G d ->
      χ([set: G]) <= 3.

End X69Legacy.

(** Not a conversion: the cardinality-first conjunction against the clique-first canonical. *)
Lemma x69_triangle_compat (G : sgraph) (T : {set G}) :
  Legacy.x69_triangle T <-> x69_triangle T.
Proof.
exact: (iff_sym (triangle_card_firstE T)).
Qed.

Lemma x69_triangles_distance_at_least_compat (G : sgraph) (d : nat) :
  X69Legacy.x69_triangles_distance_at_least G d <-> x69_triangles_distance_at_least G d.
Proof.
rewrite /X69Legacy.x69_triangles_distance_at_least /x69_triangles_distance_at_least.
setoid_rewrite x69_triangle_compat.
reflexivity.
Qed.

Lemma havel_distant_triangles_three_colourable_statement_compat :
  X69Legacy.havel_distant_triangles_three_colourable_statement <->
  havel_distant_triangles_three_colourable_statement.
Proof.
rewrite /X69Legacy.havel_distant_triangles_three_colourable_statement /havel_distant_triangles_three_colourable_statement.
setoid_rewrite x69_triangles_distance_at_least_compat.
reflexivity.
Qed.
