(** * GTMisc.migration.orientations — D11 certificates: X82's proper-orientation vocabulary and the X82 and X101 rows

    Frozen verbatim at the B29 pin e681570, references between the frozen helpers qualified [Legacy.]: X82's
    [x82_orientation_of G D] (arcs only between adjacent vertices and exactly one direction per edge,
    [D x y (+) D y x]), [x82_indegree D v] (the vertices sending an arc to [v]), [x82_proper_orientation D] (adjacent
    vertices have different indegrees; no orientation asserted), [x82_proper_orientation_bound G k] (one [D] with the
    three conjuncts in this order) and two complete rows over the bound: X82's
    [outerplanar_bounded_proper_orientation_number_statement] (one [C] before every [G], under X82's unchanged
    forbidden-minor guard [x82_outerplanar]) and X101's [planar_bounded_proper_orientation_number_statement] (one [C]
    before every [G], under the unchanged [wagner_planar] guard, through X101's import of X82).  The guards stay live
    and are not migrated here.  Since D11 the four helpers are GTBase.orientations' [orientation_of], [rel_indegree],
    [proper_indegrees] and [proper_orientation_bound], the same bodies by conversion, so all six certificates below
    are kernel-checked conversions.  No earlier migration snapshot reaches these declarations. *)

From GTBase Require Import base orientations.
From GTMisc.conjectures Require Import X82 X101.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Legacy.

Definition x82_orientation_of (G : sgraph) (D : rel G) : Prop :=
  (forall x y : G, D x y -> x -- y) /\
  forall x y : G, x -- y -> (D x y) (+) (D y x).

Definition x82_indegree (G : sgraph) (D : rel G) (v : G) : nat :=
  #|[set u : G | D u v]|.

Definition x82_proper_orientation (G : sgraph) (D : rel G) : Prop :=
  forall x y : G, x -- y -> Legacy.x82_indegree D x != Legacy.x82_indegree D y.

Definition x82_proper_orientation_bound (G : sgraph) (k : nat) : Prop :=
  exists D : rel G,
    Legacy.x82_orientation_of D /\
    Legacy.x82_proper_orientation D /\
    forall v : G, Legacy.x82_indegree D v <= k.

End Legacy.

Module X82Legacy.

Definition outerplanar_bounded_proper_orientation_number_statement : Prop :=
  exists C : nat,
    forall G : sgraph,
      x82_outerplanar G ->
      Legacy.x82_proper_orientation_bound G C.

End X82Legacy.

Module X101Legacy.

Definition planar_bounded_proper_orientation_number_statement : Prop :=
  exists C : nat,
    forall G : sgraph,
      wagner_planar G ->
      Legacy.x82_proper_orientation_bound G C.

End X101Legacy.

Lemma x82_orientation_of_compat (G : sgraph) (D : rel G) :
  Legacy.x82_orientation_of D <-> x82_orientation_of D.
Proof. exact: iff_refl. Qed.

Lemma x82_indegree_compat (G : sgraph) (D : rel G) (v : G) :
  Legacy.x82_indegree D v = x82_indegree D v.
Proof. by []. Qed.

Lemma x82_proper_orientation_compat (G : sgraph) (D : rel G) :
  Legacy.x82_proper_orientation D <-> x82_proper_orientation D.
Proof. exact: iff_refl. Qed.

Lemma x82_proper_orientation_bound_compat (G : sgraph) (k : nat) :
  Legacy.x82_proper_orientation_bound G k <-> x82_proper_orientation_bound G k.
Proof. exact: iff_refl. Qed.

Lemma outerplanar_bounded_proper_orientation_number_statement_compat :
  X82Legacy.outerplanar_bounded_proper_orientation_number_statement <->
  outerplanar_bounded_proper_orientation_number_statement.
Proof. exact: iff_refl. Qed.

Lemma planar_bounded_proper_orientation_number_statement_compat :
  X101Legacy.planar_bounded_proper_orientation_number_statement <->
  planar_bounded_proper_orientation_number_statement.
Proof. exact: iff_refl. Qed.

Print Assumptions x82_orientation_of_compat.
Print Assumptions x82_indegree_compat.
Print Assumptions x82_proper_orientation_compat.
Print Assumptions x82_proper_orientation_bound_compat.
Print Assumptions outerplanar_bounded_proper_orientation_number_statement_compat.
Print Assumptions planar_bounded_proper_orientation_number_statement_compat.
