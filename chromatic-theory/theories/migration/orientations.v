(** * Chromatic.migration.orientations — D11 certificates: X81's proper-orientation vocabulary and row

    Frozen verbatim at the B29 pin e681570, references between the frozen helpers qualified [Legacy.]: X81's
    [x81_orientation_of G D] (arcs only between adjacent vertices and exactly one direction per edge,
    [D x y (+) D y x]), [x81_indegree D v] (the vertices sending an arc to [v]), [x81_proper_orientation D] (adjacent
    vertices have different indegrees; no orientation asserted), [x81_proper_orientation_bound G k] (one [D] with the
    three conjuncts in this order) and the complete row [bipartite_proper_orientation_half_delta_constant_statement]
    (some [C] before every bipartite [G], then some [k] with the bound and [2 * k <= Delta G + 2 * C]; [bipartite] and
    [Delta] stay the live GTBase providers).  Since D11 the four helpers are GTBase.orientations' [orientation_of],
    [rel_indegree], [proper_indegrees] and [proper_orientation_bound], the same bodies by conversion, so all five
    certificates below are kernel-checked conversions.  No earlier migration snapshot reaches these declarations. *)

From GTBase Require Import base orientations.
From Chromatic.conjectures Require Import X81.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Legacy.

Definition x81_orientation_of (G : sgraph) (D : rel G) : Prop :=
  (forall x y : G, D x y -> x -- y) /\
  forall x y : G, x -- y -> (D x y) (+) (D y x).

Definition x81_indegree (G : sgraph) (D : rel G) (v : G) : nat :=
  #|[set u : G | D u v]|.

Definition x81_proper_orientation (G : sgraph) (D : rel G) : Prop :=
  forall x y : G, x -- y -> Legacy.x81_indegree D x != Legacy.x81_indegree D y.

Definition x81_proper_orientation_bound (G : sgraph) (k : nat) : Prop :=
  exists D : rel G,
    Legacy.x81_orientation_of D /\
    Legacy.x81_proper_orientation D /\
    forall v : G, Legacy.x81_indegree D v <= k.

End Legacy.

Module X81Legacy.

Definition bipartite_proper_orientation_half_delta_constant_statement : Prop :=
  exists C : nat,
    forall G : sgraph,
      bipartite G ->
      exists k : nat,
        Legacy.x81_proper_orientation_bound G k /\
        2 * k <= Delta G + 2 * C.

End X81Legacy.

Lemma x81_orientation_of_compat (G : sgraph) (D : rel G) :
  Legacy.x81_orientation_of D <-> x81_orientation_of D.
Proof. exact: iff_refl. Qed.

Lemma x81_indegree_compat (G : sgraph) (D : rel G) (v : G) :
  Legacy.x81_indegree D v = x81_indegree D v.
Proof. by []. Qed.

Lemma x81_proper_orientation_compat (G : sgraph) (D : rel G) :
  Legacy.x81_proper_orientation D <-> x81_proper_orientation D.
Proof. exact: iff_refl. Qed.

Lemma x81_proper_orientation_bound_compat (G : sgraph) (k : nat) :
  Legacy.x81_proper_orientation_bound G k <-> x81_proper_orientation_bound G k.
Proof. exact: iff_refl. Qed.

Lemma bipartite_proper_orientation_half_delta_constant_statement_compat :
  X81Legacy.bipartite_proper_orientation_half_delta_constant_statement <->
  bipartite_proper_orientation_half_delta_constant_statement.
Proof. exact: iff_refl. Qed.

Print Assumptions x81_orientation_of_compat.
Print Assumptions x81_indegree_compat.
Print Assumptions x81_proper_orientation_compat.
Print Assumptions x81_proper_orientation_bound_compat.
Print Assumptions bipartite_proper_orientation_half_delta_constant_statement_compat.
