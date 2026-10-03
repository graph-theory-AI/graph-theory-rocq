(** Frozen C7 source and complete statement declarations; baseline and exact substitutions
    are recorded in meta/migration_reports/bipartition.spec.json. *)
From GTBase Require Import base.
From Hom.conjectures Require Import U3.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module U3Legacy.

Definition bipartite_rel (G : sgraph) (r : rel G) : Prop :=
  exists f : G -> bool, forall x y : G, r x y -> f x != f y.

Definition weak_pentagon_statement : Prop :=
  forall G : sgraph, regular G 3 -> triangle_free G ->
    exists col : G -> G -> 'I_5,
      (forall x y : G, col x y = col y x) /\
      forall c : 'I_5,
        @U3Legacy.bipartite_rel G (fun x y => (x -- y) && (col x y != c)).

End U3Legacy.

Lemma bipartite_rel_compat (G : sgraph) (r : rel G) :
  U3Legacy.bipartite_rel r = bipartite_rel r.
Proof. by []. Qed.
Lemma weak_pentagon_statement_compat :
  U3Legacy.weak_pentagon_statement <-> weak_pentagon_statement.
Proof. exact: iff_refl. Qed.
