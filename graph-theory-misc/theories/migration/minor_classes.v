(** * C11: exact excluded-minor and minor-closure contracts
    Frozen at 6e1a1c4. X192 has a witness ONLY; X168 additionally closes under
    minors. Complete row guards, quantifier order and documented defects stay. *)
From GTBase Require Import base minor_classes.
From GTMisc.conjectures Require Import X168.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Legacy.

Definition x168_proper_minor_closed_class (C : sgraph -> Prop) : Prop :=
  (exists H : sgraph, forall G : sgraph, C G -> ~ minor G H) /\
  forall G H : sgraph, C G -> minor G H -> C H.

Definition minor_closed_spanning_tree_polytope_linear_xc_statement : Prop :=
  forall C : sgraph -> Prop,
    Legacy.x168_proper_minor_closed_class C ->
    exists K : nat,
      forall G : sgraph,
        C G ->
        connected [set: G] ->
        x168_spanning_tree_polytope_xc G (K * #|G|.+1).

End Legacy.

Lemma x168_proper_minor_closed_class_compat (C : sgraph -> Prop) :
  Legacy.x168_proper_minor_closed_class C <-> x168_proper_minor_closed_class C.
Proof. by []. Qed.

Lemma minor_closed_spanning_tree_polytope_linear_xc_statement_compat :
  Legacy.minor_closed_spanning_tree_polytope_linear_xc_statement <->
  minor_closed_spanning_tree_polytope_linear_xc_statement.
Proof. by []. Qed.
