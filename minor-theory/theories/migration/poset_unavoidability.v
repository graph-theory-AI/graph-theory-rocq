(** C21: X228 poset unavoidability, frozen at the fixed C20 pin
    97605ddae838bc6e84b0602240148246e9d065f2.
    - [Legacy]: the helper [x228_unavoidable] verbatim; the live helper now unfolds to
      [Minor.foundations.poset_unavoidability.poset_unavoidable H], the same body.
    - [X228Legacy]: the whole BLOCKED row over the frozen helper.  Its implication to
      planarity and treewidth at most three is the existing Kelly-construction
      placeholder consequence, kept exactly; no converse, construction or status
      change is made here.
    There is no earlier frozen history for this helper or row. *)
From GTBase Require Import base.
From GraphTheory Require Import minor.
From Minor.foundations Require Import containment width_params poset_unavoidability.
From Minor.conjectures Require Import X228.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Legacy.

Definition x228_unavoidable (H : sgraph) : Prop :=
  exists d : nat,
    forall P : finite_poset,
      ~ poset_dimension_at_most P d -> minor (poset_cover_graph P) H.

End Legacy.

Module X228Legacy.

Definition unavoidable_minor_kelly_construction_statement : Prop :=
  forall H : sgraph, Legacy.x228_unavoidable H -> wagner_planar H /\ tw_le H 3.

End X228Legacy.

Lemma x228_unavoidable_compat (H : sgraph) :
  Legacy.x228_unavoidable H <-> x228_unavoidable H.
Proof. exact: iff_refl. Qed.

Lemma unavoidable_minor_kelly_construction_statement_compat :
  X228Legacy.unavoidable_minor_kelly_construction_statement <->
  unavoidable_minor_kelly_construction_statement.
Proof.
split=> st H hu.
- exact: st H (proj2 (x228_unavoidable_compat H) hu).
- exact: st H (proj1 (x228_unavoidable_compat H) hu).
Qed.
