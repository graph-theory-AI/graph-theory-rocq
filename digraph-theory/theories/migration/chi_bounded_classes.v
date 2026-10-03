(** * C9: frozen ordinary chi-boundedness and complete statements
    Originals are pinned at 0659592. All guards, class quantifiers and status
    discrepancies stay unchanged; only the recorded references use frozen
    dependencies. The A6 Original composes the existing frozen complement. *)
From GTBase Require Import base chi_bounding.
From Digraph Require Import prelude interop_graph_theory digraph oriented tournament dipath dichromatic heroes.
From Digraph.conjectures Require Import chi_bounded.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Legacy.

Definition chi_bounded_under (C : diGraphType -> Prop) : Prop :=
  exists f : nat -> nat,
    forall G : diGraphType,
      C G -> (0 < #|G|)%N ->
      (χ([set: underlying G]) <= f (ω([set: underlying G])))%N.

Definition conj2_1605_statement : Prop :=
  forall H : diGraphType,
    oriented_dg H ->
    ( Legacy.chi_bounded_under (fun G => oriented_dg G /\ ind_free H G)
      <-> oriented_forest H ).

Definition conj4_1605_statement : Prop :=
  forall S : diGraphType,
    oriented_star S ->
    Legacy.chi_bounded_under (fun G => oriented_dg G /\ ind_free S G).

Definition conj5_1605_statement : Prop :=
  forall forb : diGraphType -> Prop,
    (forall P : diGraphType, forb P -> P4_underlying P) ->
    (exists P : diGraphType, forb P) ->
    (exists P : diGraphType, forb P /\ ~ is_dirP4 P /\ ~ is_altP4 P) ->
    Legacy.chi_bounded_under (fun G => oriented_dg G /\ Forb_ind forb G).

End Legacy.

(** The positive-order guard stays inside the supplied class adapter. *)
Lemma chi_bounded_under_compat (F : diGraphType -> Prop) :
  Legacy.chi_bounded_under F <-> chi_bounded_under F.
Proof.
split=> -[f hf]; exists f.
- by move=> G [FG nonempty]; exact: hf G FG nonempty.
- move=> G FG nonempty; apply: hf; by split.
Qed.

Lemma conj2_1605_statement_compat :
  Legacy.conj2_1605_statement <-> conj2_1605_statement.
Proof.
split=> h H oriented; have [forward backward] := h H oriented; split.
- move=> bounded; apply: forward; by apply/chi_bounded_under_compat.
- move=> forest; apply/chi_bounded_under_compat; exact: backward forest.
- move=> bounded; apply: forward; by apply/chi_bounded_under_compat.
- move=> forest; apply/chi_bounded_under_compat; exact: backward forest.
Qed.

Lemma conj4_1605_statement_compat :
  Legacy.conj4_1605_statement <-> conj4_1605_statement.
Proof.
split=> h S star; have bounded := h S star.
all: by apply/chi_bounded_under_compat.
Qed.

Lemma conj5_1605_statement_compat :
  Legacy.conj5_1605_statement <-> conj5_1605_statement.
Proof.
split=> h forb paths inhabited nonexceptional;
  have bounded := h forb paths inhabited nonexceptional.
all: by apply/chi_bounded_under_compat.
Qed.
