(** * Hypergraph.foundations.hypergraph_ramsey -- attained Ramsey numbers of a supplied hypergraph

    Library migration D10 (registry entry [ramsey-number], class [hypergraph-attained-forcing-minimum];
    report meta/migration_reports/ramsey_number.md; record meta/LIBRARY_MIGRATION_D10.md; public client
    theories/examples/ramsey_numbers.v).

    [hg_ramsey_number E C R]: [R] is the least host size forcing a monochromatic copy of the pattern
    [E : {set {set T}}] under the palette [C : Type].  It is attained, [hg_forces_mono E 'I_R C] (D5), and
    minimal, every forcing host size [N] has [R <= N].  [R] is supplied: no existence theorem, choice or
    minimum extraction.  The pattern carrier, family and palette are arbitrary, with no uniformity,
    nonempty-family, inhabited-palette or positivity guard.  With an empty palette every host forces
    vacuously, so the minimum is 0.  With a colour and the empty family the whole carrier must still
    inject, so the minimum is [#|T|].  The degree of the Ramsey number is unique.

    Axiom-free: no Axiom/Parameter/Admitted. *)
From GTBase Require Import base.
From Hypergraph.foundations Require Import hypergraph_copies hypergraph_forcing.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition hg_ramsey_number (T : finType) (E : {set {set T}}) (C : Type) (R : nat) : Prop :=
  hg_forces_mono E 'I_R C /\ forall N : nat, hg_forces_mono E 'I_N C -> R <= N.

Section Ramsey.
Variables (T : finType) (C : Type).
Implicit Types (E : {set {set T}}).

(** Attainment and minimality. *)
Lemma hg_ramsey_number_forces E R : hg_ramsey_number E C R -> hg_forces_mono E 'I_R C.
Proof. by case. Qed.

Lemma hg_ramsey_number_min E R N : hg_ramsey_number E C R -> hg_forces_mono E 'I_N C -> R <= N.
Proof. by case=> _; apply. Qed.

(** The Ramsey number is unique. *)
Lemma hg_ramsey_number_uniq E R1 R2 : hg_ramsey_number E C R1 -> hg_ramsey_number E C R2 -> R1 = R2.
Proof. by move=> [f1 m1] [f2 m2]; apply/eqP; rewrite eqn_leq (m1 _ f2) (m2 _ f1). Qed.

(** An empty palette: every host forces vacuously, so the minimum is 0. *)
Lemma hg_ramsey_number_empty_palette E R : (C -> False) -> hg_ramsey_number E C R <-> R = 0.
Proof.
move=> C0; split=> [[_ m]|->].
  by apply/eqP; rewrite -leqn0; apply: m; exact: hg_forces_mono_empty_palette.
by split=> [|N _]; first exact: hg_forces_mono_empty_palette.
Qed.

(** With a colour, the empty family is forced exactly by the hosts into which the whole carrier injects. *)
Lemma hg_forces_mono_set0 (c0 : C) N : hg_forces_mono (set0 : {set {set T}}) 'I_N C <-> #|T| <= N.
Proof.
split=> [/(hg_forces_mono_card c0)|TN col]; first by rewrite card_ord.
apply/hg_mono_copy0; exists (fun x => widen_ord TN (enum_rank x)).
by move=> x y /(congr1 val) /= /val_inj /enum_rank_inj.
Qed.

Lemma hg_ramsey_number_set0 (c0 : C) R : hg_ramsey_number (set0 : {set {set T}}) C R <-> R = #|T|.
Proof.
split=> [[F m]|->].
  have TR : #|T| <= R by apply/(hg_forces_mono_set0 c0).
  have RT : R <= #|T| by apply: m; apply/(hg_forces_mono_set0 c0).
  by apply/eqP; rewrite eqn_leq RT TR.
split; first by apply/(hg_forces_mono_set0 c0).
by move=> N /(hg_forces_mono_set0 c0).
Qed.

End Ramsey.
