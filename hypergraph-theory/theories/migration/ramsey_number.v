(** * D10: attained Ramsey numbers of a supplied hypergraph, Hypergraph certificate

    Frozen at the D9 pin eae6c3ae123de43cad5ac0675ee25ab3f48c7b10, the family baseline of
    meta/migration_reports/ramsey_number.spec.json.
    - [X117RamseyLegacy]: X117's [x117_ramsey_number] (forcing at [R] and minimality, with the live D5
      forcing and D7 hedgehog aliases) and the complete current hedgehog row over it.
    - [X119RamseyLegacy]: X119's [x119_ramsey_number] (live D5 forcing) and the complete current tower row
      over it, with the live D1 uniformity, the no-isolated guard and the opaque [x119_sqrt].
    Both sources now unfold to the public [Hypergraph.foundations.hypergraph_ramsey.hg_ramsey_number],
    with the same carrier, family and palette ([bool] for X117, ['I_q] for X119).  The complete histories
    are the existing deepest Originals, reused unchanged: D7 [X117HedgehogOriginal] and D3
    [X119ImageOriginal], with their raw constructor/image/copy/forcing/minimum chains and D1 uniformity. *)
From GTBase Require Import base.
Require Hypergraph.foundations.hypergraph_ramsey.
Require Hypergraph.conjectures.X117 Hypergraph.conjectures.X119.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module X117RamseyLegacy.
Import Hypergraph.conjectures.X117.

Definition x117_ramsey_number (t R : nat) : Prop :=
  x117_forces_mono (x117_edges t) R /\
  forall N : nat, x117_forces_mono (x117_edges t) N -> R <= N.

Definition conlon_fox_rodl_hedgehog_ramsey_statement : Prop :=
  forall e1 e2 : nat,
    0 < e1 -> 0 < e2 ->
    exists t0 : nat,
      forall t R : nat,
        t0 <= t ->
        X117RamseyLegacy.x117_ramsey_number t R ->
        t ^ (2 * e2 - e1) <= R ^ e2 /\ R ^ e2 <= t ^ (2 * e2 + e1).

End X117RamseyLegacy.

Module X119RamseyLegacy.
Import Hypergraph.conjectures.X119.

Definition x119_ramsey_number
    (T : finType) (E : {set {set T}}) (q R : nat) : Prop :=
  x119_forces_mono E q R /\
  forall N : nat, x119_forces_mono E q N -> R <= N.

Definition conlon_fox_sudakov_three_uniform_ramsey_tower_statement : Prop :=
  forall q : nat,
    2 <= q ->
    exists cq : nat,
      forall (T : finType) (E : {set {set T}}),
        x119_uniform E 3 ->
        x119_no_isolated E ->
        forall R : nat,
          X119RamseyLegacy.x119_ramsey_number E q R ->
          R <= 2 ^ (2 ^ (cq * x119_sqrt #|E|)).

End X119RamseyLegacy.

(** All four bridges are conversions: the live Ramsey numbers unfold to the same forcing-at-R and minimality conjunction. *)

Lemma x117_ramsey_number_compat (t R : nat) :
  X117RamseyLegacy.x117_ramsey_number t R <->
  Hypergraph.conjectures.X117.x117_ramsey_number t R.
Proof. exact: iff_refl. Qed.

Lemma conlon_fox_rodl_hedgehog_ramsey_statement_compat :
  X117RamseyLegacy.conlon_fox_rodl_hedgehog_ramsey_statement <->
  Hypergraph.conjectures.X117.conlon_fox_rodl_hedgehog_ramsey_statement.
Proof. exact: iff_refl. Qed.

Lemma x119_ramsey_number_compat (T : finType) (E : {set {set T}}) (q R : nat) :
  @X119RamseyLegacy.x119_ramsey_number T E q R <->
  @Hypergraph.conjectures.X119.x119_ramsey_number T E q R.
Proof. exact: iff_refl. Qed.

Lemma conlon_fox_sudakov_three_uniform_ramsey_tower_statement_compat :
  X119RamseyLegacy.conlon_fox_sudakov_three_uniform_ramsey_tower_statement <->
  Hypergraph.conjectures.X119.conlon_fox_sudakov_three_uniform_ramsey_tower_statement.
Proof. exact: iff_refl. Qed.
