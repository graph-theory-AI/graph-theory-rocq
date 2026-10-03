(** * D4: monochromatic copies of a supplied hypergraph, Hypergraph certificate

    Frozen at the D3 pin 598d668fa9225c8271852c856ce3990c7fa7890e; bindings in
    meta/migration_reports/monochromatic_copy.spec.json.
    - [<Phase>CopyLegacy]: the three copy predicates (bool palette for X108/X117, ['I_q] for X119),
      the five reached forcing/Ramsey chains (forcing over all supplied colourings; both Ramsey
      predicates with forcing AND minimality) and the three complete current rows, verbatim, each
      importing only its own conjecture file.  The live copies are now aliases of
      [Hypergraph.foundations.hypergraph_copies.hg_mono_copy]; these current copies keep the live
      D3 image alias (so they convert to the live predicates), the live D1/A10 vocabulary and
      X119's ceiling square root with its opaque witness.
    The complete raw histories are D3's existing rows (X108ImageOriginal, X119ImageOriginal and
    the complete X117ImageLegacy row in Hypergraph.migration.image_edge), reused through the spec
    with their own certificates; nothing is copied again here. *)
From GTBase Require Import base.
Require Hypergraph.foundations.hypergraph_copies.
Require Hypergraph.conjectures.X108 Hypergraph.conjectures.X117 Hypergraph.conjectures.X119.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module X108CopyLegacy.
Import Hypergraph.conjectures.X108.

Definition x108_monochromatic_copy
    (T : finType) (E : {set {set T}}) (N : nat)
    (col : {set 'I_N} -> bool) : Prop :=
  exists (colour : bool) (f : T -> 'I_N),
    injective f /\
    forall e : {set T},
      e \in E -> col (x108_image_edge f e) = colour.

Definition x108_two_colour_ramsey_at_most
    (T : finType) (E : {set {set T}}) (N : nat) : Prop :=
  forall col : {set 'I_N} -> bool, X108CopyLegacy.x108_monochromatic_copy E col.

Definition three_uniform_degenerate_hypergraph_ramsey_linear_statement : Prop :=
  forall d : nat,
    exists c : nat,
      forall (T : finType) (E : {set {set T}}),
        x108_uniform E 3 ->
        x108_d_degenerate E d ->
        X108CopyLegacy.x108_two_colour_ramsey_at_most E (c * #|T|).

End X108CopyLegacy.

Module X117CopyLegacy.
Import Hypergraph.conjectures.X117.

Definition x117_monochromatic_copy
    (T : finType) (E : {set {set T}}) (N : nat)
    (col : {set 'I_N} -> bool) : Prop :=
  exists (colour : bool) (f : T -> 'I_N),
    injective f /\
    forall e : {set T},
      e \in E -> col (x117_image_edge f e) = colour.

Definition x117_forces_mono
    (T : finType) (E : {set {set T}}) (N : nat) : Prop :=
  forall col : {set 'I_N} -> bool, X117CopyLegacy.x117_monochromatic_copy E col.

Definition x117_ramsey_number (t R : nat) : Prop :=
  X117CopyLegacy.x117_forces_mono (x117_edges t) R /\
  forall N : nat, X117CopyLegacy.x117_forces_mono (x117_edges t) N -> R <= N.

Definition conlon_fox_rodl_hedgehog_ramsey_statement : Prop :=
  forall e1 e2 : nat,
    0 < e1 -> 0 < e2 ->
    exists t0 : nat,
      forall t R : nat,
        t0 <= t ->
        X117CopyLegacy.x117_ramsey_number t R ->
        t ^ (2 * e2 - e1) <= R ^ e2 /\ R ^ e2 <= t ^ (2 * e2 + e1).

End X117CopyLegacy.

Module X119CopyLegacy.
Import Hypergraph.conjectures.X119.

Definition x119_monochromatic_copy
    (T : finType) (E : {set {set T}}) (N q : nat)
    (col : {set 'I_N} -> 'I_q) : Prop :=
  exists (colour : 'I_q) (f : T -> 'I_N),
    injective f /\
    forall e : {set T},
      e \in E -> col (x119_image_edge f e) = colour.

Definition x119_forces_mono
    (T : finType) (E : {set {set T}}) (q N : nat) : Prop :=
  forall col : {set 'I_N} -> 'I_q, X119CopyLegacy.x119_monochromatic_copy E col.

Definition x119_ramsey_number
    (T : finType) (E : {set {set T}}) (q R : nat) : Prop :=
  X119CopyLegacy.x119_forces_mono E q R /\
  forall N : nat, X119CopyLegacy.x119_forces_mono E q N -> R <= N.

Definition conlon_fox_sudakov_three_uniform_ramsey_tower_statement : Prop :=
  forall q : nat,
    2 <= q ->
    exists cq : nat,
      forall (T : finType) (E : {set {set T}}),
        x119_uniform E 3 ->
        x119_no_isolated E ->
        forall R : nat,
          X119CopyLegacy.x119_ramsey_number E q R ->
          R <= 2 ^ (2 ^ (cq * x119_sqrt #|E|)).

End X119CopyLegacy.

(** Every frozen copy unfolds, through the live D3 image alias, to the same term as the live
    alias of [hg_mono_copy]: all eleven bridges are conversions. *)

Lemma x108_monochromatic_copy_compat (T : finType) (E : {set {set T}}) (N : nat)
    (col : {set 'I_N} -> bool) :
  @X108CopyLegacy.x108_monochromatic_copy T E N col <->
  @Hypergraph.conjectures.X108.x108_monochromatic_copy T E N col.
Proof. exact: iff_refl. Qed.

Lemma x108_two_colour_ramsey_at_most_compat (T : finType) (E : {set {set T}}) (N : nat) :
  @X108CopyLegacy.x108_two_colour_ramsey_at_most T E N <->
  @Hypergraph.conjectures.X108.x108_two_colour_ramsey_at_most T E N.
Proof. exact: iff_refl. Qed.

Lemma three_uniform_degenerate_hypergraph_ramsey_linear_statement_compat :
  X108CopyLegacy.three_uniform_degenerate_hypergraph_ramsey_linear_statement <->
  Hypergraph.conjectures.X108.three_uniform_degenerate_hypergraph_ramsey_linear_statement.
Proof. exact: iff_refl. Qed.

Lemma x117_monochromatic_copy_compat (T : finType) (E : {set {set T}}) (N : nat)
    (col : {set 'I_N} -> bool) :
  @X117CopyLegacy.x117_monochromatic_copy T E N col <->
  @Hypergraph.conjectures.X117.x117_monochromatic_copy T E N col.
Proof. exact: iff_refl. Qed.

Lemma x117_forces_mono_compat (T : finType) (E : {set {set T}}) (N : nat) :
  @X117CopyLegacy.x117_forces_mono T E N <->
  @Hypergraph.conjectures.X117.x117_forces_mono T E N.
Proof. exact: iff_refl. Qed.

Lemma x117_ramsey_number_compat (t R : nat) :
  X117CopyLegacy.x117_ramsey_number t R <->
  Hypergraph.conjectures.X117.x117_ramsey_number t R.
Proof. exact: iff_refl. Qed.

Lemma conlon_fox_rodl_hedgehog_ramsey_statement_compat :
  X117CopyLegacy.conlon_fox_rodl_hedgehog_ramsey_statement <->
  Hypergraph.conjectures.X117.conlon_fox_rodl_hedgehog_ramsey_statement.
Proof. exact: iff_refl. Qed.

Lemma x119_monochromatic_copy_compat (T : finType) (E : {set {set T}}) (N q : nat)
    (col : {set 'I_N} -> 'I_q) :
  @X119CopyLegacy.x119_monochromatic_copy T E N q col <->
  @Hypergraph.conjectures.X119.x119_monochromatic_copy T E N q col.
Proof. exact: iff_refl. Qed.

Lemma x119_forces_mono_compat (T : finType) (E : {set {set T}}) (q N : nat) :
  @X119CopyLegacy.x119_forces_mono T E q N <->
  @Hypergraph.conjectures.X119.x119_forces_mono T E q N.
Proof. exact: iff_refl. Qed.

Lemma x119_ramsey_number_compat (T : finType) (E : {set {set T}}) (q R : nat) :
  @X119CopyLegacy.x119_ramsey_number T E q R <->
  @Hypergraph.conjectures.X119.x119_ramsey_number T E q R.
Proof. exact: iff_refl. Qed.

Lemma conlon_fox_sudakov_three_uniform_ramsey_tower_statement_compat :
  X119CopyLegacy.conlon_fox_sudakov_three_uniform_ramsey_tower_statement <->
  Hypergraph.conjectures.X119.conlon_fox_sudakov_three_uniform_ramsey_tower_statement.
Proof. exact: iff_refl. Qed.
