(** * D5: forcing a monochromatic copy under every colouring, Hypergraph certificate

    Frozen at the D4 pin 7647f2bd8507b2b2ebab4f2a7b92f1f8cf7ae95b; bindings in
    meta/migration_reports/forces_mono.spec.json.
    - [<Phase>ForcingLegacy]: the three forcing sources (X108's two-colour bound and X117's forcing
      over bool palettes, X119's over ['I_q] with its q N order), the two reached Ramsey-number
      chains (forcing at R AND minimality against every forcing N, kept as chains) and the three
      complete current rows, verbatim, each importing only its own conjecture file.  The live
      sources are now aliases of [Hypergraph.foundations.hypergraph_forcing.hg_forces_mono]; these
      current copies keep the live D4 copy alias (so they convert to the live predicates), the live
      D1/A10 vocabulary and X119's ceiling square root with its opaque witness.
    The complete raw histories are D3's existing rows (X108ImageOriginal, X119ImageOriginal and the
    complete X117ImageLegacy row in Hypergraph.migration.image_edge), reused through the spec with
    their own certificates; nothing is copied again here. *)
From GTBase Require Import base.
Require Hypergraph.foundations.hypergraph_forcing.
Require Hypergraph.conjectures.X108 Hypergraph.conjectures.X117 Hypergraph.conjectures.X119.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module X108ForcingLegacy.
Import Hypergraph.conjectures.X108.

Definition x108_two_colour_ramsey_at_most
    (T : finType) (E : {set {set T}}) (N : nat) : Prop :=
  forall col : {set 'I_N} -> bool, x108_monochromatic_copy E col.

Definition three_uniform_degenerate_hypergraph_ramsey_linear_statement : Prop :=
  forall d : nat,
    exists c : nat,
      forall (T : finType) (E : {set {set T}}),
        x108_uniform E 3 ->
        x108_d_degenerate E d ->
        X108ForcingLegacy.x108_two_colour_ramsey_at_most E (c * #|T|).

End X108ForcingLegacy.

Module X117ForcingLegacy.
Import Hypergraph.conjectures.X117.

Definition x117_forces_mono
    (T : finType) (E : {set {set T}}) (N : nat) : Prop :=
  forall col : {set 'I_N} -> bool, x117_monochromatic_copy E col.

Definition x117_ramsey_number (t R : nat) : Prop :=
  X117ForcingLegacy.x117_forces_mono (x117_edges t) R /\
  forall N : nat, X117ForcingLegacy.x117_forces_mono (x117_edges t) N -> R <= N.

Definition conlon_fox_rodl_hedgehog_ramsey_statement : Prop :=
  forall e1 e2 : nat,
    0 < e1 -> 0 < e2 ->
    exists t0 : nat,
      forall t R : nat,
        t0 <= t ->
        X117ForcingLegacy.x117_ramsey_number t R ->
        t ^ (2 * e2 - e1) <= R ^ e2 /\ R ^ e2 <= t ^ (2 * e2 + e1).

End X117ForcingLegacy.

Module X119ForcingLegacy.
Import Hypergraph.conjectures.X119.

Definition x119_forces_mono
    (T : finType) (E : {set {set T}}) (q N : nat) : Prop :=
  forall col : {set 'I_N} -> 'I_q, x119_monochromatic_copy E col.

Definition x119_ramsey_number
    (T : finType) (E : {set {set T}}) (q R : nat) : Prop :=
  X119ForcingLegacy.x119_forces_mono E q R /\
  forall N : nat, X119ForcingLegacy.x119_forces_mono E q N -> R <= N.

Definition conlon_fox_sudakov_three_uniform_ramsey_tower_statement : Prop :=
  forall q : nat,
    2 <= q ->
    exists cq : nat,
      forall (T : finType) (E : {set {set T}}),
        x119_uniform E 3 ->
        x119_no_isolated E ->
        forall R : nat,
          X119ForcingLegacy.x119_ramsey_number E q R ->
          R <= 2 ^ (2 ^ (cq * x119_sqrt #|E|)).

End X119ForcingLegacy.

(** Every frozen copy unfolds, through the live D4 copy alias, to the same term as the live alias
    of [hg_forces_mono]: all eight bridges are conversions. *)

Lemma x108_two_colour_ramsey_at_most_compat (T : finType) (E : {set {set T}}) (N : nat) :
  @X108ForcingLegacy.x108_two_colour_ramsey_at_most T E N <->
  @Hypergraph.conjectures.X108.x108_two_colour_ramsey_at_most T E N.
Proof. exact: iff_refl. Qed.

Lemma three_uniform_degenerate_hypergraph_ramsey_linear_statement_compat :
  X108ForcingLegacy.three_uniform_degenerate_hypergraph_ramsey_linear_statement <->
  Hypergraph.conjectures.X108.three_uniform_degenerate_hypergraph_ramsey_linear_statement.
Proof. exact: iff_refl. Qed.

Lemma x117_forces_mono_compat (T : finType) (E : {set {set T}}) (N : nat) :
  @X117ForcingLegacy.x117_forces_mono T E N <->
  @Hypergraph.conjectures.X117.x117_forces_mono T E N.
Proof. exact: iff_refl. Qed.

Lemma x117_ramsey_number_compat (t R : nat) :
  X117ForcingLegacy.x117_ramsey_number t R <->
  Hypergraph.conjectures.X117.x117_ramsey_number t R.
Proof. exact: iff_refl. Qed.

Lemma conlon_fox_rodl_hedgehog_ramsey_statement_compat :
  X117ForcingLegacy.conlon_fox_rodl_hedgehog_ramsey_statement <->
  Hypergraph.conjectures.X117.conlon_fox_rodl_hedgehog_ramsey_statement.
Proof. exact: iff_refl. Qed.

Lemma x119_forces_mono_compat (T : finType) (E : {set {set T}}) (q N : nat) :
  @X119ForcingLegacy.x119_forces_mono T E q N <->
  @Hypergraph.conjectures.X119.x119_forces_mono T E q N.
Proof. exact: iff_refl. Qed.

Lemma x119_ramsey_number_compat (T : finType) (E : {set {set T}}) (q R : nat) :
  @X119ForcingLegacy.x119_ramsey_number T E q R <->
  @Hypergraph.conjectures.X119.x119_ramsey_number T E q R.
Proof. exact: iff_refl. Qed.

Lemma conlon_fox_sudakov_three_uniform_ramsey_tower_statement_compat :
  X119ForcingLegacy.conlon_fox_sudakov_three_uniform_ramsey_tower_statement <->
  Hypergraph.conjectures.X119.conlon_fox_sudakov_three_uniform_ramsey_tower_statement.
Proof. exact: iff_refl. Qed.
