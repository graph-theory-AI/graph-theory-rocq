(** * Chromatic.migration.cycle_lengths — frozen cycle-length exclusions of X28, X159 and X204
    (library migration B15)

    Batch B, family [cycle-lengths] (meta/library_primitives/cycle-lengths.json).  [Legacy]
    freezes, verbatim as they stood at the B15 baseline 4b63976, X28's RAW interval exclusion
    [x28_no_cycle_length_between] (over MathComp [ucycle], no length guard), X159's GENUINE
    interval exclusion [x159_no_cycle_length_between] (the explicit premise [2 < size c]) and
    X204's GENUINE exact absence [x204_no_cycle_length] (a Boolean disequality).  The live
    helpers now unfold to [GTBase.walks_paths.no_ucycle_length_between (--) a b],
    [no_cycle_length_between (--) lo hi] and [no_cycle_length (--) n], whose bodies are these
    terms, so every certificate is a kernel-checked conversion.  X28 keeps its raw contract at
    every parameter: no guard is added because its row uses the interval [4, 6].  [X28Legacy],
    [X159Legacy] and [X204Legacy] freeze the three planar colouring rows with this family's
    helpers only; planarity, the interval bounds [4, 6] and [4, 8], X204's outer [p], [q] with
    [0 < q] and [3 * p < 11 * q], and the two separate length-4 and length-5 premises are
    unchanged.  Hashes and substitutions: meta/migration_reports/cycle_lengths.md. *)

From GTBase Require Import base.
From Chromatic.conjectures Require Import X130 X28 X159 X204.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Legacy.

Definition x28_no_cycle_length_between (G : sgraph) (a b : nat) : Prop :=
  forall c : seq G,
    ucycle (--) c ->
    a <= size c ->
    size c <= b ->
    False.

Definition x159_no_cycle_length_between (G : sgraph) (lo hi : nat) : Prop :=
  forall c : seq G, ucycle (--) c -> 2 < size c -> lo <= size c -> size c <= hi -> False.

Definition x204_no_cycle_length (G : sgraph) (n : nat) : Prop :=
  forall c : seq G, ucycle (--) c -> 2 < size c -> size c != n.

End Legacy.

Module X28Legacy.

Definition planar_no_4_to_6_cycles_three_choosable_statement : Prop :=
  forall G : sgraph,
    wagner_planar G ->
    Legacy.x28_no_cycle_length_between G 4 6 ->
    choosable G 3.

End X28Legacy.

Module X159Legacy.

Definition planar_no_cycles_4_to_8_correspondence_chromatic_three_statement : Prop :=
  forall G : sgraph,
    wagner_planar G ->
    Legacy.x159_no_cycle_length_between G 4 8 ->
    x159_correspondence_3_colourable G.

End X159Legacy.

Module X204Legacy.

Definition planar_no_4_5_cycles_fractional_below_eleven_thirds_statement : Prop :=
  exists p q : nat,
    [/\ 0 < q, 3 * p < 11 * q &
      forall G : sgraph,
        wagner_planar G ->
        Legacy.x204_no_cycle_length G 4 ->
        Legacy.x204_no_cycle_length G 5 ->
        x130_frac_chi_le G p q].

End X204Legacy.

(** ** Certificates *)

Lemma x28_no_cycle_length_between_compat (G : sgraph) (a b : nat) :
  Legacy.x28_no_cycle_length_between G a b <-> x28_no_cycle_length_between G a b.
Proof. exact: iff_refl. Qed.

Lemma x159_no_cycle_length_between_compat (G : sgraph) (lo hi : nat) :
  Legacy.x159_no_cycle_length_between G lo hi <-> x159_no_cycle_length_between G lo hi.
Proof. exact: iff_refl. Qed.

Lemma x204_no_cycle_length_compat (G : sgraph) (n : nat) :
  Legacy.x204_no_cycle_length G n <-> x204_no_cycle_length G n.
Proof. exact: iff_refl. Qed.

Lemma planar_no_4_to_6_cycles_three_choosable_statement_compat :
  X28Legacy.planar_no_4_to_6_cycles_three_choosable_statement <->
  planar_no_4_to_6_cycles_three_choosable_statement.
Proof. exact: iff_refl. Qed.

Lemma planar_no_cycles_4_to_8_correspondence_chromatic_three_statement_compat :
  X159Legacy.planar_no_cycles_4_to_8_correspondence_chromatic_three_statement <->
  planar_no_cycles_4_to_8_correspondence_chromatic_three_statement.
Proof. exact: iff_refl. Qed.

Lemma planar_no_4_5_cycles_fractional_below_eleven_thirds_statement_compat :
  X204Legacy.planar_no_4_5_cycles_fractional_below_eleven_thirds_statement <->
  planar_no_4_5_cycles_fractional_below_eleven_thirds_statement.
Proof. exact: iff_refl. Qed.

Print Assumptions x28_no_cycle_length_between_compat.
Print Assumptions x159_no_cycle_length_between_compat.
Print Assumptions x204_no_cycle_length_compat.
Print Assumptions planar_no_4_to_6_cycles_three_choosable_statement_compat.
Print Assumptions planar_no_cycles_4_to_8_correspondence_chromatic_three_statement_compat.
Print Assumptions planar_no_4_5_cycles_fractional_below_eleven_thirds_statement_compat.
