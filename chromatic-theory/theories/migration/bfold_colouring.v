(** * Chromatic.migration.bfold_colouring — bfold-colouring certificates: X130, X131, X149, X173, X204, X218

    Family [bfold-colouring] (meta/library_primitives/bfold-colouring.json); canonical
    [GTBase.bfold_colourings.bfold_colouring b f]: every vertex gets a [b]-element subset of the supplied palette
    ['I_a] and adjacent vertices get disjoint subsets, with no guard ([b = 0] and the empty carrier allowed).
    [Legacy] freezes, verbatim at the baseline 3bdfdae (tree ade432af), X130's [x130_bfold_colouring] (unchanged since
    its authoring 2d42162) and its consumer chain [x130_frac_chi_le]: an EXISTENTIAL cross-multiplied natural bound
    [exists a b f, 0 < b, an (a:b)-colouring and a * q <= p * b], which this family keeps distinct from any rational
    attained minimum and does not migrate.  Its raw relation is vacuous in the bound for [q = 0]; every row below
    supplies its own [q > 0].  [X130Legacy], [X131Legacy] (the duplicate, literally X130's statement), [X149Legacy],
    [X173Legacy], [X204Legacy] and [X218Legacy] freeze the six complete rows that reach the b-fold colouring through that
    chain, every guard and quantifier in place.

    [X204Original] composes the end-to-end pre-migration X204 row.  The earlier family B15 (cycle lengths, certificate
    [Chromatic.migration.cycle_lengths], bound here as [Module CL]) froze X204's cycle-length exclusion
    [x204_no_cycle_length] and kept this chain live; this family freezes the chain and keeps that exclusion live.  Over
    B15's frozen [CL.Legacy.x204_no_cycle_length] and the frozen chain here, [X204Original] is the row with every
    migrated helper at its original body, certified through B15's own row certificate.  The other five rows have no
    earlier snapshot, so their Legacy rows are already their deepest originals.  Every certificate is a kernel
    conversion. *)

From GTBase Require Import base bfold_colourings.
From Chromatic.conjectures Require Import X130 X131 X149 X173 X204 X218.
Require Chromatic.migration.cycle_lengths.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** B15's certificate, bound explicitly: its frozen cycle-length exclusion is reused by the Original. *)
Module CL := Chromatic.migration.cycle_lengths.

Module Legacy.

Definition x130_bfold_colouring (G : sgraph) (a b : nat) (f : G -> {set 'I_a}) : Prop :=
  (forall v : G, #|f v| = b) /\ (forall x y : G, x -- y -> [disjoint f x & f y]).

Definition x130_frac_chi_le (G : sgraph) (p q : nat) : Prop :=
  exists (a b : nat) (f : G -> {set 'I_a}),
    [/\ (0 < b)%N, @Legacy.x130_bfold_colouring G a b f & (a * q <= p * b)%N].

End Legacy.

Module X130Legacy.

Definition dvorak_mnich_planar_girth5_fractional_chromatic_statement : Prop :=
  exists p q : nat,
    [/\ (0 < q)%N, (p < 3 * q)%N &
      forall G : sgraph,
        wagner_planar G ->
        girth_geq G 5 ->
        Legacy.x130_frac_chi_le G p q].

End X130Legacy.

Module X131Legacy.

Definition dvorak_mnich_planar_girth5_fractional_chromatic_duplicate_statement : Prop :=
  X130Legacy.dvorak_mnich_planar_girth5_fractional_chromatic_statement.

End X131Legacy.

Module X149Legacy.

Definition gimbel_kundgen_li_thomassen_four_chromatic_planar_fractional_statement : Prop :=
  forall G : sgraph,
    wagner_planar G ->
    χ([set: G]) = 4 ->
    ~ Legacy.x130_frac_chi_le G 3 1.

End X149Legacy.

Module X173Legacy.

Definition planar_triangle_free_fractional_chromatic_bound_statement : Prop :=
  forall G : sgraph,
    wagner_planar G ->
    girth_geq G 4 ->
    Legacy.x130_frac_chi_le G (3 * #|G|) (#|G|).+1.

End X173Legacy.

Module X204Legacy.

Definition planar_no_4_5_cycles_fractional_below_eleven_thirds_statement : Prop :=
  exists p q : nat,
    [/\ 0 < q, 3 * p < 11 * q &
      forall G : sgraph,
        wagner_planar G ->
        x204_no_cycle_length G 4 ->
        x204_no_cycle_length G 5 ->
        Legacy.x130_frac_chi_le G p q].

End X204Legacy.

Module X204Original.

Definition statement : Prop :=
  exists p q : nat,
    [/\ 0 < q, 3 * p < 11 * q &
      forall G : sgraph,
        wagner_planar G ->
        CL.Legacy.x204_no_cycle_length G 4 ->
        CL.Legacy.x204_no_cycle_length G 5 ->
        Legacy.x130_frac_chi_le G p q].

End X204Original.

Module X218Legacy.

Definition kr_free_degenerate_fractional_chromatic_sublinear_statement : Prop :=
  forall r : nat, 4 <= r ->
    forall q : nat, 0 < q ->
      exists d0 : nat,
        forall (d : nat) (G : sgraph),
          d0 <= d ->
          ω([set: G]) < r ->
          k_degenerate G d ->
          Legacy.x130_frac_chi_le G d q.

End X218Legacy.

(** ** Certificates *)

Lemma x130_bfold_colouring_compat (G : sgraph) (a b : nat) (f : G -> {set 'I_a}) :
  Legacy.x130_bfold_colouring b f <-> x130_bfold_colouring b f.
Proof. exact: iff_refl. Qed.

Lemma x130_frac_chi_le_compat (G : sgraph) (p q : nat) :
  Legacy.x130_frac_chi_le G p q <-> x130_frac_chi_le G p q.
Proof. exact: iff_refl. Qed.

Lemma dvorak_mnich_planar_girth5_fractional_chromatic_statement_compat :
  X130Legacy.dvorak_mnich_planar_girth5_fractional_chromatic_statement <->
  dvorak_mnich_planar_girth5_fractional_chromatic_statement.
Proof. exact: iff_refl. Qed.

Lemma dvorak_mnich_planar_girth5_fractional_chromatic_duplicate_statement_compat :
  X131Legacy.dvorak_mnich_planar_girth5_fractional_chromatic_duplicate_statement <->
  dvorak_mnich_planar_girth5_fractional_chromatic_duplicate_statement.
Proof. exact: iff_refl. Qed.

Lemma gimbel_kundgen_li_thomassen_four_chromatic_planar_fractional_statement_compat :
  X149Legacy.gimbel_kundgen_li_thomassen_four_chromatic_planar_fractional_statement <->
  gimbel_kundgen_li_thomassen_four_chromatic_planar_fractional_statement.
Proof. exact: iff_refl. Qed.

Lemma planar_triangle_free_fractional_chromatic_bound_statement_compat :
  X173Legacy.planar_triangle_free_fractional_chromatic_bound_statement <->
  planar_triangle_free_fractional_chromatic_bound_statement.
Proof. exact: iff_refl. Qed.

Lemma planar_no_4_5_cycles_fractional_below_eleven_thirds_statement_compat :
  X204Legacy.planar_no_4_5_cycles_fractional_below_eleven_thirds_statement <->
  planar_no_4_5_cycles_fractional_below_eleven_thirds_statement.
Proof. exact: iff_refl. Qed.

(** B15's row certificate, whose frozen row applies the (unchanged) live chain, is the Original's by conversion. *)
Lemma planar_no_4_5_cycles_fractional_below_eleven_thirds_statement_original_compat :
  X204Original.statement <-> planar_no_4_5_cycles_fractional_below_eleven_thirds_statement.
Proof. exact: CL.planar_no_4_5_cycles_fractional_below_eleven_thirds_statement_compat. Qed.

Lemma kr_free_degenerate_fractional_chromatic_sublinear_statement_compat :
  X218Legacy.kr_free_degenerate_fractional_chromatic_sublinear_statement <->
  kr_free_degenerate_fractional_chromatic_sublinear_statement.
Proof. exact: iff_refl. Qed.

(** ** The local source in the canonical vocabulary *)

Lemma x130_bfold_colouring_canonical (G : sgraph) (a b : nat) (f : G -> {set 'I_a}) :
  x130_bfold_colouring b f <-> bfold_colouring b f.
Proof. exact: iff_refl. Qed.

Print Assumptions x130_bfold_colouring_compat.
Print Assumptions x130_frac_chi_le_compat.
Print Assumptions dvorak_mnich_planar_girth5_fractional_chromatic_statement_compat.
Print Assumptions dvorak_mnich_planar_girth5_fractional_chromatic_duplicate_statement_compat.
Print Assumptions gimbel_kundgen_li_thomassen_four_chromatic_planar_fractional_statement_compat.
Print Assumptions planar_triangle_free_fractional_chromatic_bound_statement_compat.
Print Assumptions planar_no_4_5_cycles_fractional_below_eleven_thirds_statement_compat.
Print Assumptions planar_no_4_5_cycles_fractional_below_eleven_thirds_statement_original_compat.
Print Assumptions kr_free_degenerate_fractional_chromatic_sublinear_statement_compat.
Print Assumptions x130_bfold_colouring_canonical.
