(** * Extremal.migration.fractional_chromatic — fractional-chromatic certificates: D2chr (fractional Hadwiger row)

    Family [fractional-chromatic] (meta/library_primitives/fractional-chromatic.json); canonical
    [Extremal.foundations.fractional_colouring.is_fractional_chromatic G r]: r is the ATTAINED RATIONAL MINIMUM of
    a/b over (a:b)-colourings with [0 < b] (a witnessing colouring with [r = a/b], and [r <= a/b] for every
    colouring), with no guard on [G] (the empty graph has value 0).  Baseline: the accepted bfold-colouring candidate
    9e83cd85 (tree 9bcad1e4), where D2chr's [bfold_colouring] is already bfold's alias of the GTBase canonical.

    - [Legacy] freezes, verbatim at the baseline, D2chr's [is_fractional_chromatic] (text unchanged since its
      authoring 818a76c).  Its [bfold_colouring] is applied live, as in the baseline text: that helper was migrated
      by the earlier bfold-colouring family (a later-family snapshot, documented in both specs).
    - [D2chrLegacy] freezes the complete fractional Hadwiger row with its [0 < #|G|] guard; [is_hadwiger] (the
      integer Hadwiger number, a distinct notion) and [is_fractional_hadwiger] (the clique-minor LP, a later
      separate family) are applied live.
    - [D2chrOriginal] is the end-to-end pre-migration row: the chain at its ORIGINAL body is bfold's frozen
      [BF.Legacy.is_fractional_chromatic] over [BF.Legacy.bfold_colouring] (verbatim at 3bdfdae, unchanged since
      818a76c), certified through bfold's own row certificate.  No earlier family froze this row before bfold, so
      that composition is its deepest original.
    The existential cross-multiplied bound [x130_frac_chi_le] of X130 and its rows are a distinct contract and are
    not touched.  Every certificate is a kernel conversion. *)

From GTBase Require Import base.
From Extremal.conjectures Require Import D2chr.
From Extremal.foundations Require fractional_colouring.
Require Extremal.migration.bfold_colouring.
From mathcomp Require Import all_algebra.
Import GRing.Theory Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.

(** bfold-colouring's certificate, bound explicitly (no Import): its frozen original chain and row certificate
    are reused by the Originals below. *)
Module BF := Extremal.migration.bfold_colouring.

Module Legacy.

Definition is_fractional_chromatic (G : sgraph) (r : rat) : Prop :=
  (exists a b : nat, (0 < b)%N /\ (exists f, @bfold_colouring G a b f) /\ r = a%:Q / b%:Q) /\
  (forall a b : nat, (0 < b)%N -> (exists f, @bfold_colouring G a b f) -> r <= a%:Q / b%:Q).

End Legacy.

Module D2chrLegacy.

Definition fractional_hadwiger_statement : Prop :=
  forall (G : sgraph) (xf hf : rat) (h : nat),
    (0 < #|G|)%N ->
    Legacy.is_fractional_chromatic G xf -> is_hadwiger G h -> is_fractional_hadwiger G hf ->
    [/\ xf <= h%:Q,
        (χ([set: G]))%:Q <= hf
      & xf <= hf ].

End D2chrLegacy.

Module D2chrOriginal.

Definition statement : Prop :=
  forall (G : sgraph) (xf hf : rat) (h : nat),
    (0 < #|G|)%N ->
    BF.Legacy.is_fractional_chromatic G xf -> is_hadwiger G h -> is_fractional_hadwiger G hf ->
    [/\ xf <= h%:Q,
        (χ([set: G]))%:Q <= hf
      & xf <= hf ].

End D2chrOriginal.

(** ** Certificates *)

Lemma is_fractional_chromatic_compat (G : sgraph) (r : rat) :
  Legacy.is_fractional_chromatic G r <-> Extremal.conjectures.D2chr.is_fractional_chromatic G r.
Proof. exact: iff_refl. Qed.

Lemma fractional_hadwiger_statement_compat :
  D2chrLegacy.fractional_hadwiger_statement <-> fractional_hadwiger_statement.
Proof. exact: iff_refl. Qed.

(** The chain at its original body (bfold's frozen copy over its frozen b-fold colouring), through bfold's own
    certificate. *)
Lemma is_fractional_chromatic_original_compat (G : sgraph) (r : rat) :
  BF.Legacy.is_fractional_chromatic G r <-> is_fractional_chromatic G r.
Proof. exact: BF.is_fractional_chromatic_compat. Qed.

(** bfold's row certificate, whose frozen row applies the original chain, is the Original's by conversion. *)
Lemma fractional_hadwiger_statement_original_compat :
  D2chrOriginal.statement <-> fractional_hadwiger_statement.
Proof. exact: BF.fractional_hadwiger_statement_compat. Qed.

(** ** The local source and the row in the canonical vocabulary *)

Lemma is_fractional_chromatic_canonical (G : sgraph) (r : rat) :
  is_fractional_chromatic G r <-> fractional_colouring.is_fractional_chromatic G r.
Proof. exact: iff_refl. Qed.

Lemma fractional_hadwiger_statement_canonical :
  fractional_hadwiger_statement <->
  forall (G : sgraph) (xf hf : rat) (h : nat),
    (0 < #|G|)%N ->
    fractional_colouring.is_fractional_chromatic G xf -> is_hadwiger G h -> is_fractional_hadwiger G hf ->
    [/\ xf <= h%:Q,
        (χ([set: G]))%:Q <= hf
      & xf <= hf ].
Proof. exact: iff_refl. Qed.

Print Assumptions is_fractional_chromatic_compat.
Print Assumptions fractional_hadwiger_statement_compat.
Print Assumptions is_fractional_chromatic_original_compat.
Print Assumptions fractional_hadwiger_statement_original_compat.
Print Assumptions is_fractional_chromatic_canonical.
Print Assumptions fractional_hadwiger_statement_canonical.
