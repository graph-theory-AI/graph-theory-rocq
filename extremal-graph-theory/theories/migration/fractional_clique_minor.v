(** * Extremal.migration.fractional_clique_minor — fractional-clique-minor certificates: D2chr (fractional Hadwiger row)

    Family [fractional-clique-minor] (meta/library_primitives/fractional-clique-minor.json); canonical
    [Extremal.foundations.fractional_hadwiger.frac_clique_minor B w r] (a feasible point of the clique-minor LP: weights
    non-negative, branch sets NON-EMPTY and connected, distinct indices adjacent, every vertex covered by weight at
    most 1, [r] the total weight) and its ATTAINED MAXIMUM [is_fractional_hadwiger G r], with no guard on [G].
    Baseline: the fractional-chromatic candidate 95ac06eb (tree 9ea68517), where D2chr's [is_fractional_chromatic] is
    already that family's alias of the Extremal canonical.

    - [Legacy] freezes, verbatim at the baseline, D2chr's [frac_clique_minor] and [is_fractional_hadwiger].  Their
      texts are those of the wave-E10 repair (e61d308, 2026-09-24), unchanged since.  The pre-repair body (connected
      branch sets only, possibly empty) made the LP unbounded and the row vacuous; it is kept verbatim with its witness
      in [Extremal.conjectures.grounding_D2chr] ([old_frac_clique_minor], [old_is_fractional_hadwiger_unsat]) as a
      re-audited DEFECT, a historical reference only, and is never an Original here.
    - [D2chrLegacy] freezes the complete fractional Hadwiger row with its [0 < #|G|] guard.  [is_hadwiger] (the
      integer Hadwiger number, a distinct notion) is applied live, and so is [is_fractional_chromatic] (the earlier
      fractional-chromatic family's alias: a later-family snapshot, documented in both specs).
    - [D2chrOriginal] is the end-to-end row at the original bodies that are still valid: the attained fractional
      chromatic number at bfold's frozen original chain [BF.Legacy.is_fractional_chromatic] over
      [BF.Legacy.bfold_colouring] (verbatim at 3bdfdae, unchanged since 818a76c) and the fractional Hadwiger number at
      this family's [Legacy] (the repaired body, its deepest valid text).  It is certified through the
      fractional-chromatic family's own Original certificate.
    The Atlas LP over sets of branch sets ([goodb]/[hfeas]/[hopt]) is local to its existence proof and not touched.
    Every certificate is a kernel conversion. *)

From GTBase Require Import base.
From Extremal.conjectures Require Import D2chr.
From Extremal.foundations Require fractional_colouring fractional_hadwiger.
Require Extremal.migration.bfold_colouring Extremal.migration.fractional_chromatic.
From mathcomp Require Import all_algebra.
Import GRing.Theory Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.

(** bfold-colouring's and fractional-chromatic's certificates, bound explicitly (no Import): their frozen original
    chain and row certificates are reused by the Original below. *)
Module BF := Extremal.migration.bfold_colouring.
Module FC := Extremal.migration.fractional_chromatic.

Module Legacy.

Definition frac_clique_minor (G : sgraph) (n : nat)
    (B : 'I_n -> {set G}) (w : 'I_n -> rat) (r : rat) : Prop :=
  [/\ (forall i, 0 <= w i),
      (forall i, B i != set0 /\ connected (B i)),
      (forall i j, i != j -> exists x y : G, [/\ x \in B i, y \in B j & x -- y]),
      (forall v : G, (\sum_(i | v \in B i) w i <= 1)%R)
    & r = \sum_i w i].

Definition is_fractional_hadwiger (G : sgraph) (r : rat) : Prop :=
  (exists (n : nat) (B : 'I_n -> {set G}) (w : 'I_n -> rat), Legacy.frac_clique_minor B w r) /\
  (forall (n : nat) (B : 'I_n -> {set G}) (w : 'I_n -> rat) (r' : rat),
     Legacy.frac_clique_minor B w r' -> r' <= r).

End Legacy.

Module D2chrLegacy.

Definition fractional_hadwiger_statement : Prop :=
  forall (G : sgraph) (xf hf : rat) (h : nat),
    (0 < #|G|)%N ->
    is_fractional_chromatic G xf -> is_hadwiger G h -> Legacy.is_fractional_hadwiger G hf ->
    [/\ xf <= h%:Q,
        (χ([set: G]))%:Q <= hf
      & xf <= hf ].

End D2chrLegacy.

Module D2chrOriginal.

Definition statement : Prop :=
  forall (G : sgraph) (xf hf : rat) (h : nat),
    (0 < #|G|)%N ->
    BF.Legacy.is_fractional_chromatic G xf -> is_hadwiger G h -> Legacy.is_fractional_hadwiger G hf ->
    [/\ xf <= h%:Q,
        (χ([set: G]))%:Q <= hf
      & xf <= hf ].

End D2chrOriginal.

(** ** Certificates *)

Lemma frac_clique_minor_compat (G : sgraph) (n : nat) (B : 'I_n -> {set G}) (w : 'I_n -> rat) (r : rat) :
  Legacy.frac_clique_minor B w r <-> Extremal.conjectures.D2chr.frac_clique_minor B w r.
Proof. exact: iff_refl. Qed.

Lemma is_fractional_hadwiger_compat (G : sgraph) (r : rat) :
  Legacy.is_fractional_hadwiger G r <-> Extremal.conjectures.D2chr.is_fractional_hadwiger G r.
Proof. exact: iff_refl. Qed.

Lemma fractional_hadwiger_statement_compat :
  D2chrLegacy.fractional_hadwiger_statement <-> fractional_hadwiger_statement.
Proof. exact: iff_refl. Qed.

(** The row at its original valid bodies: the fractional-chromatic family's Original certificate (bfold's frozen
    chain), with this family's frozen fractional Hadwiger number by conversion. *)
Lemma fractional_hadwiger_statement_original_compat :
  D2chrOriginal.statement <-> fractional_hadwiger_statement.
Proof. exact: FC.fractional_hadwiger_statement_original_compat. Qed.

(** ** The local sources and the row in the canonical vocabulary *)

Lemma frac_clique_minor_canonical (G : sgraph) (n : nat) (B : 'I_n -> {set G}) (w : 'I_n -> rat) (r : rat) :
  frac_clique_minor B w r <-> fractional_hadwiger.frac_clique_minor B w r.
Proof. exact: iff_refl. Qed.

Lemma is_fractional_hadwiger_canonical (G : sgraph) (r : rat) :
  is_fractional_hadwiger G r <-> fractional_hadwiger.is_fractional_hadwiger G r.
Proof. exact: iff_refl. Qed.

Lemma fractional_hadwiger_statement_canonical :
  fractional_hadwiger_statement <->
  forall (G : sgraph) (xf hf : rat) (h : nat),
    (0 < #|G|)%N ->
    fractional_colouring.is_fractional_chromatic G xf -> is_hadwiger G h ->
    fractional_hadwiger.is_fractional_hadwiger G hf ->
    [/\ xf <= h%:Q,
        (χ([set: G]))%:Q <= hf
      & xf <= hf ].
Proof. exact: iff_refl. Qed.

Print Assumptions frac_clique_minor_compat.
Print Assumptions is_fractional_hadwiger_compat.
Print Assumptions fractional_hadwiger_statement_compat.
Print Assumptions fractional_hadwiger_statement_original_compat.
Print Assumptions frac_clique_minor_canonical.
Print Assumptions is_fractional_hadwiger_canonical.
Print Assumptions fractional_hadwiger_statement_canonical.
