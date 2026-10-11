(** * Extremal.migration.bfold_colouring — bfold-colouring certificates: D2chr (fractional Hadwiger row)

    Family [bfold-colouring] (meta/library_primitives/bfold-colouring.json); canonical
    [GTBase.bfold_colourings.bfold_colouring b f], with no guard.  [Legacy] freezes, verbatim at the baseline 3bdfdae
    (tree ade432af), D2chr's [bfold_colouring] (unchanged since its authoring 818a76c) and its consumer chain
    [is_fractional_chromatic G r]: r is the ATTAINED RATIONAL MINIMUM of a/b over (a:b)-colourings with [0 < b] (a
    witnessing colouring with [r = a/b], and [r <= a/b] for every colouring).  This family keeps that minimum distinct
    from a mere bound and does not migrate it.  [D2chrLegacy] freezes the complete fractional Hadwiger row with its
    [0 < #|G|] guard.  The Hadwiger vocabulary ([is_hadwiger], [frac_clique_minor] with its repaired non-empty
    branch-set guard, [is_fractional_hadwiger]) is outside this family and applied live.  No earlier library family
    froze this row, so [D2chrLegacy] is already its deepest original.  Every certificate is a kernel conversion. *)

From GTBase Require Import base bfold_colourings.
From Extremal.conjectures Require Import D2chr.
From mathcomp Require Import all_algebra.
Import GRing.Theory Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.

Module Legacy.

Definition bfold_colouring (G : sgraph) (a b : nat) (f : G -> {set 'I_a}) : Prop :=
  (forall v, #|f v| = b) /\ (forall x y : G, x -- y -> [disjoint f x & f y]).

Definition is_fractional_chromatic (G : sgraph) (r : rat) : Prop :=
  (exists a b : nat, (0 < b)%N /\ (exists f, @Legacy.bfold_colouring G a b f) /\ r = a%:Q / b%:Q) /\
  (forall a b : nat, (0 < b)%N -> (exists f, @Legacy.bfold_colouring G a b f) -> r <= a%:Q / b%:Q).

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

(** ** Certificates *)

Lemma bfold_colouring_compat (G : sgraph) (a b : nat) (f : G -> {set 'I_a}) :
  Legacy.bfold_colouring b f <-> Extremal.conjectures.D2chr.bfold_colouring b f.
Proof. exact: iff_refl. Qed.

Lemma is_fractional_chromatic_compat (G : sgraph) (r : rat) :
  Legacy.is_fractional_chromatic G r <-> is_fractional_chromatic G r.
Proof. exact: iff_refl. Qed.

Lemma fractional_hadwiger_statement_compat :
  D2chrLegacy.fractional_hadwiger_statement <-> fractional_hadwiger_statement.
Proof. exact: iff_refl. Qed.

(** ** The local source in the canonical vocabulary *)

Lemma bfold_colouring_canonical (G : sgraph) (a b : nat) (f : G -> {set 'I_a}) :
  Extremal.conjectures.D2chr.bfold_colouring b f <-> bfold_colourings.bfold_colouring b f.
Proof. exact: iff_refl. Qed.

Print Assumptions bfold_colouring_compat.
Print Assumptions is_fractional_chromatic_compat.
Print Assumptions fractional_hadwiger_statement_compat.
Print Assumptions bfold_colouring_canonical.
