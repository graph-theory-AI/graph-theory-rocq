(** * Spectral.conjectures.X6 -- v2 milestone X6, clean spectral-energy row *)

From mathcomp Require Import all_boot.
From GraphTheory Require Import sgraph.
From GTBase Require Import base.
From mathcomp Require Import all_algebra perm.
From Spectral Require Import foundations.spectral.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Import GRing.Theory Num.Theory.

(** ** Local spectral vocabulary *******************************************)

Definition x6_splus (R : rcfType) (s : seq R) : R :=
  \sum_(x <- s | 0 < x) x ^+ 2.

Definition x6_sminus (R : rcfType) (s : seq R) : R :=
  \sum_(x <- s | x < 0) x ^+ 2.

(** ** X6 statements *******************************************************)

(** Corpus row: studies:std_elphick_farber_goldberg_wocjan_conjecture_s_s
    Site: none
    Review: none
    English statement: (Elphick, Farber, Goldberg and Wocjan, "Elphick-Farber-Goldberg-
      Wocjan conjecture (s+ / s-)")
      Over any real-closed field R, for every connected simple graph G with n >= 1 vertices
      and every listing s of the eigenvalues of the adjacency matrix of G in non-increasing
      order and with multiplicity: the sum of the squares of the strictly positive entries
      of s is at least n - 1, and the sum of the squares of the strictly negative entries of
      s is also at least n - 1. Equivalently, the minimum of s+(G) and s-(G) is at least
      n - 1.
    Definitions: [x6_splus R s] — the sum of x^2 over the strictly positive entries x of s
      (X6.v); [x6_sminus R s] — the same sum over the strictly negative entries (X6.v);
      [adjmx R G] — the adjacency matrix of G over R
      (spectral-graph-theory/theories/foundations/spectral.v); [is_spectrum A s] — s is the
      length-n non-increasing listing of the spectrum of A, characterised by the
      factorisation of the characteristic polynomial of A (foundations/spectral.v);
      [connected] is coq-graph-theory; [rcfType] is MathComp.
    Notes: the minimum of two quantities being at least n - 1 is encoded as the conjunction
      of the two inequalities. Eigenvalues live in an abstract real-closed field R rather
      than in the reals, and the spectrum is universally quantified through [is_spectrum];
      the sorted listing is unique, so the universal form is equivalent to naming it, but
      the statement is vacuous for any R over which the characteristic polynomial does not
      split (it does split over every real-closed field, a fact not proved here). [n.-1] is
      the nat predecessor, with [0 < n] guarded. *)
Definition elphick_farber_goldberg_wocjan_splus_sminus_statement : Prop :=
  forall (R : rcfType) (G : sgraph) (n : nat),
    connected [set: G] -> #|G| = n -> (0 < n)%N ->
    forall s : seq R, is_spectrum (adjmx R G) s ->
      (((n.-1)%:R : R) <= @x6_splus R s)%R /\
      (((n.-1)%:R : R) <= @x6_sminus R s)%R.
