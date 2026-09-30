(** * Digraph.conjectures.X93 -- v2 local-to-global tournament colouring row *)

From HB Require Import structures.
From mathcomp Require Import all_boot.
From Digraph Require Import prelude digraph tournament dichromatic.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X93 vocabulary ************************************************)

Definition x93_t_local_tournament (T : tournament) (t : nat) : Prop :=
  forall v : T, dicolorableb (induced_digraph (N_out v)) t.

(** ** X93 statements ******************************************************)

(** Corpus row: studies:std_berger_et_al_local_to_global_tournament_colourin
    Site: none
    Review: none
    English statement: (Berger, Choromanski, Chudnovsky, Fox, Loebl, Scott, Seymour and Thomasse, local-to-global tournament colouring conjecture)
      There is a function f such that every t-local tournament, that is every tournament in
      which the subtournament induced by the out-neighbourhood of each vertex has dichromatic
      number at most t, has dichromatic number at most f(t).
    Definitions: [x93_t_local_tournament T t] - every out-neighbourhood induces a t-dicolourable
      subdigraph (this file); [dicolorableb D k] (conjectures/dichromatic.v); [N_out v] and
      [tournament] (core/tournament.v); [induced_digraph] (core/digraph.v).
    Notes: The single function f is quantified outside t and T, as in the source. *)
Definition local_tournament_dichromatic_bound_statement : Prop :=
  exists f : nat -> nat,
    forall (t : nat) (T : tournament),
      x93_t_local_tournament T t ->
      dicolorableb T (f t).
