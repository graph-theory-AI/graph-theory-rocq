(** * Digraph.conjectures.X92 -- v2 tournament inversion-number row *)

From HB Require Import structures.
From mathcomp Require Import all_boot.
From Digraph Require Import prelude digraph tournament.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X92 vocabulary ************************************************)

Fixpoint x92_after_inversions
    (D : diGraphType) (steps : seq {set D}) : rel D :=
  match steps with
  | [::] => fun u v : D => u --> v
  | A :: rest =>
      fun u v : D =>
        if (u \in A) && (v \in A)
        then x92_after_inversions rest v u
        else x92_after_inversions rest u v
  end.

Definition x92_acyclic_rel (T : finType) (A : rel T) : bool :=
  [forall v : T, [forall w : T, A v w ==> ~~ connect A w v]].

Definition x92_inverts_to_acyclic
    (D : diGraphType) (steps : seq {set D}) : Prop :=
  x92_acyclic_rel (@x92_after_inversions D steps).

Definition x92_tournament_inversion_number_at_most
    (n k : nat) : Prop :=
  forall T : tournament,
    #|T| = n ->
    exists steps : seq {set T},
      size steps <= k /\ @x92_inverts_to_acyclic T steps.

(** ** X92 statements ******************************************************)

(** Corpus row: studies:std_belkhechine_bouaziz_boudabbous_pouzet_inversion
    Site: none
    Review: none
    English statement: (Belkhechine, Bouaziz, Boudabbous and Pouzet, inversion-number bound conjecture)
      For every n, every tournament on n vertices can be made acyclic by at most floor((n-1)/2)
      successive subset inversions, where one inversion picks a vertex subset and reverses every
      arc with both ends in it.
    Definitions: [x92_after_inversions steps] - the arc relation after applying the inversions
      of the list steps (this file); [x92_acyclic_rel] - no vertex reaches itself back along a
      forward arc (this file); [x92_inverts_to_acyclic] and
      [x92_tournament_inversion_number_at_most n k] (this file); [tournament]
      (core/tournament.v).
    Notes: inv(n) of the source, the maximum inversion number over n-vertex tournaments, is
      encoded as the upper bound holding for every tournament of that order; the floor is the
      natural-number quotient n.-1 %/ 2. *)
Definition tournament_inversion_number_half_bound_statement : Prop :=
  forall n : nat,
    x92_tournament_inversion_number_at_most n (n.-1 %/ 2).
