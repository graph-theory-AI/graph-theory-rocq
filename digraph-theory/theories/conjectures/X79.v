(** * Digraph.conjectures.X79 -- v2 tournament Erdos-Hajnal row *)

From HB Require Import structures.
From mathcomp Require Import all_boot.
From Digraph Require Import prelude digraph oriented tournament.
From Digraph.conjectures Require Import heroes.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X79 vocabulary ************************************************)

Definition x79_transitive_subtournament_at_least
    (T : tournament) (a : nat) : Prop :=
  exists S : {set T}, a <= #|S| /\ transb (sub_tournament S).

Definition x79_polynomial_transitive_bound
    (eps_num eps_den n a : nat) : Prop :=
  n ^ eps_num <= a ^ eps_den.

(** ** X79 statements ******************************************************)

(** Corpus row: studies:std_alon_pach_solymosi_conjecture
    Site: none
    Review: none
    English statement: (Alon, Pach and Solymosi, tournament Erdos-Hajnal conjecture)
      For every tournament H there is a positive rational exponent, given as a pair of positive
      naturals, such that every tournament T with no induced copy of H has a transitive
      subtournament on at least a vertices where #|T| raised to the numerator is at most a
      raised to the denominator, that is a is at least |T| to the power of the exponent.
    Definitions: [x79_transitive_subtournament_at_least T a] - some vertex set of size at least
      a induces a transitive subtournament (this file); [x79_polynomial_transitive_bound] - the
      division-free form of a >= n to the power eps (this file); [ind_free H T]
      (conjectures/heroes.v); [transb] and [sub_tournament] (core/tournament.v).
    Notes: The real exponent epsilon of the source is encoded as a positive rational, which is
      equivalent for an existence statement. The directed independence number alpha-vec of the
      corpus text is the maximum order of a transitive subtournament, which is what the body
      uses. This is the same conjecture as
      [erdos_hajnal_tournament_transitive_subtournament_statement] (conjectures/X136.v), stated
      with the size witness existentially quantified. *)
Definition alon_pach_solymosi_tournament_erdos_hajnal_statement : Prop :=
  forall H : tournament,
    exists eps_num eps_den : nat,
      [/\ 0 < eps_num, 0 < eps_den
        & forall T : tournament,
            ind_free H T ->
            exists a : nat,
              x79_transitive_subtournament_at_least T a /\
              x79_polynomial_transitive_bound eps_num eps_den #|T| a].
