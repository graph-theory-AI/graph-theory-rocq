(** * Chromatic.conjectures.X160 -- v2 density-zero constricting set row *)

From GTBase Require Export base.
From Chromatic.conjectures Require Import X3.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X160 vocabulary ***********************************************)

Definition x160_count_up_to (F : nat -> bool) (n : nat) : nat :=
  #|[set i : 'I_n | F ((val i).+1)]|.

Definition x160_density_zero (F : nat -> bool) : Prop :=
  forall eps_num eps_den : nat,
    0 < eps_num ->
    0 < eps_den ->
    exists N : nat,
      forall n : nat,
        N <= n ->
        eps_den * x160_count_up_to F n <= eps_num * n.

(** ** X160 statements *****************************************************)

(** Corpus row: arxiv:1509.06563#02
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/1509.06563__02/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/1509.06563__02.json
    English statement: (Scott and Seymour 2018, Problem 1.6, arXiv:1509.06563)
      There is a set F of positive integers that is infinite, constricting, and has asymptotic
      density zero: for every positive rational epsilon there is N such that for all n >= N the
      number of elements of F among the first n positive integers is at most epsilon * n.
    Definitions: [x160_density_zero F] - the cross-multiplied natural-density-zero condition just
      described, epsilon being given as a positive rational (this file); [x160_count_up_to F n] -
      how many of 1, ..., n belong to F (this file); [x3_positive_integer_set],
      [x3_infinite_integer_set], [x3_constricting] - the audited constricting-set vocabulary, where
      constricting means k-constricting for every k, i.e. for every k some n forces every graph of
      chromatic number at least n to have a clique of size k or a hole with length in F (X3.v).
    Notes: The corpus row is a QUESTION; the Rocq body is its affirmative reading, which the
      authors conjecture to be the right one. The set is here a boolean predicate [nat -> bool],
      coerced to the [nat -> Prop] interface of the X3 vocabulary. *)
Definition density_zero_constricting_set_statement : Prop :=
  exists F : nat -> bool,
    [/\ x3_positive_integer_set (fun n : nat => F n),
        x3_infinite_integer_set (fun n : nat => F n),
        x3_constricting (fun n : nat => F n) &
        x160_density_zero F].
