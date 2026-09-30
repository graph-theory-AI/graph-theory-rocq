(** * GTMisc.conjectures.X99 -- v2 hat guessing versus Hadwiger row *)

From GTBase Require Export base.
From GraphTheory Require Import minor.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X99 vocabulary ************************************************)

Definition x99_hat_strategy (G : sgraph) (q : nat) :=
  forall v : G, (G -> 'I_q) -> 'I_q.

Definition x99_local_strategy
    (G : sgraph) (q : nat) (guess : x99_hat_strategy G q) : Prop :=
  forall (v : G) (a b : G -> 'I_q),
    (forall u : G, u -- v -> a u = b u) ->
    guess v a = guess v b.

Definition x99_winning_hat_strategy (G : sgraph) (q : nat) : Prop :=
  exists guess : x99_hat_strategy G q,
    x99_local_strategy guess /\
    forall hats : G -> 'I_q,
      [exists v : G, guess v hats == hats v].

Definition x99_hat_guessing_number_at_most (G : sgraph) (k : nat) : Prop :=
  forall q : nat, k < q -> ~ x99_winning_hat_strategy G q.

Definition x99_hadwiger_number (G : sgraph) (h : nat) : Prop :=
  minor G 'K_h /\
  forall t : nat, minor G 'K_t -> t <= h.

(** ** X99 statements ******************************************************)

(** Corpus row: studies:std_bosek_dudek_farnik_grytczuk_mazur_conjecture_hat
    Site: none
    Review: none
    English statement: (Bosek, Dudek, Farnik, Grytczuk and Mazur, conjecture that the hat
      guessing number is at most the Hadwiger number)
      For every finite simple graph G whose largest complete minor has h vertices, and for
      every number of hat colours q > h, the players have no winning strategy in the hat
      guessing game on G; that is, the hat guessing number of G is at most its Hadwiger
      number.
    Definitions: [x99_hat_strategy G q] - a guess for each vertex as a function of the whole
      colouring (this file); [x99_local_strategy guess] - the guess at v depends only on the
      colours of the neighbours of v (this file); [x99_winning_hat_strategy G q] - a local
      strategy under which, for every assignment of q colours to the vertices, at least one
      vertex guesses its own colour (this file); [x99_hat_guessing_number_at_most G k] - no
      winning strategy exists for any q > k (this file); [x99_hadwiger_number G h] - the
      complete graph on h vertices is a minor of G and no larger complete graph is (this
      file); [minor], ['K_h] - coq-graph-theory.
    Notes: locality is imposed as an explicit hypothesis on the strategy (the guess sees only
      the neighbours' hats), which is the rule of the game.  The hat guessing number is stated
      in the negative form "no winning strategy for more than k colours", which is its
      definition as the largest q for which the players win, and avoids naming that largest q
      as a function. *)
Definition hat_guessing_number_hadwiger_bound_statement : Prop :=
  forall (G : sgraph) (h : nat),
    x99_hadwiger_number G h ->
    x99_hat_guessing_number_at_most G h.
