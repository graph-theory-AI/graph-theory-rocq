(** * Minor.conjectures.X8 -- v2 clean list-colouring/minor rows *)

From GraphTheory Require Import minor.
From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** X8 statements *******************************************************)

(** Corpus row: arxiv:2201.09115#00
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/2201.09115__00/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/2201.09115__00.json
    English statement: (Steiner 2022, "Disproof of a Conjecture by Woodall", Question 1)
      Two questions, conjoined: every finite simple graph with no minor isomorphic to the
      complete bipartite graph K_(4,4) has list chromatic number at most 7; and every finite
      simple graph with no minor isomorphic to K_(3,5) has list chromatic number at most 7.
    Definitions: standard
    Notes: [KB s t] is the complete bipartite graph K_(s,t) (coq-graph-theory); 7-choosability
      is stated through the choice number, as the hypothesis [is_choice_number G ch] (GTBase:
      ch is the least k for which G is k-choosable) followed by [ch <= 7].  For a finite graph
      the choice number always exists, so the implicational shape loses nothing. *)
Definition kt_minor_free_seven_choosable_statement : Prop :=
  (forall (G : sgraph) (ch : nat),
      ~ minor G (KB 4 4) ->
      is_choice_number G ch ->
      ch <= 7) /\
  forall (G : sgraph) (ch : nat),
      ~ minor G (KB 3 5) ->
      is_choice_number G ch ->
      ch <= 7.

(** Corpus row: arxiv:2201.09115#01
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/2201.09115__01/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/2201.09115__01.json
    English statement: (Steiner 2022, "Disproof of a Conjecture by Woodall", Question 2)
      For all integers s and t with 1 <= s <= t, every finite simple graph with no minor
      isomorphic to the complete bipartite graph K_(s,t) has list chromatic number at most
      2s + t.
    Definitions: standard
    Notes: as in the previous row, the list chromatic number is the GTBase choice number
      [is_choice_number G ch], introduced as a hypothesis and then bounded.  [KB s t] is
      K_(s,t) (coq-graph-theory).  The bound 2s + t involves no subtraction, so no natural
      truncation issue arises. *)
Definition kt_minor_free_two_s_plus_t_choosable_statement : Prop :=
  forall (s t ch : nat) (G : sgraph),
    1 <= s -> s <= t ->
    ~ minor G (KB s t) ->
    is_choice_number G ch ->
    ch <= 2 * s + t.
