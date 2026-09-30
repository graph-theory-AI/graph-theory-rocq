(** * GTMisc.conjectures.X144 -- v2 pure pairs in perfect graphs row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X144 vocabulary ***********************************************)

Definition x144_perfect_graph (G : sgraph) : Prop :=
  forall S : {set G}, χ([set: induced S]) = ω([set: induced S]).

Definition x144_complete_between (G : sgraph) (A B : {set G}) : Prop :=
  forall a b : G, a \in A -> b \in B -> a -- b.

Definition x144_anticomplete_between (G : sgraph) (A B : {set G}) : Prop :=
  forall a b : G, a \in A -> b \in B -> ~~ (a -- b).

Definition x144_pure_pair (G : sgraph) (A B : {set G}) : Prop :=
  [disjoint A & B] /\
  A != set0 /\
  B != set0 /\
  (x144_complete_between A B \/ x144_anticomplete_between A B).

(** ** X144 statements *****************************************************)

(** Corpus row: studies:std_fox_s_pure_pair_conjecture_for_perfect_graphs
    Site: none
    Review: none
    English statement: (Fox, pure-pair conjecture for perfect graphs)
      For every rational e1/e2 with 0 < e1 < e2 there is an N such that every perfect graph G
      on n >= N vertices contains two disjoint non-empty vertex sets A and B that are either
      completely adjacent or completely non-adjacent and satisfy n^(e2-e1) <= |A|^e2 and
      n^(e2-e1) <= |B|^e2, i.e. |A|, |B| >= n^(1 - e1/e2).
    Definitions: [x144_perfect_graph G] - every induced subgraph of G has chromatic number
      equal to its clique number (this file); [x144_complete_between A B] /
      [x144_anticomplete_between A B] - every vertex of A is adjacent to / non-adjacent to every
      vertex of B (this file); [x144_pure_pair A B] - A and B are disjoint, non-empty, and one
      of the two previous conditions holds (this file); [chi], [omega], [induced] -
      coq-graph-theory colouring and induced subgraphs.
    Notes: the source exponent n^(1-o(1)) is rendered in the standard rational-epsilon form:
      the bound is asked for every rational epsilon = e1/e2 strictly between 0 and 1, with the
      threshold N chosen after epsilon, and the inequality |A| >= n^(1-epsilon) is stated
      fraction-free as n^(e2-e1) <= |A|^e2.  Perfection is required of G itself through the
      induced-subgraph definition, so no separate hereditary hypothesis is needed. *)
Definition fox_pure_pair_perfect_graphs_statement : Prop :=
  forall e1 e2 : nat,
    0 < e1 ->
    e1 < e2 ->
    exists N : nat,
      forall (n : nat) (G : sgraph),
        N <= n ->
        #|G| = n ->
        x144_perfect_graph G ->
        exists A B : {set G},
          x144_pure_pair A B /\
          n ^ (e2 - e1) <= #|A| ^ e2 /\
          n ^ (e2 - e1) <= #|B| ^ e2.

