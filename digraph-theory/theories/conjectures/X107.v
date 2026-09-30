(** * Digraph.conjectures.X107 -- v2 oriented Ramsey row *)

From HB Require Import structures.
From mathcomp Require Import all_boot.
From Digraph Require Import prelude digraph oriented tournament dichromatic.
From Digraph.conjectures Require Import X2.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X107 vocabulary ***********************************************)

Definition x107_total_degree_at_most (D : diGraphType) (Delta : nat) : Prop :=
  let indeg v := #|[set u : D | u --> v]| in
  forall v : D, outdeg v + indeg v <= Delta.

Definition x107_oriented_ramsey_at_most (H : diGraphType) (N : nat) : Prop :=
  forall T : tournament,
    N <= #|T| ->
    subdigraph_embed H T.

(** ** X107 statements *****************************************************)

(** Corpus row: studies:std_buci_letzter_sudakov_problem_oriented_ramsey_num
    Site: none
    Review: none
    English statement: (Bucic, Letzter and Sudakov, oriented Ramsey number of bounded-degree acyclic digraphs)
      For every Delta there is a constant C such that every acyclic digraph H on n vertices in
      which every vertex has in-degree plus out-degree at most Delta has oriented Ramsey number
      at most C times n: every tournament with at least C * n vertices contains H as a
      subdigraph via an injective arc-preserving map.
    Definitions: [x107_total_degree_at_most H Delta] - in-degree plus out-degree is at most
      Delta at every vertex (this file); [x107_oriented_ramsey_at_most H N] - every tournament
      on at least N vertices contains H (this file); [subdigraph_embed H T] - injective
      arc-preserving map (conjectures/X2.v); [acyclicb] (conjectures/dichromatic.v);
      [tournament] (core/tournament.v).
    Notes: The asymptotic statement oriented Ramsey number is O_Delta(n) is encoded by an
      explicit constant C depending only on Delta, which is the combinatorial content; maximum
      degree is read as total (in plus out) degree. *)
Definition bounded_degree_acyclic_oriented_ramsey_linear_statement : Prop :=
  forall Delta : nat,
    exists C : nat,
      forall (n : nat) (H : diGraphType),
        #|H| = n ->
        acyclicb H ->
        x107_total_degree_at_most H Delta ->
        x107_oriented_ramsey_at_most H (C * n).
