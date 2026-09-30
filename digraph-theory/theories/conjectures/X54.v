(** * Digraph.conjectures.X54 -- v2 odd directed-cycle chi-bound row *)

From HB Require Import structures.
From mathcomp Require Import all_boot.
From Digraph Require Import prelude interop_graph_theory digraph dipath.
From Digraph.conjectures Require Import chi_bounded dichromatic.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X54 vocabulary ************************************************)

Definition x54_no_induced_odd_dicycle (D : diGraphType) : Prop :=
  ~ exists c : seq D,
      dicycle c /\ odd (size c) /\
      (forall u v : D, u \in c -> v \in c -> u --> v -> next c u = v).

(** ** X54 statements ******************************************************)

(** Corpus row: arxiv:2201.08204#01
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/2201.08204__01/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/2201.08204__01.json
    English statement: (Carbonero, Hompe, Moore, Spirkl 2022, A counterexample to a conjecture about triangle-free induced subgraphs of graphs with large chromatic number, arXiv:2201.08204, Question 3.2)
      There is a function f such that every finite digraph with no induced directed cycle of odd
      length has dichromatic number at most f applied to the clique number of its underlying
      simple graph.
    Definitions: [x54_no_induced_odd_dicycle D] - no directed cycle of odd size whose only arcs
      among its vertices are its own forward arcs (this file); [dicolorableb D k] - dichromatic
      number at most k (conjectures/dichromatic.v); [chi_bounded.underlying]
      (conjectures/chi_bounded.v); [omega] - coq-graph-theory's clique number.
    Notes: The corpus poses the question; the body encodes the affirmative answer. The clique
      number omega(D) of the source is read as the clique number of the underlying simple graph,
      which for digraphs is the size of the largest semicomplete vertex set. *)
Definition odd_dicycle_free_dichromatic_chi_bound_statement : Prop :=
  exists f : nat -> nat,
    forall D : diGraphType,
      x54_no_induced_odd_dicycle D ->
      dicolorableb D (f (ω([set: chi_bounded.underlying D]))).
