(** * Digraph.conjectures.X71 -- v2 directed Gyarfas-Sumner row *)

From HB Require Import structures.
From mathcomp Require Import all_boot.
From Digraph Require Import prelude interop_graph_theory digraph oriented.
From Digraph.conjectures Require Import chi_bounded dichromatic heroes.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X71 vocabulary ************************************************)

Definition x71_oriented_forb_ind (F D : diGraphType) : Prop :=
  chi_bounded.oriented_dg D /\ ind_free F D.

(** ** X71 statements ******************************************************)

(** Corpus row: studies:std_aboulker_charbit_naserasr_conjecture_directed_gy
    Site: none
    Review: none
    English statement: (Aboulker, Charbit and Naserasr, directed Gyarfas-Sumner conjecture: Forb_ind(F) is chi-vec-bounded for every oriented forest F)
      For every oriented forest F there is a function f such that every oriented graph with no
      induced copy of F has dichromatic number at most f applied to the clique number of its
      underlying simple graph.
    Definitions: [x71_oriented_forb_ind F D] - D is oriented and has no induced copy of F (this
      file); [chi_bounded.oriented_dg] and [chi_bounded.oriented_forest] and
      [chi_bounded.underlying] (conjectures/chi_bounded.v); [ind_free] (conjectures/heroes.v);
      [dicolorableb D k] (conjectures/dichromatic.v); [omega] - coq-graph-theory's clique
      number.
    Notes: chi-vec-bounded is a FUNCTION bound in the directed clique number, not the constant
      bound [dichromatic_bounded]: the class contains every tournament, and tournaments have
      unbounded dichromatic number, so no uniform constant can work. The directed clique number
      omega-vec is read as the clique number of the underlying graph, a set of pairwise adjacent
      vertices being exactly a semicomplete subdigraph. Adding a forbidden transitive tournament
      bounds omega and yields the constant form
      [directed_gyarfas_sumner_tournament_forest_statement] (conjectures/X123.v). *)
Definition directed_gyarfas_sumner_oriented_forest_dichromatic_statement : Prop :=
  forall F : diGraphType,
    chi_bounded.oriented_dg F ->
    chi_bounded.oriented_forest F ->
    exists f : nat -> nat,
      forall D : diGraphType,
        x71_oriented_forb_ind F D ->
        dicolorableb D (f (ω([set: chi_bounded.underlying D]))).
