(** * Digraph.conjectures.X44 -- v2 even directed-cycle row *)

From HB Require Import structures.
From mathcomp Require Import all_boot.
From Digraph Require Import prelude digraph dipath strong.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X44 vocabulary ************************************************)

Definition x44_p_strongly_connected (D : diGraphType) (p : nat) : Prop :=
  p < #|D| /\
  forall S : {set D},
    #|S| < p ->
    strongb (induced_digraph ([set: D] :\: S)).

Definition x44_even_dicycle (D : diGraphType) : Prop :=
  exists c : seq D, dicycle c /\ ~~ odd (size c).

(** ** X44 statements ******************************************************)

(** Corpus row: studies:std_lov_sz_s_even_directed_cycle_conjecture
    Site: none
    Review: none
    English statement: (Lovasz, Even Directed Cycle Conjecture)
      There is an integer p such that every p-strongly-connected finite digraph has a directed
      cycle of even length.
    Definitions: [x44_p_strongly_connected D p] - more than p vertices and deleting any fewer
      than p vertices leaves a strongly connected induced subdigraph (this file);
      [x44_even_dicycle D] - some directed cycle has an even number of vertices (this file);
      [strongb] (invariants/strong.v); [induced_digraph] (core/digraph.v); [dicycle]
      (core/dipath.v).
    Notes: Cycle length is counted in vertices, so even length means even size. The guard p <
      #|D| inside [x44_p_strongly_connected] keeps small digraphs from satisfying the hypothesis
      vacuously. *)
Definition lovasz_even_directed_cycle_statement : Prop :=
  exists p : nat,
    forall D : diGraphType,
      x44_p_strongly_connected D p ->
      x44_even_dicycle D.
