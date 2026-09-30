(** * Digraph.conjectures.X16 -- v2 quasi-kernel rows *)

From HB Require Import structures.
From mathcomp Require Import all_boot.
From Digraph Require Import prelude digraph oriented.
From Digraph.conjectures Require Import X2.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X16 vocabulary ************************************************)

Definition x16_loopless (D : diGraphType) : Prop :=
  forall v : D, ~~ (v --> v).

(** Rocq's [diGraphType] permits loops; the source convention for "no source" is
    loopless digraphs, so an in-neighbour is required to be distinct. *)
Definition x16_no_sources (D : diGraphType) : Prop :=
  forall v : D, [exists u : D, (u != v) && (u --> v)].

Definition x16_one_covered_set (D : diGraphType) (K : {set D}) : {set D} :=
  [set v : D | @x2_covers1 D K v].

(** ** X16 statements ******************************************************)

(** Corpus row: studies:std_small_quasi_kernel_conjecture_erd_s_sz_kely
    Site: none
    Review: none
    English statement: (P. L. Erdos and L. A. Szekely, Small Quasi-Kernel Conjecture)
      Every finite loopless digraph with no source (every vertex has an in-neighbour distinct
      from itself) has a quasi-kernel K with 2 * #|K| <= #|D|, that is of size at most half the
      order: K contains no arc inside it and every vertex is reached from K by a directed path
      of length at most two.
    Definitions: [x16_loopless D] - no loop (this file); [x16_no_sources D] - every vertex has a
      distinct in-neighbour (this file); [two_kernel K] - K is arc-stable and 2-covers every
      vertex (conjectures/X2.v); [x2_covers2] (conjectures/X2.v).
    Notes: A 2-kernel in the source is the quasi-kernel. The distinctness in the no-source
      condition is load-bearing because [diGraphType] permits loops, and a loop would otherwise
      make a vertex a non-source while barring it from K. The bound |K| <= |G|/2 is cleared of
      division. *)
Definition small_quasi_kernel_statement : Prop :=
  forall D : diGraphType,
    x16_loopless D ->
    x16_no_sources D ->
    exists K : {set D},
      @two_kernel D K /\ (2 * #|K| <= #|D|)%N.

(** Corpus row: studies:std_spiro_s_quasi_kernel_conjecture
    Site: none
    Review: none
    English statement: (Spiro, quasi-kernel half-covered conjecture)
      Every finite loopless digraph D has a quasi-kernel K such that at least half of the
      vertices of D lie in K or have an in-neighbour in K, written without division as #|D| <= 2
      * #|one-covered set of K|.
    Definitions: [x16_loopless D] (this file); [two_kernel K] (conjectures/X2.v);
      [x16_one_covered_set K] - the vertices that are in K or have an in-neighbour in K (this
      file); [x2_covers1] (conjectures/X2.v).
    Notes: No no-source hypothesis here, matching the source; the empty digraph satisfies the
      inequality with K empty. *)
Definition spiro_quasi_kernel_half_covered_statement : Prop :=
  forall D : diGraphType,
    x16_loopless D ->
    exists K : {set D},
      @two_kernel D K /\ (#|D| <= 2 * #|x16_one_covered_set K|)%N.
