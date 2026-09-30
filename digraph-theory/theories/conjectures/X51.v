(** * Digraph.conjectures.X51 -- v2 majority choosability row *)

From HB Require Import structures.
From mathcomp Require Import all_boot.
From Digraph Require Import prelude digraph oriented.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X51 vocabulary ************************************************)

Definition x51_same_colour_outneighbours
    (D : diGraphType) (C : finType) (col : D -> C) (v : D) : nat :=
  #|[set w : D | (v --> w) && (col w == col v)]|.

Definition x51_majority_colouring
    (D : diGraphType) (C : finType) (col : D -> C) : Prop :=
  forall v : D,
    (2 * x51_same_colour_outneighbours col v <= outdeg v)%N.

Definition x51_respects_lists
    (D : diGraphType) (C : finType) (L : D -> {set C}) (col : D -> C) : Prop :=
  forall v : D, col v \in L v.

(** ** X51 statements ******************************************************)

(** Corpus row: arxiv:1608.03040#06
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/1608.03040__06/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/1608.03040__06.json
    English statement: (Kreutzer, Oum, Seymour, van der Zypen, Wood 2016, arXiv:1608.03040, Open Problem 7)
      There is a constant c >= 1 such that every finite digraph is majority c-choosable: for
      every assignment of a colour list of size at least c to each vertex there is a colouring
      picking each vertex's colour from its own list in which every vertex has at most half of
      its out-neighbours coloured like itself.
    Definitions: [x51_majority_colouring col] - at most half of the out-neighbours share the
      colour, written as 2 * #same <= outdeg (this file); [x51_respects_lists L col] - each
      vertex is coloured from its own list (this file); [x51_same_colour_outneighbours] (this
      file); [outdeg] (core/oriented.v).
    Notes: The colour universe is an arbitrary finite type quantified inside the statement, so a
      single c works for lists over any palette. *)
Definition majority_choosable_universal_constant_statement : Prop :=
  exists c : nat,
    0 < c /\
    forall (D : diGraphType) (C : finType) (L : D -> {set C}),
      (forall v : D, c <= #|L v|) ->
      exists col : D -> C,
        x51_respects_lists L col /\
        x51_majority_colouring col.
