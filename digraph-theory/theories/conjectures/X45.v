(** * Digraph.conjectures.X45 -- v2 majority 3-colouring row *)

From HB Require Import structures.
From mathcomp Require Import all_boot.
From Digraph Require Import prelude digraph oriented.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X45 vocabulary ************************************************)

Definition x45_same_colour_outneighbours
    (D : diGraphType) (col : D -> 'I_3) (v : D) : nat :=
  #|[set w : D | (v --> w) && (col w == col v)]|.

(** ** X45 statements ******************************************************)

(** Corpus row: arxiv:1608.03040#02
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/1608.03040__02/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/1608.03040__02.json
    English statement: (Kreutzer, Oum, Seymour, van der Zypen, Wood 2016, arXiv:1608.03040, Open Problem 1)
      Every finite digraph has a colouring of its vertices by three colours in which every
      vertex v has at most half of its out-neighbours coloured like v, written without division
      as 2 * #(out-neighbours of v with the colour of v) <= outdeg v.
    Definitions: [x45_same_colour_outneighbours col v] - the number of out-neighbours of v
      carrying the colour of v (this file); [outdeg v] (core/oriented.v).
    Notes: DISCREPANCY: the corpus row asks whether SOME constant beta < 1 works (at most beta
      times the out-degree share the colour); the body encodes the specific value beta = 1/2,
      which is the strictly stronger majority 3-colouring conjecture, identical to
      [majority_3col_statement] in conjectures/colouring_variants.v (row arxiv:1608.03040#00).
      Recorded in meta/STATEMENT_IMPROVEMENTS.md. *)
Definition majority_three_colouring_beta_statement : Prop :=
  forall D : diGraphType,
    exists col : D -> 'I_3,
      forall v : D,
        (2 * x45_same_colour_outneighbours col v <= outdeg v)%N.
