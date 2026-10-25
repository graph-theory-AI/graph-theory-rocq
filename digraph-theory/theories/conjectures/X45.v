(** * Digraph.conjectures.X45 -- v2 majority 3-colouring row *)

From HB Require Import structures.
From mathcomp Require Import all_boot.
From Digraph Require Import prelude digraph oriented.
From Digraph.conjectures Require Import two_extremal.

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
      There is a constant beta < 1, written as a fraction p/q of natural numbers with p < q,
      such that every finite loopless digraph has a colouring of its vertices by three colours
      in which every vertex v has at most beta times its out-degree out-neighbours coloured
      like v, written without division as q * #(out-neighbours of v with the colour of v) <=
      p * outdeg v.
    Definitions: [x45_same_colour_outneighbours col v] - the number of out-neighbours of v
      carrying the colour of v (this file); [outdeg v] (core/oriented.v); [loopless D] - no
      vertex carries a loop (conjectures/two_extremal.v).
    Notes: RE-ENCODED 2026-10-25 (coordination/PROGRAMME.md, A1). Until then the body fixed
      beta = 1/2 over all digraphs, which restated the strictly stronger majority 3-colouring
      conjecture [majority_3col_statement] of conjectures/colouring_variants.v (row
      arxiv:1608.03040#00), and a one-vertex digraph with a loop refuted it
      (meta/probe_hints/majority_three_colouring_beta_statement.v). Now beta is existential,
      as the source asks. A rational beta loses nothing: a real beta < 1 that works can be
      raised to a rational one below 1, and no negative beta works on a digraph with an arc.
      The guard [loopless D] is load-bearing: [diGraphType] allows loops, a loop makes v an
      out-neighbour of itself carrying its own colour, and the one-vertex digraph with a loop
      then violates the bound for every beta < 1, so the question presupposes loopless
      digraphs. The old body implies the new one (beta = 1/2); the converse is open. The
      pinned review records the question as solved: Knox and Samal (2018) give beta = 2/3.
      Recorded in meta/STATEMENT_IMPROVEMENTS.md. *)
Definition majority_three_colouring_beta_statement : Prop :=
  exists p q : nat, (p < q)%N /\
    forall D : diGraphType, loopless D ->
      exists col : D -> 'I_3,
        forall v : D,
          (q * x45_same_colour_outneighbours col v <= p * outdeg v)%N.
