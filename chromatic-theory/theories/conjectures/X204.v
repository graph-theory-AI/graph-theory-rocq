(** * Chromatic.conjectures.X204 -- v2 planar no 4/5-cycle fractional row *)

From GTBase Require Export base.
From Chromatic.conjectures Require Import X130.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X204 vocabulary ***********************************************)

Definition x204_no_cycle_length (G : sgraph) (n : nat) : Prop :=
  forall c : seq G, ucycle (--) c -> 2 < size c -> size c != n.

(** ** X204 statements *****************************************************)

(** Corpus row: arxiv:1802.04179#01
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/1802.04179__01/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/1802.04179__01.json
    English statement: (Dvorak and Hu 2019, informal conjecture on the optimality of 11/3, arXiv:1802.04179)
      There are naturals p and q with q > 0 and 3p < 11q, i.e. p/q < 11/3, such that every planar
      finite simple graph with no cycle of length 4 and no cycle of length 5 has fractional
      chromatic number at most p/q.
    Definitions: [x204_no_cycle_length G n] - G has no cycle with exactly n vertices (this file);
      [x130_frac_chi_le G p q] - the fractional chromatic number is at most p/q, witnessed by an
      (a:b)-fold colouring (X130.v); [wagner_planar] (GTBase base/theories/base.v).
    Notes: The source only says the authors suspect that 11/3 is not optimal; the Rocq body turns
      this into the precise assertion that some uniform rational bound strictly below 11/3 holds for
      the whole class. Corpus status: partial, the suspicion was confirmed by Xu and Zhu 2025 with
      the bound 7/2. *)
Definition planar_no_4_5_cycles_fractional_below_eleven_thirds_statement : Prop :=
  exists p q : nat,
    [/\ 0 < q, 3 * p < 11 * q &
      forall G : sgraph,
        wagner_planar G ->
        x204_no_cycle_length G 4 ->
        x204_no_cycle_length G 5 ->
        x130_frac_chi_le G p q].

