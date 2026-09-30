(** * Chromatic.conjectures.X131 -- v2 duplicate Dvorak-Mnich fractional row *)

From Chromatic.conjectures Require Import X130.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Corpus row: studies:std_dvo_k_mnich_conjecture_fractional_chromatic_numb_186
    Site: none
    Review: none
    English statement: (Dvorak and Mnich, studies slice of the corpus, duplicate row)
      For some epsilon > 0, every planar finite simple graph of girth at least five has fractional
      chromatic number at most 3 - epsilon. This is the same conjecture as the X130 row, and the
      Rocq body is literally the X130 statement, reused as a synonym so that the two corpus rows
      cannot drift apart.
    Definitions: [dvorak_mnich_planar_girth5_fractional_chromatic_statement] - the X130 encoding,
      a rational bound p/q < 3 on the fractional chromatic number of planar graphs of girth at least
      5 (X130.v).
    Notes: This row has no site or review page in the corpus, hence the literal "none" above. The
      corpus contains this conjecture twice, phrased once with a real c < 3 and once with 3 -
      epsilon; the two phrasings are equivalent, and only one encoding exists. *)
Definition dvorak_mnich_planar_girth5_fractional_chromatic_duplicate_statement : Prop :=
  dvorak_mnich_planar_girth5_fractional_chromatic_statement.

