(** * Chromatic.conjectures.X149 -- v2 4-chromatic planar fractional row *)

From GTBase Require Export base.
From Chromatic.conjectures Require Import X130.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Corpus row: studies:std_gimbel_k_ndgen_li_thomassen_conjecture
    Site: none
    Review: none
    English statement: (Gimbel, Kundgen, Li and Thomassen, studies slice of the corpus)
      Every planar finite simple graph with chromatic number exactly 4 has fractional chromatic
      number strictly greater than 3.
    Definitions: [x130_frac_chi_le G p q] - the fractional chromatic number of G is at most p/q,
      witnessed by an (a:b)-fold colouring with a*q <= p*b (X130.v); [wagner_planar G] - no K5 and
      no K3,3 minor, i.e. planarity (GTBase base/theories/base.v).
    Notes: This row has no site or review page in the corpus, hence the literal "none" above. The
      strict inequality chi_f(G) > 3 is encoded as the NEGATION of the audited relation
      [x130_frac_chi_le G 3 1], i.e. "it is not the case that chi_f(G) <= 3", which is faithful
      because the fractional chromatic number of a finite graph is attained and rational. *)
Definition gimbel_kundgen_li_thomassen_four_chromatic_planar_fractional_statement : Prop :=
  forall G : sgraph,
    wagner_planar G ->
    χ([set: G]) = 4 ->
    ~ x130_frac_chi_le G 3 1.

