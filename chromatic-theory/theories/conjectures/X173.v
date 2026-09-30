(** * Chromatic.conjectures.X173 -- v2 planar triangle-free fractional row *)

From GTBase Require Export base.
From Chromatic.conjectures Require Import X130.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Corpus row: arxiv:1606.06265#00
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/1606.06265__00/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/1606.06265__00.json
    English statement: (Dvorak, Masarik, Musilek and Pangrac 2016, informal bound, arXiv:1606.06265)
      Every planar triangle-free finite simple graph on n vertices has fractional chromatic number
      at most 3n/(n+1), which is the source's 3 - 3/(n+1).
    Definitions: [x130_frac_chi_le G p q] - the fractional chromatic number of G is at most p/q,
      witnessed by an (a:b)-fold colouring with a*q <= p*b (X130.v); [wagner_planar] (GTBase
      base/theories/base.v); [girth_geq G 4] - triangle-freeness for simple graphs (base.v).
    Notes: The bound 3 - 3/(n+1) is rewritten as the equal fraction 3n/(n+1) so that it can be
      passed to the audited rational relation of X130 without nat subtraction. Triangle-freeness is
      expressed as girth at least 4. *)
Definition planar_triangle_free_fractional_chromatic_bound_statement : Prop :=
  forall G : sgraph,
    wagner_planar G ->
    girth_geq G 4 ->
    x130_frac_chi_le G (3 * #|G|) (#|G|).+1.

