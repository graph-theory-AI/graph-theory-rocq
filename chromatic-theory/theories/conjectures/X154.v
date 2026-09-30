(** * Chromatic.conjectures.X154 -- v2 duplicate fixed-surface 4-colourability row *)

From Chromatic.conjectures Require Import X152.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Corpus row: arxiv:1404.6356#00
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/1404.6356__00/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/1404.6356__00.json
    English statement: (Dvorak, Kral and Thomas 2020, open step in Thomassen's program, arXiv:1404.6356)
      Whether 4-colourability of graphs embedded in a fixed surface can be decided in polynomial
      time. The Rocq body is literally the X152 statement, reused as a synonym so that this
      duplicate corpus row cannot drift from it: for every fixed surface of positive genus there is
      a polynomial-time algorithm deciding whether an embeddable graph has chromatic number at most
      4.
    Definitions: [fixed_surface_four_colourability_polytime_statement] - the X152 encoding,
      [polytime_decides_graph_on] on the class of graphs embeddable in a fixed surface for the
      property chi <= 4 (X152.v).
    Notes: PROXY ENCODING inherited from X152, corpus leg partial: the surface primitive expresses
      orientable genus only, so non-orientable surfaces are excluded, and the corpus row is a remark
      about an open question while the Rocq body asserts the affirmative answer. See
      meta/BLOCKED_RETARGETING_AUDIT.md. *)
Definition fixed_surface_four_colourability_polytime_duplicate_statement : Prop :=
  fixed_surface_four_colourability_polytime_statement.
