(** * Chromatic.conjectures.X152 -- v2 fixed-surface 4-colourability algorithm row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X152 vocabulary ***********************************************)

Definition x152_embeddable_in_fixed_surface (surface : nat) (G : sgraph) : Prop :=
  surface_embeddable surface G.

Definition x152_polytime_decides_four_colourability (surface : nat) : Prop :=
  polytime_decides_graph_on
    (fun G : sgraph => x152_embeddable_in_fixed_surface surface G)
    (fun G : sgraph => χ([set: G]) <= 4).

(** ** X152 statements *****************************************************)

(** Corpus row: arxiv:1010.2472#00
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/1010.2472__00/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/1010.2472__00.json
    English statement: (Dvorak, Kral and Thomas 2016, open problem, arXiv:1010.2472)
      For every fixed surface other than the sphere, given as a positive genus bound, there is a
      polynomial-time algorithm deciding whether a graph embeddable in that surface has chromatic
      number at most 4.
    Definitions: [x152_embeddable_in_fixed_surface surface G] - a synonym for base's
      [surface_embeddable surface G], i.e. G has a rotation system whose Euler-formula genus is at
      most the bound (this file, GTBase base/theories/surface.v);
      [x152_polytime_decides_four_colourability surface] - [polytime_decides_graph_on] applied to
      that class and the property chi <= 4 (this file); [polytime_decides_graph_on] (GTBase
      base/theories/complexity.v).
    Notes: PROXY ENCODING, corpus leg partial. Per the faithfulness audit of 2026-07-17,
      meta/BLOCKED_RETARGETING_AUDIT.md, the surface model is load-bearing and lightweight:
      [surface_euler_genus] is computed from a pure rotation system and is the ORIENTABLE genus, so
      non-orientable surfaces cannot be expressed and are silently excluded. The same audit checked
      that the statement is not trivially true: for positive genus the class contains both graphs
      with chi <= 4 and graphs with chi > 4, for instance K5 on the torus, so a constant program
      does not decide it. "Other than the sphere" is encoded as 0 < surface. The corpus row is a
      QUESTION; the Rocq body asserts the affirmative answer.
      V counts every vertex including isolated ones (base fix 2026-09-23): the old count saw
      only the vertices carrying a dart, so the Euler count overstated the genus of every
      graph with an isolated vertex and this hypothesis admitted fewer graphs than intended. *)
Definition fixed_surface_four_colourability_polytime_statement : Prop :=
  forall surface : nat,
    0 < surface -> x152_polytime_decides_four_colourability surface.
