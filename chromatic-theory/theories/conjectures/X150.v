(** * Chromatic.conjectures.X150 -- v2 surface 3-colourability algorithm row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X150 vocabulary ***********************************************)

Definition x150_embeddable_in_fixed_surface (surface : nat) (G : sgraph) : Prop :=
  surface_embeddable surface G.

Definition x150_polytime_decides_3_colourability_on_surface (surface : nat) : Prop :=
  polytime_decides_graph_on
    (fun G : sgraph => x150_embeddable_in_fixed_surface surface G /\ girth_geq G 4)
    (fun G : sgraph => χ([set: G]) <= 3).

(** ** X150 statements *****************************************************)

(** Corpus row: studies:std_gimbel_thomassen_problem_3
    Site: none
    Review: none
    English statement: (Gimbel and Thomassen, Problem 3, studies slice of the corpus)
      For every fixed surface, given as a genus bound, there is a polynomial-time algorithm deciding
      whether a triangle-free graph embeddable in that surface has chromatic number at most 3.
    Definitions: [x150_embeddable_in_fixed_surface surface G] - a synonym for base's
      [surface_embeddable surface G], i.e. G has a rotation system whose Euler-formula genus is at
      most the bound (this file, GTBase base/theories/surface.v);
      [x150_polytime_decides_3_colourability_on_surface surface] - [polytime_decides_graph_on]
      applied to the class of such graphs of girth at least 4 and the property chi <= 3 (this file);
      [polytime_decides_graph_on Class P] - a program decides P correctly on the encodings of all
      graphs in Class within a polynomial time bound (GTBase base/theories/complexity.v); [girth_geq
      G 4] - triangle-freeness for simple graphs (base.v).
    Notes: PROXY ENCODING, corpus leg partial. The faithfulness audit of 2026-07-17, recorded in
      meta/BLOCKED_RETARGETING_AUDIT.md and in the row's verification_note, observes that
      [surface_euler_genus] computes the ORIENTABLE genus from a rotation system, so the natural
      parameter ranges over orientable surfaces only and all non-orientable surfaces, such as the
      projective plane and the Klein bottle, are silently excluded from the statement. The corpus
      row is also a QUESTION, while the Rocq body asserts the affirmative answer. Triangle-freeness
      is expressed as girth at least 4. The body is left untouched here, WP4 changes comments only.
      V counts every vertex including isolated ones (base fix 2026-09-23): the old count saw
      only the vertices carrying a dart, so the Euler count overstated the genus of every
      graph with an isolated vertex and this hypothesis admitted fewer graphs than intended. *)
Definition gimbel_thomassen_triangle_free_surface_three_colourability_polytime_statement : Prop :=
  forall surface : nat, x150_polytime_decides_3_colourability_on_surface surface.
