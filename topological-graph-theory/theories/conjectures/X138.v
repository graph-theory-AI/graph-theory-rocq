(** * Topological.conjectures.X138 -- v2 clustered-colouring on surfaces row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X138 vocabulary ***********************************************)

Definition x138_embeddable_on_surface (surface : nat) (G : sgraph) : Prop :=
  surface_embeddable surface G.

Definition x138_clustered_two_colourable (G : sgraph) : Prop :=
  clustered_chromatic_at_most G 2.

Definition x138_clustered_two_colourable_with_clustering
    (c : nat) (G : sgraph) : Prop :=
  clustered_colouring G 2 c.

(** ** X138 statements *****************************************************)

(** Corpus row: studies:std_esperet_joret_question_on_clustered_colouring_of
    Site: none
    Review: none
    English statement: (Esperet, Joret, "Question on clustered colouring of triangle-free
      bounded-degree graphs on surfaces", studies slice)
      For every surface and every degree bound D, is the class of triangle-free graphs of
      maximum degree at most D embeddable in that surface of clustered chromatic number at
      most two?  The Rocq body asserts it positively, with the clustering constant pulled
      OUTSIDE the graph quantifier: for all naturals [surface] and D there is a c such that
      every finite simple graph G of girth at least 4 and maximum degree at most D that
      embeds with Euler genus at most [surface] has a 2-colouring in which every connected
      monochromatic vertex set has at most c vertices.
    Definitions: [x138_embeddable_on_surface surface G] - a thin wrapper for
      [surface_embeddable surface G], i.e. G admits a rotation system of Euler genus at most
      [surface] (base/theories/surface.v); [x138_clustered_two_colourable_with_clustering c G]
      - a wrapper for [clustered_colouring G 2 c] (base/theories/surface.v);
      [x138_clustered_two_colourable] - a wrapper for [clustered_chromatic_at_most G 2], not
      used by the statement (this file); [girth_geq G 4] - every genuine cycle has length at
      least 4 (base/theories/base.v); [Delta G] - maximum degree (base/theories/base.v).
    Notes: (1) The quantifier order is load-bearing and was fixed by the 2026-07-17
      faithfulness re-encoding: "the CLASS has clustered chromatic number at most two"
      requires one constant c uniform over the class, so [exists c] must precede
      [forall G], not follow it.  (2) Triangle-freeness is written as girth at least 4, which
      for simple graphs is equivalent to base's [triangle_free] but is a different notion
      when read literally; see the ledger.  (3) The surface is a natural number bounding the
      ORIENTABLE Euler genus computed from a rotation system (base/theories/surface.v), not a
      classified surface, and non-orientable surfaces are not reachable - a proxy, since the
      source quantifies over all surfaces.  (4) The three [x138_*] names are pure aliases of
      base notions; see the ledger.
      V counts every vertex including isolated ones (base fix 2026-09-23): the old count saw
      only the vertices carrying a dart, so the Euler count overstated the genus of every
      graph with an isolated vertex and this hypothesis admitted fewer graphs than intended. *)
Definition esperet_joret_surface_triangle_free_clustered_two_colouring_statement : Prop :=
  forall surface Delta0 : nat,
    exists c : nat,
      forall G : sgraph,
        girth_geq G 4 ->
        Delta G <= Delta0 ->
        x138_embeddable_on_surface surface G ->
        x138_clustered_two_colourable_with_clustering c G.
