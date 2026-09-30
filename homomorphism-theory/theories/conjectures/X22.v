(** * Hom.conjectures.X22 -- v2 planar high-girth homomorphism row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** X22 statements ******************************************************)

(** Corpus row: studies:std_jaeger_s_conjecture_high_girth_planar_graphs_and
    Site: none
    Review: none
    English statement: (Jaeger, studies row "Jaeger's Conjecture (high-girth
      planar graphs and odd-cycle homomorphisms)") For every k >= 1 and every
      planar graph G all of whose cycles have length at least 4k, there is a
      homomorphism from G to the odd cycle on 2k+1 vertices.
    Definitions: [wagner_planar G] - G has neither K5 nor K3,3 as a minor, which
      by Wagner's theorem is exactly planarity (base/theories/base.v);
      [girth_geq G (4*k)] - every genuine cycle has length at least 4k (base.v);
      [cycle_graph (2*k+1)] - the odd cycle C_(2k+1) (base.v); [homs_to G H] -
      an adjacency-preserving map from G to H exists (base.v).
    Notes: the corpus text adds the equivalent reformulation "the circular
      chromatic number of G is at most (2k+1)/k"; only the homomorphism form is
      formalised, the circular chromatic number not being in the vocabulary.
      The same mathematics is formalised a second time in
      homomorphism-theory/theories/conjectures/U3.v as the OPG row
      opg:mapping_planar_graphs_to_odd_cycles. *)
Definition jaeger_high_girth_planar_odd_cycle_hom_statement : Prop :=
  forall (k : nat) (G : sgraph),
    1 <= k ->
    wagner_planar G ->
    girth_geq G (4 * k) ->
    homs_to G (cycle_graph (2 * k + 1)).
