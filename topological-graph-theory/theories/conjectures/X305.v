(** * Topological.conjectures.X305 -- v2 row: the Earth-Moon sub-bracket chi_EM <= 11 (derived row
      drv_earthmoon_chiem_le_11): every biplanar graph is 11-colourable *)

From GTBase Require Import base.
From Topological.conjectures Require Import U13.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** X305 statement ******************************************************)

(** Reused vocabulary: U13's [union_of_two_planar] (the Earth-Moon problem's biplanarity, U13.v), GTBase.base
    [wagner_planar] (no K_5 and no K_(3,3) minor) and coq-graph-theory's chromatic number.  X305 declares no helper
    of its own. *)

(** Corpus row: derived:drv_earthmoon_chiem_le_11
    Site: none
    Review: none
    English statement: (corpus derived row chiEM-le-11, folder earth_moon_problem, ledger e62bc77e: the upper half
      of the Earth-Moon bracket; Ringel's Earth-Moon problem)
      For every finite simple graph G = (V, E) that is biplanar, i.e. E admits a partition E = E1 + E2 with both
      (V, E1) and (V, E2) planar (equivalently with no K_5 and no K_(3,3) minor), there is a proper vertex colouring
      c : V -> {1, ..., 11}; equivalently chi_EM = max { chi(G) : G biplanar } <= 11.
    Definitions: [union_of_two_planar wagner_planar G] - two symmetric irreflexive relations e1, e2 on the vertices
      of G, each Wagner-planar when read as a graph on those vertices, with x -- y exactly when e1 x y or e2 x y
      (U13.v); [wagner_planar H] - H has no K_5 and no K_(3,3) minor (GTBase base; the record's "equivalently");
      [χ([set: G])] - the chromatic number of G, the least k such that G has a proper colouring with k colours
      (coq-graph-theory).
    Notes: encoded as stated, with U13's biplanarity.  The record splits E into two disjoint planar layers, U13
      takes the union of two planar layers: the two agree, since deleting from the second layer the edges of the
      first leaves a graph on the same vertices whose minors are minors of the second layer (grounding_X305.v,
      g305_union_partition).  A proper colouring with 11 colours exists exactly when χ([set: G]) <= 11, the reading
      of U13's earth_moon_statement.  Status: open.  The bracket 9 <= chi_EM <= 12 is unchanged since the problem
      was posted (the Open Problem Garden review at the corpus pin; U13 encodes the problem itself, the existence of
      the maximum), and Gethner's 2018 survey conjectures chi_EM = 11, of which this row is the upper half. *)
Definition earth_moon_biplanar_chi_le_11_statement : Prop :=
  forall G : sgraph, union_of_two_planar wagner_planar G -> χ([set: G]) <= 11.
