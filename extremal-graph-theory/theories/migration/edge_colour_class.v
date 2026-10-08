(** * Extremal.migration.edge_colour_class -- frozen Extremal colour-class certificates

    Library migration D12, second stage of the family "edge-colour-class"
    (meta/library_primitives/edge-colour-class.json): the public adapter.  The
    Extremal foundation's [cc_rel] and [colour_class] now unfold to
    [GTBase.edge_colourings.edge_colour_class_rel col p] and
    [GTBase.edge_colourings.edge_colour_class col p]; [cc_sym] and [cc_irrefl] keep
    their headers and are proved by the promoted lemmas.

    The whole original Section [ColourClass] of theories/foundations/edge_colourings.v
    is frozen as it stood at the D10 pin 2f37b10a (unchanged since 3011c28), in
    dependency-ordered modules, each with a verbatim copy of the Section binders
    [Variables (G : sgraph) (C : eqType)] and [Variables (col : {set G} -> C)
    (p : pred C)], so the discharged arguments are the original's; references to an
    earlier frozen name are module-qualified ([cc_rel] -> [(Legacy.cc_rel col p)],
    the same term once the Section is closed): [Legacy] holds the relation,
    [ProofsLegacy] the two opaque scripts, [GraphLegacy] the [SGraph] built from
    them with the original [Arguments], and [ApiLegacy] the two Section API lemmas.

    The frozen and live adjacencies are the same function (conversion) on the same
    host carrier; the graphs, which carry different opaque proofs, are related only
    by the identity isomorphism ([colour_class_diso], computing to the identity:
    [colour_class_disoE]), never equated.  [connected] reads only carrier and
    adjacency, so both X229 rows are kernel-checked by conversion.

    [X229Legacy] freezes the X229 row with the frozen colour classes and the live
    C6 alias [proper_ecolouring].  [X229Original] is the row as it stood before C6
    and D12: C6's frozen raw [Extremal.migration.edge_colourings.Legacy.proper_ecolouring]
    (qualified, not imported) and the frozen complementary spanning classes, with
    one positive uniform [C] before every host, palette and colouring, robust
    expansion, every [L] with [2 ^ L <= #|G|], the exact density bound, and one [P]
    whose two complementary classes are connected.  The regeneration spec is
    meta/migration_reports/edge_colour_class.spec.json. *)

From GTBase Require Import base.
Require GTBase.edge_colourings.
From Extremal.foundations Require Import edge_colourings.
From Extremal.conjectures Require Import X229.
Require Extremal.migration.edge_colourings.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Legacy.

Section ColourClass.
Variables (G : sgraph) (C : eqType).
Variables (col : {set G} -> C) (p : pred C).

Definition cc_rel : rel G := [rel x y | (x -- y) && p (col [set x; y])].

End ColourClass.

End Legacy.

Module ProofsLegacy.

Section ColourClass.
Variables (G : sgraph) (C : eqType).
Variables (col : {set G} -> C) (p : pred C).

Lemma cc_sym : symmetric (Legacy.cc_rel col p).
Proof. by move=> x y; rewrite /Legacy.cc_rel /= sg_sym setUC. Qed.

Lemma cc_irrefl : irreflexive (Legacy.cc_rel col p).
Proof. by move=> x; rewrite /Legacy.cc_rel /= sg_irrefl. Qed.

End ColourClass.

End ProofsLegacy.

Module GraphLegacy.

Section ColourClass.
Variables (G : sgraph) (C : eqType).
Variables (col : {set G} -> C) (p : pred C).

(** The spanning subgraph of [G] carrying exactly the [p]-coloured edges. *)
Definition colour_class : sgraph := SGraph (ProofsLegacy.cc_sym col p) (ProofsLegacy.cc_irrefl col p).

End ColourClass.

Arguments colour_class [G C] col p.

End GraphLegacy.

Module ApiLegacy.

Section ColourClass.
Variables (G : sgraph) (C : eqType).
Variables (col : {set G} -> C) (p : pred C).

Lemma colour_class_adj (x y : G) :
  @sedge (GraphLegacy.colour_class col p) x y = (x -- y) && p (col [set x; y]).
Proof. by []. Qed.

Lemma edges_colour_class : E(GraphLegacy.colour_class col p) = [set e in E(G) | p (col e)].
Proof.
apply/setP => e; rewrite inE; apply/idP/idP.
- case/edgesP => x [y [-> /andP[xy pc]]].
  by rewrite in_edges xy.
- case/andP => /edgesP[x [y [-> xy]]] pc.
  by apply/edgesP; exists x, y; split => //; apply/andP; split.
Qed.

End ColourClass.

End ApiLegacy.

(** ** Helper certificates *)

(** Unconditional: every host, palette, colouring and predicate. *)
Lemma cc_rel_compat (G : sgraph) (C : eqType) (col : {set G} -> C) (p : pred C) :
  Legacy.cc_rel col p =2 cc_rel col p.
Proof. by []. Qed.

Lemma colour_class_compat (G : sgraph) (C : eqType) (col : {set G} -> C) (p : pred C) :
  @edge_rel (GraphLegacy.colour_class col p) =2 @edge_rel (colour_class col p).
Proof. by []. Qed.

Lemma colour_class_diso (G : sgraph) (C : eqType) (col : {set G} -> C) (p : pred C) :
  GraphLegacy.colour_class col p ≃ colour_class col p.
Proof. exact: GTBase.edge_colourings.edge_colour_class_eq_diso. Defined.

(** The isomorphism is the identity of the common host carrier. *)
Lemma colour_class_disoE (G : sgraph) (C : eqType) (col : {set G} -> C) (p : pred C) (v : G) :
  GraphTheory.core.bij.bij_fwd (diso_v (colour_class_diso col p)) v = v.
Proof. by []. Qed.

(** Graph-construction certificate: the [SGraph] built from the frozen symmetry and
    irreflexivity proofs is isomorphic, through the identity, to the one built from
    the retained live lemmas.  It relates the constructions; it does not equate the
    opaque proof terms. *)
Lemma cc_proofs_compat (G : sgraph) (C : eqType) (col : {set G} -> C) (p : pred C) :
  SGraph (ProofsLegacy.cc_sym col p) (ProofsLegacy.cc_irrefl col p) ≃
  SGraph (cc_sym col p) (cc_irrefl col p).
Proof. exact: eq_diso. Qed.

(** ** X229 (arxiv:2309.04460#01) *)

Module X229Legacy.

Definition expander_proper_colouring_two_connected_palettes_statement : Prop :=
  exists C : nat,
    0 < C /\
    forall (G : sgraph) (Col : finType) (col : {set G} -> Col),
      x229_robust_sublinear_expander G ->
      proper_ecolouring col ->
      (forall L : nat, 2 ^ L <= #|G| -> C * (#|G| * L) <= 2 * #|E(G)|) ->
      exists P : pred Col,
        connected [set: GraphLegacy.colour_class col P] /\
        connected [set: GraphLegacy.colour_class col (predC P)].

End X229Legacy.

(** Kernel-checked conversion: [connected] reads only carrier and adjacency. *)
Lemma expander_proper_colouring_two_connected_palettes_statement_compat :
  X229Legacy.expander_proper_colouring_two_connected_palettes_statement <->
  expander_proper_colouring_two_connected_palettes_statement.
Proof. exact: iff_refl. Qed.

(** ** X229 before C6 and D12 *)

Module X229Original.

Definition expander_proper_colouring_two_connected_palettes_statement : Prop :=
  exists C : nat,
    0 < C /\
    forall (G : sgraph) (Col : finType) (col : {set G} -> Col),
      x229_robust_sublinear_expander G ->
      Extremal.migration.edge_colourings.Legacy.proper_ecolouring col ->
      (forall L : nat, 2 ^ L <= #|G| -> C * (#|G| * L) <= 2 * #|E(G)|) ->
      exists P : pred Col,
        connected [set: GraphLegacy.colour_class col P] /\
        connected [set: GraphLegacy.colour_class col (predC P)].

End X229Original.

(** Kernel-checked conversion: C6's raw properness is the canonical body
    ([Extremal.migration.edge_colourings.proper_ecolouring_compat] is [iff_refl]) and
    the frozen classes have the live carrier and adjacency. *)
Lemma expander_proper_colouring_two_connected_palettes_statement_original_compat :
  X229Original.expander_proper_colouring_two_connected_palettes_statement <->
  expander_proper_colouring_two_connected_palettes_statement.
Proof. exact: iff_refl. Qed.
