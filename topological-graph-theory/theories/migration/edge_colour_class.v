(** * Topological.migration.edge_colour_class -- frozen X23 colour-class certificates

    Library migration D12, family "edge-colour-class"
    (meta/library_primitives/edge-colour-class.json).  [Legacy] freezes the X23
    colour-class helpers verbatim as they stood at the D10 pin 2f37b10a: the
    relation [(x -- y) && (col [set x; y] == i)], its symmetry and irreflexivity
    lemmas (opaque, with their original scripts) and the [SGraph] built from them.
    The live helpers now unfold to [GTBase.edge_colourings.edge_colour_class_rel
    col (pred1 i)] and [GTBase.edge_colourings.edge_colour_class col (pred1 i)].

    The frozen and live adjacencies are the same function (conversion), on the
    same host carrier; the graphs, which carry different opaque proofs, are related
    only by the identity isomorphism ([x23_colour_graph_diso], which computes to
    the identity: [x23_colour_graph_disoE]), never equated.  [is_forest] and
    [Delta] read only the carrier and the adjacency, so the linear-forest,
    attained-minimum and whole-row certificates are kernel-checked by conversion.

    [X23Legacy] freezes the chain and the planar linear arboricity row: supplied
    total colouring, achievability AND the universal minimality clause, and the
    [wagner_planar G] and [5 <= Delta G] guards with [ceil_div (Delta G) 2].  The
    X23 closure is unchanged since before the library migrations (B6 changed only
    [x23_genuine_path]), so no older Original exists.  The regeneration spec is
    meta/migration_reports/edge_colour_class.spec.json. *)

From GTBase Require Import base.
Require GTBase.edge_colourings.
From Topological.conjectures Require Import X23.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Legacy.

Definition x23_edge_colour_rel
    (G : sgraph) (q : nat) (col : {set G} -> 'I_q) (i : 'I_q) : rel G :=
  fun x y => (x -- y) && (col [set x; y] == i).

Lemma x23_edge_colour_sym
    (G : sgraph) (q : nat) (col : {set G} -> 'I_q) (i : 'I_q) :
  symmetric (Legacy.x23_edge_colour_rel col i).
Proof.
by move=> x y; rewrite /Legacy.x23_edge_colour_rel sg_sym setUC.
Qed.

Lemma x23_edge_colour_irrefl
    (G : sgraph) (q : nat) (col : {set G} -> 'I_q) (i : 'I_q) :
  irreflexive (Legacy.x23_edge_colour_rel col i).
Proof. by move=> x; rewrite /Legacy.x23_edge_colour_rel sg_irrefl. Qed.

Definition x23_colour_graph
    (G : sgraph) (q : nat) (col : {set G} -> 'I_q) (i : 'I_q) : sgraph :=
  SGraph (Legacy.x23_edge_colour_sym col i) (Legacy.x23_edge_colour_irrefl col i).

End Legacy.

(** ** Helper certificates *)

(** Unconditional: every colouring, colour and host, edges or not. *)
Lemma x23_edge_colour_rel_compat
    (G : sgraph) (q : nat) (col : {set G} -> 'I_q) (i : 'I_q) :
  Legacy.x23_edge_colour_rel col i =2 x23_edge_colour_rel col i.
Proof. by []. Qed.

Lemma x23_colour_graph_compat
    (G : sgraph) (q : nat) (col : {set G} -> 'I_q) (i : 'I_q) :
  @edge_rel (Legacy.x23_colour_graph col i) =2 @edge_rel (x23_colour_graph col i).
Proof. by []. Qed.

Lemma x23_colour_graph_diso
    (G : sgraph) (q : nat) (col : {set G} -> 'I_q) (i : 'I_q) :
  Legacy.x23_colour_graph col i ≃ x23_colour_graph col i.
Proof. exact: GTBase.edge_colourings.edge_colour_class_eq_diso. Defined.

(** The isomorphism is the identity of the common host carrier. *)
Lemma x23_colour_graph_disoE
    (G : sgraph) (q : nat) (col : {set G} -> 'I_q) (i : 'I_q) (v : G) :
  GraphTheory.core.bij.bij_fwd (diso_v (x23_colour_graph_diso col i)) v = v.
Proof. by []. Qed.

(** Graph-construction certificate: the [SGraph] built from the frozen symmetry and
    irreflexivity proofs is isomorphic, through the identity, to the one built from
    the retained live lemmas.  It relates the constructions; it does not equate the
    opaque proof terms. *)
Lemma x23_colour_proofs_compat
    (G : sgraph) (q : nat) (col : {set G} -> 'I_q) (i : 'I_q) :
  SGraph (Legacy.x23_edge_colour_sym col i) (Legacy.x23_edge_colour_irrefl col i) ≃
  SGraph (x23_edge_colour_sym col i) (x23_edge_colour_irrefl col i).
Proof. exact: eq_diso. Qed.

(** ** X23 (planar linear arboricity) *)

Module X23Legacy.

Definition linear_forest_colour
    (G : sgraph) (q : nat) (col : {set G} -> 'I_q) (i : 'I_q) : Prop :=
  is_forest [set: Legacy.x23_colour_graph col i] /\
  Delta (Legacy.x23_colour_graph col i) <= 2.

Definition linear_arboricity_at_most (G : sgraph) (q : nat) : Prop :=
  exists col : {set G} -> 'I_q,
    forall i : 'I_q, linear_forest_colour col i.

Definition linear_arboricity (G : sgraph) (q : nat) : Prop :=
  linear_arboricity_at_most G q /\
  forall q' : nat, linear_arboricity_at_most G q' -> q <= q'.

Definition planar_linear_arboricity_statement : Prop :=
  forall G : sgraph,
    wagner_planar G ->
    5 <= Delta G ->
    linear_arboricity G (ceil_div (Delta G) 2).

End X23Legacy.

(** Kernel-checked conversion: [is_forest] and [Delta] read only the carrier and
    the adjacency of the colour class, which are the same on both sides. *)
Lemma x23_linear_forest_colour_compat
    (G : sgraph) (q : nat) (col : {set G} -> 'I_q) (i : 'I_q) :
  X23Legacy.linear_forest_colour col i <-> x23_linear_forest_colour col i.
Proof. exact: iff_refl. Qed.

Lemma x23_linear_arboricity_at_most_compat (G : sgraph) (q : nat) :
  X23Legacy.linear_arboricity_at_most G q <-> x23_linear_arboricity_at_most G q.
Proof. exact: iff_refl. Qed.

Lemma x23_linear_arboricity_compat (G : sgraph) (q : nat) :
  X23Legacy.linear_arboricity G q <-> x23_linear_arboricity G q.
Proof. exact: iff_refl. Qed.

Lemma planar_linear_arboricity_statement_compat :
  X23Legacy.planar_linear_arboricity_statement <-> planar_linear_arboricity_statement.
Proof. exact: iff_refl. Qed.
