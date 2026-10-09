(** * Chromatic.migration.edge_colour_class -- frozen X34 colour-class certificates

    Library migration D12, family "edge-colour-class"
    (meta/library_primitives/edge-colour-class.json).  [Legacy] freezes the X34
    colour-class helpers verbatim as they stood at the D10 pin 2f37b10a: the
    relation [(x -- y) && (col [set x; y] == i)], its symmetry and irreflexivity
    lemmas (opaque, with their original scripts) and the [SGraph] built from them.
    The live helpers now unfold to [GTBase.edge_colourings.edge_colour_class_rel
    col (pred1 i)] and [GTBase.edge_colourings.edge_colour_class col (pred1 i)].

    The frozen and live adjacencies are the same function (conversion), on the
    same host carrier; the graphs, which carry different opaque proofs, are related
    only by the identity isomorphism ([x34_colour_graph_diso], which computes to the
    identity: [x34_colour_graph_disoE]), never equated.  [is_forest] and [Delta]
    read only the carrier and the adjacency, so the linear-forest chain and the
    whole row are kernel-checked by conversion.

    [X34Legacy] freezes the chain and the row with the live matching clause.
    [X34Original] is the row as it stood before both M1 and D12: it reuses M1's
    frozen raw edge set [simple_edges.Legacy.exists_edge_set] (the X34 text at
    061154c) in the matching clause, with the same colouring for the widened
    linear-forest colours and the [ord_max] matching, the exact [let q], and the
    full planar / odd / [9 <= Delta G] guards (the documented 9-vs-7 defect is
    kept).  The regeneration spec is meta/migration_reports/edge_colour_class.spec.json. *)

From GTBase Require Import base.
Require GTBase.edge_colourings.
From Chromatic.conjectures Require Import X34.
From Chromatic.migration Require simple_edges.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Legacy.

Definition x34_edge_colour_rel
    (G : sgraph) (q : nat) (col : {set G} -> 'I_q) (i : 'I_q) : rel G :=
  fun x y => (x -- y) && (col [set x; y] == i).

Lemma x34_edge_colour_sym
    (G : sgraph) (q : nat) (col : {set G} -> 'I_q) (i : 'I_q) :
  symmetric (Legacy.x34_edge_colour_rel col i).
Proof. by move=> x y; rewrite /Legacy.x34_edge_colour_rel sg_sym setUC. Qed.

Lemma x34_edge_colour_irrefl
    (G : sgraph) (q : nat) (col : {set G} -> 'I_q) (i : 'I_q) :
  irreflexive (Legacy.x34_edge_colour_rel col i).
Proof. by move=> x; rewrite /Legacy.x34_edge_colour_rel sg_irrefl. Qed.

Definition x34_colour_graph
    (G : sgraph) (q : nat) (col : {set G} -> 'I_q) (i : 'I_q) : sgraph :=
  SGraph (Legacy.x34_edge_colour_sym col i) (Legacy.x34_edge_colour_irrefl col i).

End Legacy.

(** ** Helper certificates *)

(** Unconditional: every colouring, colour and host, edges or not. *)
Lemma x34_edge_colour_rel_compat
    (G : sgraph) (q : nat) (col : {set G} -> 'I_q) (i : 'I_q) :
  Legacy.x34_edge_colour_rel col i =2 x34_edge_colour_rel col i.
Proof. by []. Qed.

Lemma x34_colour_graph_compat
    (G : sgraph) (q : nat) (col : {set G} -> 'I_q) (i : 'I_q) :
  @edge_rel (Legacy.x34_colour_graph col i) =2 @edge_rel (x34_colour_graph col i).
Proof. by []. Qed.

Lemma x34_colour_graph_diso
    (G : sgraph) (q : nat) (col : {set G} -> 'I_q) (i : 'I_q) :
  Legacy.x34_colour_graph col i ≃ x34_colour_graph col i.
Proof. exact: GTBase.edge_colourings.edge_colour_class_eq_diso. Defined.

(** The isomorphism is the identity of the common host carrier. *)
Lemma x34_colour_graph_disoE
    (G : sgraph) (q : nat) (col : {set G} -> 'I_q) (i : 'I_q) (v : G) :
  GraphTheory.core.bij.bij_fwd (diso_v (x34_colour_graph_diso col i)) v = v.
Proof. by []. Qed.

(** Graph-construction certificate: the [SGraph] built from the frozen symmetry and
    irreflexivity proofs is isomorphic, through the identity, to the one built from
    the retained live lemmas.  It relates the constructions; it does not equate the
    opaque proof terms. *)
Lemma x34_colour_proofs_compat
    (G : sgraph) (q : nat) (col : {set G} -> 'I_q) (i : 'I_q) :
  SGraph (Legacy.x34_edge_colour_sym col i) (Legacy.x34_edge_colour_irrefl col i) ≃
  SGraph (x34_edge_colour_sym col i) (x34_edge_colour_irrefl col i).
Proof. exact: eq_diso. Qed.

(** ** X34 *)

Module X34Legacy.

Definition linear_forest_colour
    (G : sgraph) (q : nat) (col : {set G} -> 'I_q) (i : 'I_q) : Prop :=
  is_forest [set: Legacy.x34_colour_graph col i] /\
  Delta (Legacy.x34_colour_graph col i) <= 2.

Definition linear_forests_and_matching
    (G : sgraph) (q : nat) (col : {set G} -> 'I_(q.+1)) : Prop :=
  (forall i : 'I_q,
      linear_forest_colour col (widen_ord (leqnSn q) i)) /\
  x34_matching_colour col ord_max.

Definition planar_odd_degree_linear_forests_plus_matching_statement : Prop :=
  forall G : sgraph,
    wagner_planar G ->
    odd (Delta G) ->
    9 <= Delta G ->
    let q := (Delta G - 1) %/ 2 in
    exists col : {set G} -> 'I_(q.+1),
      linear_forests_and_matching col.

End X34Legacy.

(** Kernel-checked conversion: [is_forest] and [Delta] read only the carrier and
    the adjacency of the colour class, which are the same on both sides. *)
Lemma x34_linear_forest_colour_compat
    (G : sgraph) (q : nat) (col : {set G} -> 'I_q) (i : 'I_q) :
  X34Legacy.linear_forest_colour col i <-> x34_linear_forest_colour col i.
Proof. exact: iff_refl. Qed.

Lemma x34_linear_forests_and_matching_compat
    (G : sgraph) (q : nat) (col : {set G} -> 'I_(q.+1)) :
  X34Legacy.linear_forests_and_matching col <-> x34_linear_forests_and_matching col.
Proof. exact: iff_refl. Qed.

Lemma planar_odd_degree_linear_forests_plus_matching_statement_compat :
  X34Legacy.planar_odd_degree_linear_forests_plus_matching_statement <->
  planar_odd_degree_linear_forests_plus_matching_statement.
Proof. exact: iff_refl. Qed.

(** ** X34 before M1 and D12 *)

Module X34Original.

Definition matching_colour
    (G : sgraph) (q : nat) (col : {set G} -> 'I_q) (i : 'I_q) : Prop :=
  forall v : G, #|[set e in simple_edges.Legacy.exists_edge_set G | (col e == i) && (v \in e)]| <= 1.

Definition linear_forests_and_matching
    (G : sgraph) (q : nat) (col : {set G} -> 'I_(q.+1)) : Prop :=
  (forall i : 'I_q,
      X34Legacy.linear_forest_colour col (widen_ord (leqnSn q) i)) /\
  matching_colour col ord_max.

Definition planar_odd_degree_linear_forests_plus_matching_statement : Prop :=
  forall G : sgraph,
    wagner_planar G ->
    odd (Delta G) ->
    9 <= Delta G ->
    let q := (Delta G - 1) %/ 2 in
    exists col : {set G} -> 'I_(q.+1),
      linear_forests_and_matching col.

End X34Original.

(** The raw M1 edge set is the upstream edge set ([simple_edges.x34_edge_set_compat]). *)
Lemma x34_matching_colour_original_compat
    (G : sgraph) (q : nat) (col : {set G} -> 'I_q) (i : 'I_q) :
  X34Original.matching_colour col i <-> x34_matching_colour col i.
Proof.
rewrite /X34Original.matching_colour /x34_matching_colour.
by rewrite simple_edges.x34_edge_set_compat.
Qed.

Lemma x34_linear_forests_and_matching_original_compat
    (G : sgraph) (q : nat) (col : {set G} -> 'I_(q.+1)) :
  X34Original.linear_forests_and_matching col <-> x34_linear_forests_and_matching col.
Proof.
split=> -[lf mc]; split.
- exact: lf.
- exact/x34_matching_colour_original_compat.
- exact: lf.
- exact/x34_matching_colour_original_compat.
Qed.

Lemma planar_odd_degree_linear_forests_plus_matching_statement_original_compat :
  X34Original.planar_odd_degree_linear_forests_plus_matching_statement <->
  planar_odd_degree_linear_forests_plus_matching_statement.
Proof.
split=> row G pl od ge; case: (row G pl od ge) => col lfm; exists col.
- exact/x34_linear_forests_and_matching_original_compat.
- exact/x34_linear_forests_and_matching_original_compat.
Qed.
