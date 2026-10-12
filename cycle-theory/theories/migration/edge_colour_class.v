(** * Cycle.migration.edge_colour_class -- frozen X212 colour-class certificates

    Library migration D12, family "edge-colour-class"
    (meta/library_primitives/edge-colour-class.json).  [Legacy] freezes the X212
    colour-class helpers verbatim as they stood at the D10 pin 2f37b10a: the
    relation [(x -- y) && (col [set x; y] == i)], its symmetry and irreflexivity
    lemmas (opaque, with their original scripts) and the [SGraph] built from them.
    The live helpers now unfold to [GTBase.edge_colourings.edge_colour_class_rel
    col (pred1 i)] and [GTBase.edge_colourings.edge_colour_class col (pred1 i)].

    The frozen and live adjacencies are the same function (conversion), on the
    same host carrier; the graphs, which carry different opaque proofs, are related
    only by the identity isomorphism ([x212_colour_graph_diso], which computes to
    the identity: [x212_colour_graph_disoE]), never equated.  [is_forest] and
    [Delta] read only the carrier and the adjacency, so the linear-forest,
    attained-minimum and whole-row certificates are kernel-checked by conversion.

    [X212Legacy] freezes the chain and the bm-016 row: supplied total colouring,
    achievability AND the universal minimality clause, and the [0 < #|G|] and
    [regular G k] guards ([regular] is [GTBase.base.regular]).  The X212 closure is
    unchanged since before the library migrations, so no older Original exists.
    The regeneration spec is meta/migration_reports/edge_colour_class.spec.json. *)

From GTBase Require Import base.
Require GTBase.edge_colourings.
From Cycle.conjectures Require Import X212.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Legacy.

Definition x212_edge_colour_rel
    (G : sgraph) (q : nat) (col : {set G} -> 'I_q) (i : 'I_q) : rel G :=
  fun x y => (x -- y) && (col [set x; y] == i).

Lemma x212_edge_colour_sym
    (G : sgraph) (q : nat) (col : {set G} -> 'I_q) (i : 'I_q) :
  symmetric (Legacy.x212_edge_colour_rel col i).
Proof. by move=> x y; rewrite /Legacy.x212_edge_colour_rel sg_sym setUC. Qed.

Lemma x212_edge_colour_irrefl
    (G : sgraph) (q : nat) (col : {set G} -> 'I_q) (i : 'I_q) :
  irreflexive (Legacy.x212_edge_colour_rel col i).
Proof. by move=> x; rewrite /Legacy.x212_edge_colour_rel sg_irrefl. Qed.

Definition x212_colour_graph
    (G : sgraph) (q : nat) (col : {set G} -> 'I_q) (i : 'I_q) : sgraph :=
  SGraph (Legacy.x212_edge_colour_sym col i) (Legacy.x212_edge_colour_irrefl col i).

End Legacy.

(** ** Helper certificates *)

(** Unconditional: every colouring, colour and host, edges or not. *)
Lemma x212_edge_colour_rel_compat
    (G : sgraph) (q : nat) (col : {set G} -> 'I_q) (i : 'I_q) :
  Legacy.x212_edge_colour_rel col i =2 x212_edge_colour_rel col i.
Proof. by []. Qed.

Lemma x212_colour_graph_compat
    (G : sgraph) (q : nat) (col : {set G} -> 'I_q) (i : 'I_q) :
  @edge_rel (Legacy.x212_colour_graph col i) =2 @edge_rel (x212_colour_graph col i).
Proof. by []. Qed.

Lemma x212_colour_graph_diso
    (G : sgraph) (q : nat) (col : {set G} -> 'I_q) (i : 'I_q) :
  Legacy.x212_colour_graph col i ≃ x212_colour_graph col i.
Proof. exact: GTBase.edge_colourings.edge_colour_class_eq_diso. Defined.

(** The isomorphism is the identity of the common host carrier. *)
Lemma x212_colour_graph_disoE
    (G : sgraph) (q : nat) (col : {set G} -> 'I_q) (i : 'I_q) (v : G) :
  GraphTheory.core.bij.bij_fwd (diso_v (x212_colour_graph_diso col i)) v = v.
Proof. by []. Qed.

(** Graph-construction certificate: the [SGraph] built from the frozen symmetry and
    irreflexivity proofs is isomorphic, through the identity, to the one built from
    the retained live lemmas.  It relates the constructions; it does not equate the
    opaque proof terms. *)
Lemma x212_colour_proofs_compat
    (G : sgraph) (q : nat) (col : {set G} -> 'I_q) (i : 'I_q) :
  SGraph (Legacy.x212_edge_colour_sym col i) (Legacy.x212_edge_colour_irrefl col i) ≃
  SGraph (x212_edge_colour_sym col i) (x212_edge_colour_irrefl col i).
Proof. exact: eq_diso. Qed.

(** ** X212 (bm-016) *)

Module X212Legacy.

Definition linear_forest_colour
    (G : sgraph) (q : nat) (col : {set G} -> 'I_q) (i : 'I_q) : Prop :=
  is_forest [set: Legacy.x212_colour_graph col i] /\ Delta (Legacy.x212_colour_graph col i) <= 2.

Definition linear_arboricity_at_most (G : sgraph) (q : nat) : Prop :=
  exists col : {set G} -> 'I_q, forall i : 'I_q, linear_forest_colour col i.

Definition linear_arboricity (G : sgraph) (q : nat) : Prop :=
  linear_arboricity_at_most G q /\
  forall q' : nat, linear_arboricity_at_most G q' -> q <= q'.

Definition linear_arboricity_regular_statement : Prop :=
  forall (k : nat) (G : sgraph),
    0 < #|G| -> regular G k -> linear_arboricity G (ceil_div (k + 1) 2).

End X212Legacy.

(** Kernel-checked conversion: [is_forest] and [Delta] read only the carrier and
    the adjacency of the colour class, which are the same on both sides. *)
Lemma x212_linear_forest_colour_compat
    (G : sgraph) (q : nat) (col : {set G} -> 'I_q) (i : 'I_q) :
  X212Legacy.linear_forest_colour col i <-> x212_linear_forest_colour col i.
Proof. exact: iff_refl. Qed.

Lemma x212_linear_arboricity_at_most_compat (G : sgraph) (q : nat) :
  X212Legacy.linear_arboricity_at_most G q <-> x212_linear_arboricity_at_most G q.
Proof. exact: iff_refl. Qed.

Lemma x212_linear_arboricity_compat (G : sgraph) (q : nat) :
  X212Legacy.linear_arboricity G q <-> x212_linear_arboricity G q.
Proof. exact: iff_refl. Qed.

Lemma linear_arboricity_regular_statement_compat :
  X212Legacy.linear_arboricity_regular_statement <-> linear_arboricity_regular_statement.
Proof. exact: iff_refl. Qed.
