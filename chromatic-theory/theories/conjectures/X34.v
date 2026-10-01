(** * Chromatic.conjectures.X34 -- v2 odd-degree planar linear arboricity row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X34 vocabulary ************************************************)

Definition x34_edge_set (G : sgraph) : {set {set G}} :=
  simple_edge_set G.

Definition x34_edge_colour_rel
    (G : sgraph) (q : nat) (col : {set G} -> 'I_q) (i : 'I_q) : rel G :=
  fun x y => (x -- y) && (col [set x; y] == i).

Lemma x34_edge_colour_sym
    (G : sgraph) (q : nat) (col : {set G} -> 'I_q) (i : 'I_q) :
  symmetric (x34_edge_colour_rel col i).
Proof. by move=> x y; rewrite /x34_edge_colour_rel sg_sym setUC. Qed.

Lemma x34_edge_colour_irrefl
    (G : sgraph) (q : nat) (col : {set G} -> 'I_q) (i : 'I_q) :
  irreflexive (x34_edge_colour_rel col i).
Proof. by move=> x; rewrite /x34_edge_colour_rel sg_irrefl. Qed.

Definition x34_colour_graph
    (G : sgraph) (q : nat) (col : {set G} -> 'I_q) (i : 'I_q) : sgraph :=
  SGraph (x34_edge_colour_sym col i) (x34_edge_colour_irrefl col i).

Definition x34_linear_forest_colour
    (G : sgraph) (q : nat) (col : {set G} -> 'I_q) (i : 'I_q) : Prop :=
  is_forest [set: x34_colour_graph col i] /\
  Delta (x34_colour_graph col i) <= 2.

Definition x34_matching_colour
    (G : sgraph) (q : nat) (col : {set G} -> 'I_q) (i : 'I_q) : Prop :=
  forall v : G, #|[set e in x34_edge_set G | (col e == i) && (v \in e)]| <= 1.

Definition x34_linear_forests_and_matching
    (G : sgraph) (q : nat) (col : {set G} -> 'I_(q.+1)) : Prop :=
  (forall i : 'I_q,
      x34_linear_forest_colour col (widen_ord (leqnSn q) i)) /\
  x34_matching_colour col ord_max.

(** ** X34 statements ******************************************************)

(** arXiv:2302.13312, planar odd-degree linear arboricity refinement. *)
Definition planar_odd_degree_linear_forests_plus_matching_statement : Prop :=
  forall G : sgraph,
    wagner_planar G ->
    odd (Delta G) ->
    9 <= Delta G ->
    let q := (Delta G - 1) %/ 2 in
    exists col : {set G} -> 'I_(q.+1),
      x34_linear_forests_and_matching col.
