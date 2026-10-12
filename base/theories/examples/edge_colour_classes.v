(** * Public colour-class API client: no conjecture imports.

    [GTBase.edge_colourings.edge_colour_class] on general hosts and on small
    concrete graphs: the adjacency, the spanning carrier, the edge set and its
    split, off-edge irrelevance, the identity transport, the [predT] / [pred0] /
    single-colour corners, an edgeless and an empty host, and the empty palette. *)
From GTBase Require Import base edge_colourings.
From GraphTheory Require Import bij.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section PublicClient.
Variables (G : sgraph) (C : eqType).

(** Adjacency: a host edge whose colour satisfies the predicate. *)
Example class_adjacency (col : {set G} -> C) (p : pred C) (x y : G) :
  @edge_rel (edge_colour_class col p) x y = (x -- y) && p (col [set x; y]).
Proof. exact: edge_colour_classE. Qed.

(** Spanning: the class keeps every vertex of the host, isolated ones included. *)
Example class_is_spanning (col : {set G} -> C) (p : pred C) :
  #|edge_colour_class col p| = #|G|.
Proof. by []. Qed.

(** The edge set, and the split of [E(G)] by a predicate and its complement. *)
Example class_edges (col : {set G} -> C) (p : pred C) :
  E(edge_colour_class col p) = [set e in E(G) | p (col e)].
Proof. exact: edges_edge_colour_class. Qed.

Example class_split (col : {set G} -> C) (p : pred C) :
  #|E(edge_colour_class col p)| + #|E(edge_colour_class col (predC p))| = #|E(G)|.
Proof. exact: card_edges_edge_colour_class_split. Qed.

(** Values off the edge set do not matter. *)
Example off_edge_values_irrelevant (col col' : {set G} -> C) (p : pred C) :
  {in E(G), col =1 col'} -> edge_colour_class col p ≃ edge_colour_class col' p.
Proof. by move=> eqE; apply: eq_edge_colour_class => e eG; rewrite (eqE e eG). Qed.

(** The identity transport from a hand-made copy of the relation. *)
Definition single_colour_rel (col : {set G} -> C) (c : C) : rel G :=
  fun x y => (x -- y) && (col [set x; y] == c).

Lemma single_colour_sym (col : {set G} -> C) (c : C) : symmetric (single_colour_rel col c).
Proof. by move=> x y; rewrite /single_colour_rel sg_sym setUC. Qed.

Lemma single_colour_irrefl (col : {set G} -> C) (c : C) : irreflexive (single_colour_rel col c).
Proof. by move=> x; rewrite /single_colour_rel sg_irrefl. Qed.

Example single_colour_copy_is_the_class (col : {set G} -> C) (c : C) :
  SGraph (single_colour_sym col c) (single_colour_irrefl col c) ≃ edge_colour_class col (pred1 c).
Proof. exact: edge_colour_class_eq_diso. Qed.

Example single_colour_copy_is_the_identity (col : {set G} -> C) (c : C) (v : G) :
  @edge_colour_class_eq_diso G C col (pred1 c) _ (single_colour_sym col c)
    (single_colour_irrefl col c) (fun x y => erefl) v = v.
Proof. exact: edge_colour_class_eq_disoE. Qed.

(** Corners: every colour kept, no colour kept, one colour. *)
Example all_colours_give_the_host (col : {set G} -> C) : edge_colour_class col predT ≃ G.
Proof. exact: edge_colour_class_predT. Qed.

Example no_colour_gives_no_edge (col : {set G} -> C) : E(edge_colour_class col pred0) = set0.
Proof. exact: edges_edge_colour_class_pred0. Qed.

Example edge_in_its_own_class (col : {set G} -> C) (e : {set G}) :
  e \in E(G) -> e \in E(edge_colour_class col (pred1 (col e))).
Proof. by move=> eG; rewrite edges_edge_colour_class1. Qed.

Example edge_in_no_other_class (col : {set G} -> C) (c : C) (e : {set G}) :
  e \in E(G) -> col e != c -> e \notin E(edge_colour_class col (pred1 c)).
Proof. by move=> eG; rewrite edges_edge_colour_class1. Qed.

(** No total colouring into an empty palette exists, whatever the host. *)
Example classes_need_a_colour (col0 : {set G} -> 'I_0) : False.
Proof. exact: no_set_map_into_empty_palette col0. Qed.

End PublicClient.

(** ** Concrete hosts *)

(** One edge, one colour: the class is the whole edge set; an unused colour is empty. *)
Example complete_two_one_class : E(edge_colour_class (fun _ : {set 'K_2} => tt) (pred1 tt)) = E('K_2).
Proof. by rewrite edges_edge_colour_class_const eqxx. Qed.

Example complete_three_unused_colour :
  E(edge_colour_class (fun _ : {set 'K_3} => true) (pred1 false)) = set0.
Proof. by rewrite edges_edge_colour_class_const. Qed.

(** An edgeless host: every class is edgeless, its single vertex stays. *)
Example single_vertex_class_edgeless (C : eqType) (col : {set 'K_1} -> C) (p : pred C) :
  E(edge_colour_class col p) = set0 /\ #|edge_colour_class col p| = 1.
Proof.
split; last by rewrite card_ord.
apply/setP => e; rewrite edges_edge_colour_class !inE.
apply/negbTE/negP => /andP[/edgesP[x [y [_ xy]]] _].
by move: xy; rewrite (ord1 x) (ord1 y) sg_irrefl.
Qed.

(** The empty host has an empty class, yet still no colouring into an empty
    palette: its powerset is inhabited. *)
Example empty_host_class (C : eqType) (col : {set 'K_0} -> C) (p : pred C) :
  #|edge_colour_class col p| = 0.
Proof. by rewrite card_ord. Qed.

Example empty_host_needs_a_colour (col0 : {set 'K_0} -> 'I_0) : False.
Proof. exact: no_set_map_into_empty_palette col0. Qed.

Print Assumptions class_edges.
Print Assumptions off_edge_values_irrelevant.
Print Assumptions single_colour_copy_is_the_identity.
Print Assumptions all_colours_give_the_host.
Print Assumptions complete_two_one_class.
Print Assumptions single_vertex_class_edgeless.
Print Assumptions empty_host_needs_a_colour.
