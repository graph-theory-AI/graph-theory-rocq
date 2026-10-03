(** * Public edge-colouring API client: no conjecture imports.

    Both supplied-map interfaces of [GTBase.edge_colourings] on positive and
    negative instances: set maps on [K_2]/[K_3], pair maps on [K_0]/[K_1]/[K_2]/
    [K_3], the bridge between them, off-edge extensionality, relabelling and
    the two empty-palette behaviours. *)
From GTBase Require Import base edge_colourings.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section PublicClient.
Variables (G : sgraph) (C : eqType).

(** The endpoint form and the two edge-pair presentations agree. *)
Example meeting_edges_differ (col : {set G} -> C) :
  proper_edge_colouring col ->
  forall e f, e \in E(G) -> f \in E(G) -> e != f -> e :&: f != set0 -> col e != col f.
Proof. by move/proper_edge_colouring_edgesP. Qed.

Example non_disjoint_edges_differ (col : {set G} -> C) :
  proper_edge_colouring col ->
  forall e f, e \in E(G) -> f \in E(G) -> e != f -> ~~ [disjoint e & f] -> col e != col f.
Proof. by move/proper_edge_colouring_meetP. Qed.

(** Values off the edge set do not matter. *)
Example off_edge_values_irrelevant (col col' : {set G} -> C) :
  {in E(G), col =1 col'} -> proper_edge_colouring col -> proper_edge_colouring col'.
Proof. exact: eq_proper_edge_colouring. Qed.

(** A set map yields a globally symmetric pair map, and back. *)
Example set_map_as_pair_map (col : {set G} -> C) :
  proper_edge_colouring col <-> proper_pair_edge_colouring (fun x y => col [set x; y]).
Proof. exact: proper_edge_colouring_pairP. Qed.

Example pair_map_is_symmetric_everywhere (col : G -> G -> C) :
  proper_pair_edge_colouring col -> forall u v, col u v = col v u.
Proof. exact: proper_pair_edge_colouring_sym. Qed.

(** Injective relabelling keeps the supplied labels and properness. *)
Example injective_relabelling (D : eqType) (g : C -> D) (col : {set G} -> C) :
  injective g -> proper_edge_colouring (g \o col) <-> proper_edge_colouring col.
Proof. exact: proper_edge_colouring_relabel. Qed.

(** No set map into an empty palette exists, whatever the graph. *)
Example set_maps_need_a_colour (col0 : {set G} -> 'I_0) : False.
Proof. exact: no_set_map_into_empty_palette col0. Qed.

End PublicClient.

(** ** Concrete graphs *)

(** One edge: a constant colouring of [K_2] is proper, in both interfaces. *)
Example complete_two_constant_set : proper_edge_colouring (fun _ : {set 'K_2} => tt).
Proof. exact: proper_edge_colouring_K2. Qed.

Example complete_two_constant_pair : proper_pair_edge_colouring (fun _ _ : 'K_2 => tt).
Proof. exact: proper_pair_edge_colouring_K2. Qed.

(** Two edges at a vertex: no constant colouring of [K_3] is proper. *)
Example complete_three_constant_set_improper :
  ~ proper_edge_colouring (fun _ : {set 'K_3} => tt).
Proof. exact: not_proper_edge_colouring_K3. Qed.

Example complete_three_constant_pair_improper :
  ~ proper_pair_edge_colouring (fun _ _ : 'K_3 => tt).
Proof. exact: not_proper_pair_edge_colouring_K3. Qed.

(** The empty graph admits the unique pair map into the EMPTY palette ... *)
Example empty_graph_empty_pair_palette (col : 'K_0 -> 'K_0 -> 'I_0) :
  proper_pair_edge_colouring col.
Proof. exact: proper_pair_edge_colouring_K0. Qed.

(** ... but a single vertex, although edgeless, needs one colour for the pair
    [(ord0, ord0)] (the [K_1 = 1] convention of the star chromatic index). *)
Example single_vertex_needs_a_colour (col0 : 'K_1 -> 'K_1 -> 'I_0) : False.
Proof. exact: (@no_pair_map_into_empty_palette (complete 1) ord0 col0). Qed.

Example single_vertex_one_colour : proper_pair_edge_colouring (fun _ _ : 'K_1 => (ord0 : 'I_1)).
Proof. exact: proper_pair_edge_colouring_K1. Qed.

Print Assumptions set_map_as_pair_map.
Print Assumptions complete_three_constant_set_improper.
Print Assumptions single_vertex_needs_a_colour.
