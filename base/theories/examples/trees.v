(** Public-only clients of [GTBase.trees]: no conjecture, area foundation or migration import.
    Upstream [is_tree] at the whole carrier, its Boolean form and reflection, the whole-carrier
    projections and introduction, and the recorded conventions: the empty graph, one vertex, one edge
    and the claw are trees (the claw is excluded by B9's path trees); the triangle and two isolated
    vertices are not.  No nonempty guard is assumed. *)
From mathcomp Require Import all_boot.
From GraphTheory Require Import digraph sgraph.
From GTBase Require Import base path_trees trees.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Example projections (G : sgraph) (t : is_tree [set: G]) :
  is_forest [set: G] /\ connected [set: G].
Proof. by split; [exact: is_treeT_forest t | exact: is_treeT_connected t]. Qed.

Example introduction (G : sgraph) :
  is_forest [set: G] -> connected [set: G] -> is_tree [set: G].
Proof. exact: is_treeTI. Qed.

Example boolean_form (G : sgraph) : reflect (is_tree [set: G]) (is_treeb [set: G]).
Proof. exact: is_treeP. Qed.

Example every_two_vertices_are_joined (G : sgraph) :
  is_tree [set: G] -> forall x y : G, connect (--) x y.
Proof. exact: is_treeT_connect. Qed.

Example irredundant_paths_are_unique (G : sgraph) (x y : G) (p q : Path x y) :
  is_tree [set: G] -> irred p -> irred q -> p = q.
Proof. by move=> t ip iq; exact: (is_treeT_unique t ip iq). Qed.

Example the_empty_graph_is_a_tree : is_tree [set: 'K_0] := is_tree_K0.

Example one_vertex_is_a_tree : is_tree [set: 'K_1] := is_tree_K1.

Example one_edge_is_a_tree : is_tree [set: 'K_2] := is_tree_K2.

Example the_claw_is_a_tree_but_not_a_path : is_tree [set: 'K_1,3] /\ ~ path_tree 'K_1,3.
Proof. by split; [exact: is_tree_claw | exact: not_path_tree_claw]. Qed.

Example the_triangle_is_not_a_tree : ~ is_tree [set: 'K_3] := not_is_tree_K3.

Example two_isolated_vertices_are_not_a_tree : ~ is_tree [set: compl 'K_2] := not_is_tree_two_isolated.
