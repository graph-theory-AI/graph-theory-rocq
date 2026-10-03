(** Public-only clients of [GTBase.spanning_trees]: no conjecture, area foundation or migration
    import.  The projections, introduction and Boolean form of [fg_spanning_tree], its edge
    validity, whole-carrier covering and host connectivity, and the recorded conventions on
    ['K_0], ['K_1], ['K_2], the triangle, a missing vertex, two isolated vertices and an invalid
    member.  No nonempty guard is assumed. *)
From mathcomp Require Import all_boot.
From GraphTheory Require Import digraph sgraph.
From GTBase Require Import finite_graph spanning_trees.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Example projections (G : sgraph) (T : {set {set G}}) (sT : fg_spanning_tree T) :
  [/\ T \subset fg_edges G, is_forest [set: fg_labelled_sgraph T]
    & connected [set: fg_labelled_sgraph T]].
Proof.
by split; [exact: fg_spanning_tree_sub sT | exact: fg_spanning_tree_forest sT
          | exact: fg_spanning_tree_connected sT].
Qed.

Example introduction (G : sgraph) (T : {set {set G}}) :
  T \subset fg_edges G -> is_tree [set: fg_labelled_sgraph T] -> fg_spanning_tree T.
Proof. exact: fg_spanning_treeI. Qed.

Example boolean_form (G : sgraph) (T : {set {set G}}) :
  reflect (fg_spanning_tree T) (fg_spanning_treeb T).
Proof. exact: fg_spanning_treeP. Qed.

Example upstream_edge_set_form (G : sgraph) (T : {set {set G}}) :
  fg_spanning_tree T -> T \subset E(G).
Proof. by move/fg_spanning_treeE => []. Qed.

Example members_are_edges (G : sgraph) (T : {set {set G}}) (x y : G) :
  fg_spanning_tree T -> [set x; y] \in T -> x -- y.
Proof. exact: fg_spanning_tree_edge. Qed.

Example every_vertex_is_covered (G : sgraph) (T : {set {set G}}) (x : G) :
  fg_spanning_tree T -> 1 < #|G| -> exists y, [set x; y] \in T.
Proof. exact: fg_spanning_tree_cover. Qed.

Example the_host_is_connected (G : sgraph) (T : {set {set G}}) :
  fg_spanning_tree T -> connected [set: G].
Proof. exact: fg_spanning_tree_connectedG. Qed.

Example the_empty_graph_has_the_empty_spanning_tree : fg_spanning_tree (@set0 {set 'K_0}) :=
  fg_spanning_tree_K0.

Example a_single_vertex_has_the_empty_spanning_tree : fg_spanning_tree (@set0 {set 'K_1}) :=
  fg_spanning_tree_K1.

Example the_single_edge_spans_K2 : fg_spanning_tree (fg_edges 'K_2) := fg_spanning_tree_K2.

Example the_triangle_is_not_a_tree : ~ fg_spanning_tree (fg_edges 'K_3) := not_fg_spanning_tree_K3.

Example one_edge_misses_a_vertex_of_K3 : ~ fg_spanning_tree [set [set (ord0 : 'K_3); k3_o1]] :=
  not_fg_spanning_tree_K3_edge.

Example two_isolated_vertices_have_none (T : {set {set two_isolated}}) : ~ fg_spanning_tree T :=
  @not_fg_spanning_tree_two_isolated T.

Example a_singleton_member_is_invalid (G : sgraph) (x : G) :
  ~ fg_spanning_tree [set [set x]].
Proof. exact: not_fg_spanning_tree_singleton (set11 _). Qed.
