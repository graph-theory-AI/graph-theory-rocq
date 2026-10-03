(** Downstream use of the public multigraph spanning-tree API of [Cycle.foundations], without
    conjecture imports: the projections, introduction and Boolean walk form of
    [spanning_tree_edge_set], host connectivity, the rejection of loops and parallel pairs, and
    the recorded conventions (empty host, one vertex beside an unselected loop, one edge in either
    orientation, a third isolated vertex, a parallel pair, a digon).  No loopless, simplicity or
    nonempty premise is assumed. *)
From GraphTheory Require Import mgraph.
From GTBase Require Import base.
From Cycle.foundations Require Import connectivity path_subgraphs spanning_trees.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Example projections (G : mgraph) (T : {set edge G}) (sT : spanning_tree_edge_set T) :
  spanning_connected_edge_set T /\ acyclic_edge_set T.
Proof. by split; [exact: spanning_tree_edge_set_connected sT | exact: spanning_tree_edge_set_acyclic sT]. Qed.

Example introduction (G : mgraph) (T : {set edge G}) :
  spanning_connected_edge_set T -> acyclic_edge_set T -> spanning_tree_edge_set T.
Proof. exact: spanning_tree_edge_setI. Qed.

Example boolean_walk_form (G : mgraph) (T : {set edge G}) :
  spanning_connected_edge_set T <-> forall x y : G, exists w, walk_in T x y w.
Proof. exact: spanning_connected_edge_setP. Qed.

Example the_host_is_connected (G : mgraph) (T : {set edge G}) :
  spanning_tree_edge_set T -> mconnected G.
Proof. exact: spanning_tree_edge_set_mconnected. Qed.

Example a_selected_loop_is_rejected (G : mgraph) (T : {set edge G}) (e : edge G) :
  source e = target e -> e \in T -> ~ spanning_tree_edge_set T.
Proof. exact: spanning_tree_edge_set_noloop. Qed.

Example the_empty_host_is_spanned_by_nothing : spanning_tree_edge_set (@set0 (edge empty_host)) :=
  spanning_tree_edge_set_empty.

Example one_vertex_beside_an_unselected_loop : spanning_tree_edge_set (@set0 (edge one_loop)) :=
  spanning_tree_edge_set_one_vertex.

Example selecting_the_loop_fails : ~ spanning_tree_edge_set [set (None : edge one_loop)] :=
  not_spanning_tree_edge_set_loop.

Example one_edge_spans_two_vertices : spanning_tree_edge_set [set (None : edge one_edge)] :=
  spanning_tree_edge_set_one_edge.

Example orientation_does_not_matter : spanning_tree_edge_set [set (None : edge one_edge_rev)] :=
  spanning_tree_edge_set_one_edge_rev.

Example incident_support_connectivity_is_not_spanning :
  subgraph_connected [set (inl None : edge one_edge_and_vertex)]
  /\ ~ spanning_tree_edge_set [set (inl None : edge one_edge_and_vertex)].
Proof.
by split; [exact: subgraph_connected_one_edge_and_vertex | exact: not_spanning_tree_edge_set_one_edge_and_vertex].
Qed.

Example a_parallel_pair_is_rejected : ~ spanning_tree_edge_set [set: edge parallel_pair] :=
  not_spanning_tree_edge_set_parallel_pair.

Example a_digon_is_rejected : ~ spanning_tree_edge_set [set: edge digon] :=
  not_spanning_tree_edge_set_digon.
