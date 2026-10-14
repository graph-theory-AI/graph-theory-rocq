(** Downstream use of path trees ([GTBase.path_trees.path_tree]: a tree of maximum
    degree at most two) and linear forests ([GTBase.path_trees.linear_forest]: a
    forest of maximum degree at most two), without corpus imports.  Each example
    uses public API lemmas only. *)
From GTBase Require Import base path_trees edge_colourings.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Client.
Variable T : sgraph.

(** A path tree is a connected forest whose vertices have at most two neighbours. *)
Example path_tree_parts :
  path_tree T -> [/\ is_forest [set: T], connected [set: T] & forall v : T, #|N(v)| <= 2].
Proof.
move=> pT; split; [exact: path_tree_forest | exact: path_tree_connected | ].
by move=> v; exact: path_tree_degree.
Qed.

(** Conversely, a tree with degrees at most two is a path tree. *)
Example path_tree_from_degrees :
  is_tree [set: T] -> (forall v : T, #|N(v)| <= 2) -> path_tree T.
Proof. exact: path_treeI. Qed.

End Client.

(** The empty graph, a single vertex and a single edge are path trees. *)
Example small_path_trees : [/\ path_tree ('K_0), path_tree ('K_1) & path_tree ('K_2)].
Proof. by split; [exact: path_tree_K0 | exact: path_tree_K1 | exact: path_tree_K2]. Qed.

(** A cycle and a branching vertex are excluded. *)
Example cycle_and_branch_excluded : ~ path_tree 'K_3 /\ ~ path_tree 'K_1,3.
Proof. by split; [exact: not_path_tree_K3 | exact: not_path_tree_claw]. Qed.

Print Assumptions small_path_trees.
Print Assumptions cycle_and_branch_excluded.

(** ** Linear forests *)

Section LinearForestClient.
Variable G : sgraph.

(** A linear forest is a forest whose vertices have at most two neighbours, and back. *)
Example linear_forest_parts :
  linear_forest G <-> is_forest [set: G] /\ (forall v : G, #|N(v)| <= 2).
Proof. exact: linear_forestP. Qed.

(** A path tree is exactly a connected linear forest; connectedness is not part of
    [linear_forest]. *)
Example path_tree_connected_linear_forest :
  path_tree G <-> linear_forest G /\ connected [set: G].
Proof. exact: path_treeP. Qed.

(** A graph without edges is a linear forest. *)
Example edgeless_linear_forest : (forall x y : G, ~~ (x -- y)) -> linear_forest G.
Proof. exact: linear_forest_edgeless. Qed.

End LinearForestClient.

(** A colour class of an unused colour keeps every vertex of the host (the carrier
    is the host's, not the incident vertices) and has no edge, so it is a linear
    forest; this holds on every host, the empty one included. *)
Example unused_colour_class_linear_forest
    (G : sgraph) (q : nat) (col : {set G} -> 'I_q) (i : 'I_q) :
  (forall x y : G, x -- y -> col [set x; y] != i) ->
  linear_forest (edge_colour_class col (pred1 i)) /\
  #|edge_colour_class col (pred1 i)| = #|G|.
Proof.
move=> unused; split=> //; apply: linear_forest_edgeless => x y.
rewrite edge_colour_classE /=; apply/andP=> -[xy /eqP ci].
by move: (unused x y xy); rewrite ci eqxx.
Qed.

(** The empty graph, a single vertex and a single edge are linear forests. *)
Example small_linear_forests :
  [/\ linear_forest ('K_0), linear_forest ('K_1) & linear_forest ('K_2)].
Proof. by split; [exact: linear_forest_K0 | exact: linear_forest_K1 | exact: linear_forest_K2]. Qed.

(** A cycle and a branching vertex are excluded. *)
Example cycle_and_branch_not_linear_forests : ~ linear_forest 'K_3 /\ ~ linear_forest 'K_1,3.
Proof. by split; [exact: not_linear_forest_K3 | exact: not_linear_forest_claw]. Qed.

Print Assumptions unused_colour_class_linear_forest.
Print Assumptions small_linear_forests.
Print Assumptions cycle_and_branch_not_linear_forests.
