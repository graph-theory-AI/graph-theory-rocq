(** Downstream use of path trees ([GTBase.path_trees.path_tree]: a tree of maximum
    degree at most two), without corpus imports.  Each example uses public API
    lemmas only. *)
From GTBase Require Import base path_trees.

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
