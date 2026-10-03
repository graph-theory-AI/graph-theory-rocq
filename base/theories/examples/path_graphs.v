(** * GTBase.examples.path_graphs — public-only client of [GTBase.path_graphs] (B21)

    Exercises the ordinal path graph through the public API alone: no conjecture module is imported.
    The small cases n = 0, 1, 2, 3, the absence of loops and of a modular wrap, the P_4
    specialisation, the order, the isomorphism of a guarded constructor with the canonical graph,
    and the bridges to [is_tree] and to B9's [path_tree]. *)

From mathcomp Require Import all_boot.
From GraphTheory Require Import preliminaries digraph sgraph.
From GTBase Require Import base path_trees path_graphs.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** The small cases *)

(** P_0 has no vertex at all. *)
Lemma no_vertex : #|ordinal_path 0| = 0.
Proof. exact: ordinal_path0_empty. Qed.

(** P_1 has a vertex but no edge. *)
Lemma one_vertex_no_edge (i j : ordinal_path 1) : ~~ (i -- j).
Proof. exact: ordinal_path1_edgeless. Qed.

(** P_2 is one edge, between its two vertices. *)
Lemma two_vertices_one_edge : (ord0 : ordinal_path 2) -- ord_max.
Proof. exact: ordinal_path2_edge. Qed.

(** P_3 is a path, not a triangle: its ends are not adjacent. *)
Lemma three_vertices_no_wrap : ~~ ((ord0 : ordinal_path 3) -- ord_max).
Proof. exact: ordinal_path3_no_wrap. Qed.

(** The middle vertex of P_3 is adjacent to both ends. *)
Lemma three_vertices_middle :
  ((ord0 : ordinal_path 3) -- inord 1) /\ ((inord 1 : ordinal_path 3) -- ord_max).
Proof. by split; rewrite ordinal_path_edgeE /= ?inordK. Qed.

(** ** The contract for every n *)

Lemma order n : #|ordinal_path n| = n.
Proof. exact: card_ordinal_path. Qed.

Lemma no_loops n (i : ordinal_path n) : ~~ (i -- i).
Proof. exact: ordinal_path_no_loop. Qed.

Lemma adjacent_iff_consecutive n (i j : ordinal_path n) :
  reflect (val j = (val i).+1 \/ val i = (val j).+1) (i -- j).
Proof. exact: ordinal_path_relP. Qed.

Lemma ends_never_adjacent n (i j : ordinal_path n) :
  2 < n -> val i = 0 -> val j = n.-1 -> ~~ (i -- j).
Proof. exact: ordinal_path_ends. Qed.

(** The P_4 specialisation: the X170 relation. *)
Lemma p4_edges (i j : ordinal_path 4) :
  (i -- j) = ((val i).+1 == val j) || ((val j).+1 == val i).
Proof. exact: ordinal_path4_edgeE. Qed.

(** ** A guarded constructor is the same graph up to isomorphism *)

Definition guarded_rel n : rel 'I_n :=
  fun i j => (i != j) && (((val i).+1 == val j) || ((val j).+1 == val i)).

Lemma guarded_rel_sym n : symmetric (@guarded_rel n).
Proof. by move=> i j; rewrite /guarded_rel eq_sym orbC. Qed.

Lemma guarded_rel_irrefl n : irreflexive (@guarded_rel n).
Proof. by move=> i; rewrite /guarded_rel eqxx. Qed.

Lemma guarded_constructor_isomorphic n :
  SGraph (@guarded_rel_sym n) (@guarded_rel_irrefl n) ≃ ordinal_path n.
Proof. by apply: guarded_ordinal_path_diso => i j. Qed.

(** The guard changes no edge. *)
Lemma guard_is_redundant n (i j : 'I_n) :
  guarded_rel i j = ordinal_path_rel i j.
Proof. exact: ordinal_path_rel_guardedE. Qed.

(** ** Bridges *)

Lemma max_degree_at_most_two n : Delta (ordinal_path n) <= 2.
Proof. exact: ordinal_path_Delta. Qed.

Lemma connected_for_every_n n : connected [set: ordinal_path n].
Proof. exact: ordinal_path_connected. Qed.

Lemma a_forest_for_every_n n : is_forest [set: ordinal_path n].
Proof. exact: ordinal_path_is_forest. Qed.

Lemma a_tree_for_every_n n : is_tree [set: ordinal_path n].
Proof. exact: ordinal_path_is_tree. Qed.

(** B9's path-tree predicate holds, P_0 included (the empty graph is a path tree there too). *)
Lemma a_path_tree_for_every_n n : path_tree (ordinal_path n).
Proof. exact: ordinal_path_path_tree. Qed.
