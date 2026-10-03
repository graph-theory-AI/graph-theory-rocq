(** Downstream use of the ordered pair counts between two vertex sets ([edges_between],
    [nonedges_between]), without corpus imports. *)
From GTBase Require Import base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section PublicClient.
Variable G : sgraph.
Implicit Types (A B : {set G}) (x : G).

(** Every ordered pair of [A x B] is an edge or a non-edge. *)
Example pairs_split A B : edges_between A B + nonedges_between A B = #|A| * #|B|.
Proof. exact: edges_nonedges_between. Qed.

Example swapping_the_sets A B :
  edges_between A B = edges_between B A /\ nonedges_between A B = nonedges_between B A.
Proof. by split; [exact: edges_between_sym | exact: nonedges_between_sym]. Qed.

Example empty_set_counts_nothing B : edges_between set0 B = 0 /\ nonedges_between set0 B = 0.
Proof. by rewrite edges_between_set0 nonedges_between_set0. Qed.

(** Overlap is allowed: a shared vertex gives one diagonal non-edge pair and no edge. *)
Example shared_vertex x :
  edges_between [set x] [set x] = 0 /\ nonedges_between [set x] [set x] = 1.
Proof. by rewrite edges_between_set1 nonedges_between_set1. Qed.

(** On disjoint sets: the cross edges of [E(G)], and the edges of the complement. *)
Example disjoint_sets_cross_edges A B : [disjoint A & B] ->
  edges_between A B = #|[set e in E(G) | (e :&: A != set0) && (e :&: B != set0)]|.
Proof. exact: edges_between_cross. Qed.

Example disjoint_sets_complement_edges A B : [disjoint A & B] ->
  nonedges_between A B = @edges_between (compl G) A B.
Proof. exact: nonedges_between_compl. Qed.

(** Negative: without disjointness the complement reading can fail. *)
Example overlap_breaks_the_complement_reading x :
  nonedges_between [set x] [set x] <> @edges_between (compl G) [set x] [set x].
Proof. by case: (nonedges_between_compl_overlap x) => -> ->. Qed.

End PublicClient.

(** Complete graphs: exactly the diagonal pairs are non-edges. *)
Example complete_graph_pairs n (A B : {set 'K_n}) :
  nonedges_between A B = #|A :&: B| /\ edges_between A B = #|A| * #|B| - #|A :&: B|.
Proof. by rewrite nonedges_between_Kn edges_between_Kn. Qed.

(** [K_2] taken whole has its edge in both orientations; its two singletons have it once. *)
Example K2_whole : edges_between [set: 'K_2] [set: 'K_2] = 2.
Proof. exact: edges_between_K2. Qed.

Example K2_disjoint_singletons : edges_between [set ord0 : 'K_2] [set ord_max : 'K_2] = 1.
Proof.
rewrite edges_between_Kn !cards1.
suff -> : [set ord0 : 'K_2] :&: [set ord_max] = set0 by rewrite cards0.
by apply/setP => z; rewrite !inE; case: (z =P ord0) => [->|].
Qed.

Print Assumptions pairs_split.
Print Assumptions disjoint_sets_cross_edges.
Print Assumptions overlap_breaks_the_complement_reading.
Print Assumptions K2_disjoint_singletons.
