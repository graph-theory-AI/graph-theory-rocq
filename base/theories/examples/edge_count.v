(** Downstream use of the canonical edge count [edge_count G = #|E(G)|], without corpus
    imports. *)
From GTBase Require Import base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section PublicClient.
Variable G : sgraph.

(** The cardinality of the upstream edge set: unordered pairs of adjacent vertices. *)
Example edge_count_is_the_number_of_edges : edge_count G = #|E(G)|.
Proof. by []. Qed.

(** Adjacent pairs taken in one orientation, by enumeration rank, are counted exactly once. *)
Example rank_oriented_pairs_count_the_edges :
  #|[set p : G * G | (p.1 -- p.2) && (enum_rank p.1 < enum_rank p.2)%N]| = edge_count G.
Proof. exact: edge_count_rank. Qed.

Example isomorphic_graphs_have_the_same_count (H : sgraph) :
  G ≃ H -> edge_count G = edge_count H.
Proof. exact: edge_count_diso. Qed.

(** Positive: one edge already makes the count positive. *)
Example an_edge_gives_a_positive_count (x y : G) : x -- y -> 0 < edge_count G.
Proof. by move=> xy; apply/card_gt0P; exists [set x; y]; apply/edgesP; exists x, y. Qed.

End PublicClient.

(** Degenerate and concrete cases. *)
Example empty_and_one_vertex_graphs_have_no_edges :
  edge_count 'K_0 = 0 /\ edge_count 'K_1 = 0.
Proof. exact: edge_count_K0_K1. Qed.

Example K2_has_one_edge : edge_count 'K_2 = 1.
Proof. exact: edge_count_K2. Qed.

Example K3_has_three_edges : edge_count 'K_3 = 3.
Proof. exact: edge_count_K3. Qed.

Example complete_graph_count (n : nat) : edge_count 'K_n = 'C(n, 2).
Proof. exact: edge_count_Kn. Qed.

(** Negative: counting both orientations (six adjacent ordered pairs in [K_3]) is a different
    quantity. *)
Example K3_count_is_not_the_ordered_pair_count : edge_count 'K_3 <> 6.
Proof. by rewrite edge_count_K3. Qed.

Print Assumptions rank_oriented_pairs_count_the_edges.
Print Assumptions an_edge_gives_a_positive_count.
Print Assumptions complete_graph_count.
