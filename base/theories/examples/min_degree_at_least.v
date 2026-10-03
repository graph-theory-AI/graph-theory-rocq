(** Downstream use of the minimum-degree lower bound ([min_degree_at_least]), without corpus
    imports: the universal bound, its corner cases, and induced subgraphs. *)
From GTBase Require Import base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Bounds.
Variable G : sgraph.

Example zero_bound : min_degree_at_least G 0.
Proof. exact: min_degree_at_least0. Qed.

Example weaker_bounds_follow (d : nat) :
  min_degree_at_least G d.+1 -> min_degree_at_least G d.
Proof. exact: min_degree_at_least_le. Qed.

Example regular_graphs (d : nat) : regular G d -> min_degree_at_least G d.
Proof. exact: regular_min_degree_at_least. Qed.

Example bound_one_is_no_isolated_vertex :
  min_degree_at_least G 1 <-> forall v : G, exists w : G, v -- w.
Proof. exact: min_degree_at_least1P. Qed.

(** Given a vertex, the bound is at most the maximum degree and below the order. *)
Example bounded_by_Delta_and_order (d : nat) (v : G) :
  min_degree_at_least G d -> d <= Delta G /\ d < #|G|.
Proof.
by move=> h; split; [exact: (min_degree_at_least_Delta v h) | exact: (min_degree_at_least_lt_card v h)].
Qed.

(** An empty induced subgraph satisfies every bound. *)
Example empty_induced_subgraph (d : nat) : min_degree_at_least (induced (set0 : {set G})) d.
Proof. by move=> x; have := valP x; rewrite inE. Qed.

(** A one-vertex induced subgraph has an isolated vertex. *)
Example singleton_induced_subgraph (v : G) : ~ min_degree_at_least (induced [set v]) 1.
Proof.
move/(_ (Sub v (set11 v)))/card_gt0P => [y]; rewrite in_opn induced_edge /=.
by have /set1P -> := valP y; rewrite sg_irrefl.
Qed.

End Bounds.

(** The empty graph satisfies every bound: there is no attained minimum. *)
Example K0_every_bound (d : nat) : min_degree_at_least 'K_0 d.
Proof. exact: min_degree_at_least_K0. Qed.

Example K1_has_an_isolated_vertex : ~ min_degree_at_least 'K_1 1.
Proof. by move/(_ ord0)/card_gt0P => [w]; rewrite in_opn (ord1 w) sg_irrefl. Qed.

Example K2_bound_one_not_two : min_degree_at_least 'K_2 1 /\ ~ min_degree_at_least 'K_2 2.
Proof.
split; first exact: (@min_degree_at_least_Kn 1).
by move/(min_degree_at_least_lt_card (ord0 : 'K_2)); rewrite card_ord.
Qed.

(** The bound is not inherited by induced subgraphs: [K_2] has no isolated vertex, but its
    one-vertex induced subgraphs do. *)
Example not_inherited_by_induced_subgraphs :
  min_degree_at_least 'K_2 1 /\ ~ min_degree_at_least (induced [set (ord0 : 'K_2)]) 1.
Proof. by split; [exact: (@min_degree_at_least_Kn 1) | exact: singleton_induced_subgraph]. Qed.

Example complete_graphs (n : nat) : min_degree_at_least 'K_n.+1 n.
Proof. exact: min_degree_at_least_Kn. Qed.

Example complete_bipartite_graphs (n m : nat) : min_degree_at_least 'K_n,m (minn n m).
Proof. exact: min_degree_at_least_Knm. Qed.

Example k_connected_graphs (G : sgraph) (k : nat) :
  k.-connected G -> min_degree_at_least G k.
Proof. exact: min_degree_at_least_kconnected. Qed.

Example isomorphic_graphs (G H : sgraph) (i : G ≃ H) (d : nat) :
  min_degree_at_least G d -> min_degree_at_least H d.
Proof. exact: min_degree_at_least_diso. Qed.

Print Assumptions singleton_induced_subgraph.
Print Assumptions K2_bound_one_not_two.
Print Assumptions not_inherited_by_induced_subgraphs.
Print Assumptions isomorphic_graphs.
