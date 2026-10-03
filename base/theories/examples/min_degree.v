(** Downstream use of the exact (attained) minimum degree ([min_degree]), without corpus imports:
    attainment, uniqueness, existence with a vertex, and the empty-graph and wrong-degree corners. *)
From GTBase Require Import base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Exact.
Variable G : sgraph.

Example lower_bound_and_attained (d : nat) :
  min_degree G d -> min_degree_at_least G d /\ exists v : G, #|N(v)| = d.
Proof. by move=> h; split; [exact: min_degree_lower h | exact: min_degree_attained h]. Qed.

Example unique (d d' : nat) : min_degree G d -> min_degree G d' -> d = d'.
Proof. exact: min_degree_uniq. Qed.

Example exists_with_a_vertex (v : G) : exists d, min_degree G d.
Proof. exact: (min_degree_exists v). Qed.

Example greatest_lower_bound (d d' : nat) :
  min_degree G d -> min_degree_at_least G d' <-> d' <= d.
Proof. exact: min_degree_at_leastE. Qed.

Example below_Delta_and_order (d : nat) : min_degree G d -> d <= Delta G /\ d < #|G|.
Proof. by move=> h; split; [exact: min_degree_Delta h | exact: min_degree_lt_card h]. Qed.

Example regular_with_a_vertex (d : nat) (v : G) : regular G d -> min_degree G d.
Proof. exact: regular_min_degree. Qed.

End Exact.

(** The empty graph has no minimum degree, although it satisfies every lower bound. *)
Example K0_no_minimum (d : nat) : ~ min_degree 'K_0 d /\ min_degree_at_least 'K_0 d.
Proof. by split; [exact: min_degree_K0 | exact: min_degree_at_least_K0]. Qed.

Example K1_minimum_zero : min_degree 'K_1 0.
Proof. exact: (@min_degree_Kn 0). Qed.

Example K2_minimum_one : min_degree 'K_2 1.
Proof. exact: (@min_degree_Kn 1). Qed.

Example K3_minimum_two : min_degree 'K_3 2.
Proof. exact: (@min_degree_Kn 2). Qed.

Example complete_graphs (n : nat) : min_degree 'K_n.+1 n.
Proof. exact: min_degree_Kn. Qed.

(** Wrong degrees fail: [K_3] has minimum degree 2, neither 1 nor 3. *)
Example K3_not_one_or_three : ~ min_degree 'K_3 1 /\ ~ min_degree 'K_3 3.
Proof. by split=> h; have := min_degree_uniq h (@min_degree_Kn 2). Qed.

Example isomorphic_graphs (G H : sgraph) (i : G ≃ H) (d : nat) :
  min_degree G d -> min_degree H d.
Proof. exact: min_degree_diso. Qed.

(** The presentation with the attaining vertex first is equivalent. *)
Example attained_first (G : sgraph) (d : nat) :
  min_degree G d <-> (exists v : G, #|N(v)| = d) /\ min_degree_at_least G d.
Proof. exact: min_degree_attained_firstE. Qed.

Print Assumptions K0_no_minimum.
Print Assumptions K3_not_one_or_three.
Print Assumptions exists_with_a_vertex.
Print Assumptions isomorphic_graphs.
