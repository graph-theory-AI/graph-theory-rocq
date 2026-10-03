(** C13 frozen supplied bag decompositions; baseline 58d6d609.
    All guards, supplied data, whole statements and known defects are retained. *)

From GTBase Require Import base bag_decompositions.
From Minor.conjectures Require Import X27 X42 X67 X95 X121 X127 X201.
From Minor.migration Require induced_free consecutive_in_cycle consecutive_in_path path_tree.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Legacy.

Definition x27_tree_decomposition (G T : sgraph) (bag : T -> {set G}) : Prop := (forall v : G, [exists t : T, v \in bag t]) /\ (forall x y : G, x -- y -> [exists t : T, (x \in bag t) && (y \in bag t)]) /\ forall v : G, connected [set t : T | v \in bag t].

Definition x121_tree_alpha_le (G : sgraph) (k : nat) : Prop := exists (T : sgraph) (bag : T -> {set G}), is_tree [set: T] /\ Legacy.x27_tree_decomposition bag /\ forall t : T, α(bag t) <= k.

Definition x127_two_tree_width_le (G : sgraph) (k : nat) : Prop := exists (T1 : sgraph) (bag1 : T1 -> {set G}) (T2 : sgraph) (bag2 : T2 -> {set G}), [/\ is_tree [set: T1], Legacy.x27_tree_decomposition bag1, is_tree [set: T2], Legacy.x27_tree_decomposition bag2 & forall (t1 : T1) (t2 : T2), #|bag1 t1 :&: bag2 t2| <= k].

Definition dujmovic_joret_morin_norin_wood_two_tree_width_chi_statement : Prop := exists f : nat -> nat, forall (k : nat) (G : sgraph), Legacy.x127_two_tree_width_le G k -> χ([set: G]) <= f k.

Definition x27_treewidth_at_most (G : sgraph) (k : nat) : Prop := exists (T : sgraph) (bag : T -> {set G}), is_tree [set: T] /\ Legacy.x27_tree_decomposition bag /\ forall t : T, #|bag t| <= k.+1.

Definition dallard_milanic_storgel_tw_omega_tree_alpha_statement : Prop := forall C : sgraph -> Prop, (exists f : nat -> nat, forall G : sgraph, C G -> Legacy.x27_treewidth_at_most G (f (x121_omega G))) <-> (exists k : nat, forall G : sgraph, C G -> Legacy.x121_tree_alpha_le G k).

Definition x201_treewidth_at_least (G : sgraph) (r : nat) : Prop := forall k : nat, Legacy.x27_treewidth_at_most G k -> r <= k.

Definition x201_k_disjoint_large_treewidth_subgraphs (G : sgraph) (r k : nat) : Prop := exists S : 'I_k -> {set G}, (forall i : 'I_k, S i != set0) /\ (forall i j : 'I_k, i != j -> S i :&: S j = set0) /\ forall i : 'I_k, Legacy.x201_treewidth_at_least (induced (S i)) r.

Definition treewidth_vertex_disjoint_subgraphs_log_bound_statement : Prop := exists f : nat -> nat, forall (r k : nat) (G : sgraph), 1 <= r -> 1 <= k -> Legacy.x201_treewidth_at_least G (f r * k * (trunc_log 2 k.+1).+1) -> Legacy.x201_k_disjoint_large_treewidth_subgraphs G r k.

Definition bounded_degree_even_hole_free_bounded_treewidth_statement : Prop := exists f : nat -> nat, forall (d : nat) (G : sgraph), Delta G <= d -> x27_even_hole_free G -> Legacy.x27_treewidth_at_most G (f d).

Definition even_hole_k4_diamond_free_bounded_treewidth_statement : Prop := exists c : nat, forall G : sgraph, x27_even_hole_free G -> x42_induced_free G 'K_4 -> x42_induced_free G x42_diamond -> Legacy.x27_treewidth_at_most G c.

Definition theta_triangle_free_bounded_degree_treewidth_statement : Prop := exists f : nat -> nat, forall (t : nat) (G : sgraph), 4 <= t -> Delta G <= t -> triangle_free G -> ~ x67_theta G -> Legacy.x27_treewidth_at_most G (f t).

Definition x95_pathwidth_at_most (G : sgraph) (k : nat) : Prop := exists (T : sgraph) (bag : T -> {set G}), x95_path_index_graph T /\ Legacy.x27_tree_decomposition bag /\ forall t : T, #|bag t| <= k.+1.

Definition x95_subgraph_indexed_tree_decomposition_width_at_most (G : sgraph) (k : nat) : Prop := exists (T : sgraph) (bag : T -> {set G}), is_tree [set: T] /\ x95_index_tree_subgraph T G /\ Legacy.x27_tree_decomposition bag /\ forall t : T, #|bag t| <= k.+1.

Definition subgraph_indexed_tree_decomposition_pathwidth_bound_statement : Prop := exists f : nat -> nat, forall (p : nat) (G : sgraph), connected [set: G] -> Legacy.x95_pathwidth_at_most G p -> Legacy.x95_subgraph_indexed_tree_decomposition_width_at_most G (f p).

End Legacy.

Lemma x27_tree_decomposition_compat (G T : sgraph) (bag : T -> {set G}) :
  @Legacy.x27_tree_decomposition G T bag <-> @x27_tree_decomposition G T bag.
Proof. exact: iff_refl. Qed.

Lemma x121_tree_alpha_le_compat (G : sgraph) (k : nat) :
  @Legacy.x121_tree_alpha_le G k <-> @x121_tree_alpha_le G k.
Proof. exact: iff_refl. Qed.

Lemma x127_two_tree_width_le_compat (G : sgraph) (k : nat) :
  @Legacy.x127_two_tree_width_le G k <-> @x127_two_tree_width_le G k.
Proof. exact: iff_refl. Qed.

Lemma dujmovic_joret_morin_norin_wood_two_tree_width_chi_statement_compat  :
  @Legacy.dujmovic_joret_morin_norin_wood_two_tree_width_chi_statement <-> @dujmovic_joret_morin_norin_wood_two_tree_width_chi_statement.
Proof. exact: iff_refl. Qed.

Lemma x27_treewidth_at_most_compat (G : sgraph) (k : nat) :
  @Legacy.x27_treewidth_at_most G k <-> @x27_treewidth_at_most G k.
Proof. exact: iff_refl. Qed.

Lemma dallard_milanic_storgel_tw_omega_tree_alpha_statement_compat  :
  @Legacy.dallard_milanic_storgel_tw_omega_tree_alpha_statement <-> @dallard_milanic_storgel_tw_omega_tree_alpha_statement.
Proof. exact: iff_refl. Qed.

Lemma x201_treewidth_at_least_compat (G : sgraph) (r : nat) :
  @Legacy.x201_treewidth_at_least G r <-> @x201_treewidth_at_least G r.
Proof. exact: iff_refl. Qed.

Lemma x201_k_disjoint_large_treewidth_subgraphs_compat (G : sgraph) (r k : nat) :
  @Legacy.x201_k_disjoint_large_treewidth_subgraphs G r k <-> @x201_k_disjoint_large_treewidth_subgraphs G r k.
Proof. exact: iff_refl. Qed.

Lemma treewidth_vertex_disjoint_subgraphs_log_bound_statement_compat  :
  @Legacy.treewidth_vertex_disjoint_subgraphs_log_bound_statement <-> @treewidth_vertex_disjoint_subgraphs_log_bound_statement.
Proof. exact: iff_refl. Qed.

Lemma bounded_degree_even_hole_free_bounded_treewidth_statement_compat  :
  @Legacy.bounded_degree_even_hole_free_bounded_treewidth_statement <-> @bounded_degree_even_hole_free_bounded_treewidth_statement.
Proof. exact: iff_refl. Qed.

Lemma even_hole_k4_diamond_free_bounded_treewidth_statement_compat  :
  @Legacy.even_hole_k4_diamond_free_bounded_treewidth_statement <-> @even_hole_k4_diamond_free_bounded_treewidth_statement.
Proof. exact: iff_refl. Qed.

Lemma theta_triangle_free_bounded_degree_treewidth_statement_compat  :
  @Legacy.theta_triangle_free_bounded_degree_treewidth_statement <-> @theta_triangle_free_bounded_degree_treewidth_statement.
Proof. exact: iff_refl. Qed.

Lemma x95_pathwidth_at_most_compat (G : sgraph) (k : nat) :
  @Legacy.x95_pathwidth_at_most G k <-> @x95_pathwidth_at_most G k.
Proof. exact: iff_refl. Qed.

Lemma x95_subgraph_indexed_tree_decomposition_width_at_most_compat (G : sgraph) (k : nat) :
  @Legacy.x95_subgraph_indexed_tree_decomposition_width_at_most G k <-> @x95_subgraph_indexed_tree_decomposition_width_at_most G k.
Proof. exact: iff_refl. Qed.

Lemma subgraph_indexed_tree_decomposition_pathwidth_bound_statement_compat  :
  @Legacy.subgraph_indexed_tree_decomposition_pathwidth_bound_statement <-> @subgraph_indexed_tree_decomposition_pathwidth_bound_statement.
Proof. exact: iff_refl. Qed.

(** Complete historical composition; all older snapshots remain unchanged. *)
Module X27Original.

Definition bounded_degree_even_hole_free_bounded_treewidth_statement : Prop := exists f : nat -> nat, forall (d : nat) (G : sgraph), Delta G <= d -> Minor.migration.consecutive_in_cycle.X27Legacy.even_hole_free G -> Legacy.x27_treewidth_at_most G (f d).

End X27Original.

(** Complete historical composition; all older snapshots remain unchanged. *)
Module X42Original.

Definition even_hole_k4_diamond_free_bounded_treewidth_statement : Prop := exists c : nat, forall G : sgraph, Minor.migration.consecutive_in_cycle.X27Legacy.even_hole_free G -> Minor.migration.induced_free.Legacy.x42_induced_free G 'K_4 -> Minor.migration.induced_free.Legacy.x42_induced_free G x42_diamond -> Legacy.x27_treewidth_at_most G c.

End X42Original.

(** Complete historical composition; all older snapshots remain unchanged. *)
Module X67Original.

Definition theta_triangle_free_bounded_degree_treewidth_statement : Prop := exists f : nat -> nat, forall (t : nat) (G : sgraph), 4 <= t -> Delta G <= t -> triangle_free G -> ~ Minor.migration.consecutive_in_path.X67Original.theta G -> Legacy.x27_treewidth_at_most G (f t).

End X67Original.

(** Complete historical composition; all older snapshots remain unchanged. *)
Module X95Original.

Definition x95_pathwidth_at_most (G : sgraph) (k : nat) : Prop := exists (T : sgraph) (bag : T -> {set G}), Minor.migration.path_tree.Legacy.x95_path_index_graph T /\ Legacy.x27_tree_decomposition bag /\ forall t : T, #|bag t| <= k.+1.

Definition subgraph_indexed_tree_decomposition_pathwidth_bound_statement : Prop := exists f : nat -> nat, forall (p : nat) (G : sgraph), connected [set: G] -> X95Original.x95_pathwidth_at_most G p -> Legacy.x95_subgraph_indexed_tree_decomposition_width_at_most G (f p).

End X95Original.

Lemma bounded_degree_even_hole_free_bounded_treewidth_statement_original_compat  :
  @X27Original.bounded_degree_even_hole_free_bounded_treewidth_statement <-> @bounded_degree_even_hole_free_bounded_treewidth_statement.
Proof. rewrite /X27Original.bounded_degree_even_hole_free_bounded_treewidth_statement /bounded_degree_even_hole_free_bounded_treewidth_statement; setoid_rewrite Minor.migration.consecutive_in_cycle.x27_even_hole_free_compat; reflexivity. Qed.

Lemma even_hole_k4_diamond_free_bounded_treewidth_statement_original_compat  :
  @X42Original.even_hole_k4_diamond_free_bounded_treewidth_statement <-> @even_hole_k4_diamond_free_bounded_treewidth_statement.
Proof. rewrite /X42Original.even_hole_k4_diamond_free_bounded_treewidth_statement /even_hole_k4_diamond_free_bounded_treewidth_statement; setoid_rewrite Minor.migration.consecutive_in_cycle.x27_even_hole_free_compat; setoid_rewrite Minor.migration.induced_free.x42_induced_free_compat; reflexivity. Qed.

Lemma theta_triangle_free_bounded_degree_treewidth_statement_original_compat  :
  @X67Original.theta_triangle_free_bounded_degree_treewidth_statement <-> @theta_triangle_free_bounded_degree_treewidth_statement.
Proof. rewrite /X67Original.theta_triangle_free_bounded_degree_treewidth_statement /theta_triangle_free_bounded_degree_treewidth_statement; setoid_rewrite Minor.migration.consecutive_in_path.x67_theta_original_compat; reflexivity. Qed.

Lemma x95_pathwidth_at_most_original_compat (G : sgraph) (k : nat) :
  @X95Original.x95_pathwidth_at_most G k <-> @x95_pathwidth_at_most G k.
Proof. exact: iff_refl. Qed.

Lemma subgraph_indexed_tree_decomposition_pathwidth_bound_statement_original_compat  :
  @X95Original.subgraph_indexed_tree_decomposition_pathwidth_bound_statement <-> @subgraph_indexed_tree_decomposition_pathwidth_bound_statement.
Proof. exact: iff_refl. Qed.
