(** C13 frozen supplied bag decompositions; baseline 58d6d609.
    All guards, supplied data, whole statements and known defects are retained. *)

From GTBase Require Import base bag_decompositions.
From GTMisc.conjectures Require Import X102 X169.
From Minor.migration Require bag_decompositions.
From GTMisc.migration Require induced_free simple_edges.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Legacy.

Definition x102_tree_alpha_at_most (G : sgraph) (a : nat) : Prop := exists (T : sgraph) (bag : T -> {set G}), is_tree [set: T] /\ Minor.migration.bag_decompositions.Legacy.x27_tree_decomposition bag /\ forall t : T, α(bag t) <= a.

Definition x102_free_class_tree_alpha_bounded (I : finType) (F : I -> sgraph) : Prop := exists a : nat, forall G : sgraph, (forall i : I, x102_induced_free G (F i)) -> Legacy.x102_tree_alpha_at_most G a.

Definition bounded_tree_independence_forbidden_family_statement : Prop := forall (I : finType) (F : I -> sgraph), Legacy.x102_free_class_tree_alpha_bounded F <-> exists i1 i2 i3 : I, x102_complete_bipartite_graph (F i1) /\ x102_subdivided_multiclaw (F i2) /\ x102_line_graph_of_subdivided_multiclaw (F i3).

Definition x169_tree_decomposition (G T : sgraph) (bag : T -> {set G}) : Prop := is_tree [set: T] /\ (forall v : G, exists t : T, v \in bag t) /\ (forall x y : G, x -- y -> exists t : T, x \in bag t /\ y \in bag t) /\ (forall v : G, connected [set t : T | v \in bag t]).

Definition x169_clique_tree (G T : sgraph) (bag : T -> {set G}) : Prop := Legacy.x169_tree_decomposition bag /\ forall t : T, cliqueb (bag t).

Definition x169_chordal (G : sgraph) : Prop := exists (T : sgraph) (bag : T -> {set G}), Legacy.x169_clique_tree bag.

Definition x169_clique_tree_degree_at_most (G : sgraph) (D : nat) : Prop := exists (T : sgraph) (bag : T -> {set G}), Legacy.x169_clique_tree bag /\ forall t : T, #|N(t)| <= D.

Definition x169_polytime_decides_TS_connectivity (k D : nat) : Prop := polytime_decides_graph_on (fun G : sgraph => Legacy.x169_chordal G /\ Legacy.x169_clique_tree_degree_at_most G D) (fun G : sgraph => x169_token_sliding_connected G k).

Definition token_sliding_chordal_clique_tree_degree_polytime_statement : Prop := forall k D : nat, Legacy.x169_polytime_decides_TS_connectivity k D.

End Legacy.

Lemma x102_tree_alpha_at_most_compat (G : sgraph) (a : nat) :
  @Legacy.x102_tree_alpha_at_most G a <-> @x102_tree_alpha_at_most G a.
Proof. exact: iff_refl. Qed.

Lemma x102_free_class_tree_alpha_bounded_compat (I : finType) (F : I -> sgraph) :
  @Legacy.x102_free_class_tree_alpha_bounded I F <-> @x102_free_class_tree_alpha_bounded I F.
Proof. exact: iff_refl. Qed.

Lemma bounded_tree_independence_forbidden_family_statement_compat  :
  @Legacy.bounded_tree_independence_forbidden_family_statement <-> @bounded_tree_independence_forbidden_family_statement.
Proof. exact: iff_refl. Qed.

Lemma x169_tree_decomposition_compat (G T : sgraph) (bag : T -> {set G}) :
  @Legacy.x169_tree_decomposition G T bag <-> @x169_tree_decomposition G T bag.
Proof. rewrite /Legacy.x169_tree_decomposition /x169_tree_decomposition.
exact: iff_sym (tree_bag_decompositionP bag). Qed.

Lemma x169_clique_tree_compat (G T : sgraph) (bag : T -> {set G}) :
  @Legacy.x169_clique_tree G T bag <-> @x169_clique_tree G T bag.
Proof. rewrite /Legacy.x169_clique_tree /x169_clique_tree.
setoid_rewrite x169_tree_decomposition_compat; reflexivity. Qed.

Lemma x169_chordal_compat (G : sgraph) :
  @Legacy.x169_chordal G <-> @x169_chordal G.
Proof. rewrite /Legacy.x169_chordal /x169_chordal.
setoid_rewrite x169_clique_tree_compat; reflexivity. Qed.

Lemma x169_clique_tree_degree_at_most_compat (G : sgraph) (D : nat) :
  @Legacy.x169_clique_tree_degree_at_most G D <-> @x169_clique_tree_degree_at_most G D.
Proof. rewrite /Legacy.x169_clique_tree_degree_at_most /x169_clique_tree_degree_at_most.
setoid_rewrite x169_clique_tree_compat; reflexivity. Qed.

Lemma x169_polytime_decides_TS_connectivity_compat (k D : nat) :
  @Legacy.x169_polytime_decides_TS_connectivity k D <-> @x169_polytime_decides_TS_connectivity k D.
Proof. rewrite /Legacy.x169_polytime_decides_TS_connectivity /x169_polytime_decides_TS_connectivity
 /polytime_decides_graph_on /polytime_decides_on_class /decides_on_class.
setoid_rewrite x169_chordal_compat;
setoid_rewrite x169_clique_tree_degree_at_most_compat; reflexivity. Qed.

Lemma token_sliding_chordal_clique_tree_degree_polytime_statement_compat  :
  @Legacy.token_sliding_chordal_clique_tree_degree_polytime_statement <-> @token_sliding_chordal_clique_tree_degree_polytime_statement.
Proof. rewrite /Legacy.token_sliding_chordal_clique_tree_degree_polytime_statement
 /token_sliding_chordal_clique_tree_degree_polytime_statement.
setoid_rewrite x169_polytime_decides_TS_connectivity_compat; reflexivity. Qed.

(** Complete historical composition; all older snapshots remain unchanged. *)
Module X102Original.

Definition x102_free_class_tree_alpha_bounded (I : finType) (F : I -> sgraph) : Prop := exists a : nat, forall G : sgraph, (forall i : I, GTMisc.migration.induced_free.Legacy.x102_induced_free G (F i)) -> Legacy.x102_tree_alpha_at_most G a.

Definition bounded_tree_independence_forbidden_family_statement : Prop := forall (I : finType) (F : I -> sgraph), X102Original.x102_free_class_tree_alpha_bounded F <-> exists i1 i2 i3 : I, x102_complete_bipartite_graph (F i1) /\ x102_subdivided_multiclaw (F i2) /\ GTMisc.migration.simple_edges.X102Legacy.line_graph_of_subdivided_multiclaw (F i3).

End X102Original.

Lemma x102_free_class_tree_alpha_bounded_original_compat (I : finType) (F : I -> sgraph) :
  @X102Original.x102_free_class_tree_alpha_bounded I F <-> @x102_free_class_tree_alpha_bounded I F.
Proof. rewrite /X102Original.x102_free_class_tree_alpha_bounded /x102_free_class_tree_alpha_bounded; setoid_rewrite GTMisc.migration.induced_free.x102_induced_free_compat; reflexivity. Qed.

Lemma bounded_tree_independence_forbidden_family_statement_original_compat  :
  @X102Original.bounded_tree_independence_forbidden_family_statement <-> @bounded_tree_independence_forbidden_family_statement.
Proof. rewrite /X102Original.bounded_tree_independence_forbidden_family_statement /bounded_tree_independence_forbidden_family_statement; setoid_rewrite x102_free_class_tree_alpha_bounded_original_compat; setoid_rewrite GTMisc.migration.simple_edges.x102_line_graph_of_subdivided_multiclaw_compat; reflexivity. Qed.
