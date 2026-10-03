(** C15: supplied branch-set models on the same map, frozen at 35b6b165295fb373d864d646d74284c4751dae65.
    Nested conjunctions, disjointness and edge-witness presentations are related
    unconditionally to upstream minor_rmap. Every whole statement retains its
    original guards, quantifier order and conclusion. *)
From GTBase Require Import base minor_models.
From Minor.conjectures Require Import X200.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Legacy.
Definition x200_minor_model (G H : sgraph) (branch : H -> {set G}) : Prop := (forall h : H, branch h != set0) /\ (forall h : H, connected (branch h)) /\ (forall h1 h2 : H, h1 != h2 -> branch h1 :&: branch h2 = set0) /\ (forall h1 h2 : H, h1 -- h2 -> exists x y : G, [/\ x \in branch h1, y \in branch h2 & x -- y]).

Definition x200_k_disjoint_H_models (G H : sgraph) (k : nat) : Prop := exists branch : 'I_k -> H -> {set G}, (forall i : 'I_k, @Legacy.x200_minor_model G H (branch i)) /\ forall i j : 'I_k, i != j -> @x200_model_vertices G H (branch i) :&: @x200_model_vertices G H (branch j) = set0.

Definition x200_H_model_hitting_set (G H : sgraph) (X : {set G}) : Prop := forall branch : H -> {set G}, @Legacy.x200_minor_model G H branch -> @x200_model_vertices G H branch :&: X != set0.

Definition x200_H_model_erdos_posa_oklogk (H : sgraph) : Prop := exists C : nat, forall (G : sgraph) (k : nat), 1 <= k -> Legacy.x200_k_disjoint_H_models G H k \/ exists X : {set G}, #|X| <= C * k * (trunc_log 2 k.+1).+1 /\ @Legacy.x200_H_model_hitting_set G H X.

Definition planar_H_model_erdos_posa_oklogk_statement : Prop := forall H : sgraph, wagner_planar H -> Legacy.x200_H_model_erdos_posa_oklogk H.

End Legacy.

Lemma x200_minor_model_compat (G H : sgraph) (branch : H -> {set G}) :
  @Legacy.x200_minor_model G H branch <-> @x200_minor_model G H branch.
Proof. exact: (iff_sym (@minor_rmap_nestedE G H branch)). Qed.

Lemma x200_k_disjoint_H_models_compat (G H : sgraph) (k : nat) :
  Legacy.x200_k_disjoint_H_models G H k <-> x200_k_disjoint_H_models G H k.
Proof.
split=> -[branch [models dj]]; exists branch; split=> // i.
- exact: (proj1 (@x200_minor_model_compat G H (branch i)) (models i)).
- exact: (proj2 (@x200_minor_model_compat G H (branch i)) (models i)).
Qed.

Lemma x200_H_model_hitting_set_compat (G H : sgraph) (X : {set G}) :
  @Legacy.x200_H_model_hitting_set G H X <-> @x200_H_model_hitting_set G H X.
Proof.
split=> hit branch model; apply: hit.
- exact: (proj2 (@x200_minor_model_compat G H branch) model).
- exact: (proj1 (@x200_minor_model_compat G H branch) model).
Qed.

Lemma x200_H_model_erdos_posa_oklogk_compat (H : sgraph) :
  Legacy.x200_H_model_erdos_posa_oklogk H <-> x200_H_model_erdos_posa_oklogk H.
Proof.
split=> -[C bound]; exists C => G k pos; have [models|[X [sizeX hit]]] := bound G k pos.
- left; exact: (proj1 (@x200_k_disjoint_H_models_compat G H k) models).
- right; exists X; split=> //.
  exact: (proj1 (@x200_H_model_hitting_set_compat G H X) hit).
- left; exact: (proj2 (@x200_k_disjoint_H_models_compat G H k) models).
- right; exists X; split=> //.
  exact: (proj2 (@x200_H_model_hitting_set_compat G H X) hit).
Qed.

Lemma planar_H_model_erdos_posa_oklogk_statement_compat :
  Legacy.planar_H_model_erdos_posa_oklogk_statement <->
  planar_H_model_erdos_posa_oklogk_statement.
Proof.
split=> statement H planar.
- exact: (proj1 (x200_H_model_erdos_posa_oklogk_compat H) (statement H planar)).
- exact: (proj2 (x200_H_model_erdos_posa_oklogk_compat H) (statement H planar)).
Qed.
