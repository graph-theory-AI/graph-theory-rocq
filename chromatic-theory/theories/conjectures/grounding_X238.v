(** * Chromatic.conjectures.grounding_X238 -- grounding certificates of wave X238.

    For both rows: hyp_inhabited (the hypotheses hold on a concrete instance, and the statement then
    yields its conclusion there), not_trivially_true and helper_sanity for [x238_tau], with positive
    and negative instances (both rows use it).  not_trivially_true uses a false strengthened
    conclusion that implies the row, a constant bound refuted at d = 1 by the complete graphs
    (P_3-free, tau_1(K_n) = n = chi(K_n)): the contract form, a variant without a load-bearing
    hypothesis, would need graphs of bounded tau_d (d >= 2) and large chromatic number, which the
    corpus does not have (a deviation recorded for the A3 verifier, as in X236; design read (89)). *)

From GTBase Require Export base.
From GTBase Require Import common graph_classes complete_multipartite_graphs path_graphs poly_nat.
From Chromatic.conjectures Require Import X238.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Instances *)

Lemma g238_chi_K (n : nat) : χ([set: 'K_n]) = n.
Proof.
have cl : clique [set: 'K_n] by move=> x y _ _ xy.
by rewrite (chi_clique cl) cardsT card_ord.
Qed.

Lemma g238_chi_le_card (G : sgraph) : χ([set: G]) <= #|G|.
Proof. by rewrite -cardsT; exact: leq_chi. Qed.

(** tau_1(G) = |G|: the edgeless K_1(|G|) is a subgraph, and K_1(s) has s vertices. *)
Lemma g238_tau1 (G : sgraph) : x238_tau G 1 #|G|.
Proof.
split.
- apply/has_subgraphP; exists (fun x : complete_multipartite_graph 1 #|G| => enum_val x.2); split.
    move=> [a i] [b j] /= /enum_val_inj ij.
    by rewrite (ord1 a) (ord1 b) ij.
  by move=> x y; rewrite complete_multipartite_edgeE (ord1 x.1) (ord1 y.1) eqxx.
- by move=> s /has_subgraph_card; rewrite card_complete_multipartite_graph mul1n.
Qed.

Lemma g238_tau1_card (G : sgraph) (t : nat) : x238_tau G 1 t -> t = #|G|.
Proof.
case=> /has_subgraph_card + max; rewrite card_complete_multipartite_graph mul1n => le.
by apply/eqP; rewrite eqn_leq le; case: (g238_tau1 G) => h _; exact: max h.
Qed.

Lemma g238_tau_K1 : x238_tau 'K_1 1 1.
Proof. by have := g238_tau1 'K_1; rewrite card_ord. Qed.

Lemma g238_not_tau_K1_0 : ~ x238_tau 'K_1 1 0.
Proof. by move=> /g238_tau1_card; rewrite card_ord. Qed.

(** tau_2(K_3) = 1: an edge is K_{1,1}, and K_{2,2} needs four vertices. *)
Lemma g238_tau_K3_2 : x238_tau 'K_3 2 1.
Proof.
split.
- apply/has_subgraphP.
  exists (fun x : complete_multipartite_graph 2 1 => widen_ord (isT : 2 <= 3) x.1); split.
    move=> [a i] [b j] /= /(congr1 val) /= /val_inj ab.
    by rewrite ab (ord1 i) (ord1 j).
  move=> x y; rewrite complete_multipartite_edgeE => xy.
  by rewrite /edge_rel /= -(inj_eq val_inj) /= (inj_eq val_inj).
- move=> s /has_subgraph_card; rewrite card_complete_multipartite_graph card_ord.
  by case: s => [|[|s]] //; rewrite !mulnS.
Qed.

Lemma g238_not_tau_K3_2_2 : ~ x238_tau 'K_3 2 2.
Proof. by case=> /has_subgraph_card; rewrite card_complete_multipartite_graph card_ord. Qed.

(** Complete graphs are P_3-free (P_3 has a non-edge). *)
Lemma g238_K_P3_free (n : nat) : induced_free 'K_n (ordinal_path 3).
Proof.
apply: (@induced_free_Kn n (ordinal_path 3) (@Ordinal 3 0 isT) (@Ordinal 3 2 isT)) => //.
Qed.

(** ** Row arxiv:2202.05557#01 *)

Definition g238_path_hyp_claim : Prop :=
  [/\ induced_free 'K_1 (ordinal_path 2), x238_tau 'K_1 1 1 &
      (path_free_polynomial_tau_bound_statement -> exists p : seq nat, χ([set: 'K_1]) <= horner_nat p 1)].

Theorem g238_path_hyp_inhabited : g238_path_hyp_claim.
Proof.
have free : induced_free 'K_1 (ordinal_path 2) by apply: induced_free_card; rewrite !card_ord.
split=> //; first exact: g238_tau_K1.
by move=> h; have [p hp] := h 2 1 (leqnn 1); exists p; exact: hp _ _ free g238_tau_K1.
Qed.

(** The strengthened conclusion, one constant bound, is false: at k = 3 and d = 1, K_(c+1) is
    P_3-free with tau_1 = chi = c + 1.  It implies the row (p = [:: c]). *)
Definition g238_path_constant_bound : Prop :=
  forall k d : nat, 1 <= d ->
    exists c : nat, forall (G : sgraph) (t : nat),
      induced_free G (ordinal_path k) -> x238_tau G d t -> χ([set: G]) <= c.

Definition g238_path_ntt_claim : Prop :=
  ~ g238_path_constant_bound /\ (g238_path_constant_bound -> path_free_polynomial_tau_bound_statement).

Theorem g238_path_not_trivially_true : g238_path_ntt_claim.
Proof.
split.
- move=> h; have [c hc] := h 3 1 (leqnn 1).
  have tau : x238_tau 'K_(c.+1) 1 c.+1 by have := g238_tau1 'K_(c.+1); rewrite card_ord.
  by have := hc 'K_(c.+1) c.+1 (@g238_K_P3_free c.+1) tau; rewrite g238_chi_K ltnn.
- move=> h k d d1; have [c hc] := h k d d1; exists [:: c] => G t free tau.
  by rewrite horner_nat_cons horner_nat_nil muln0 addn0; exact: hc free tau.
Qed.

(** ** Row arxiv:2202.05557#02 *)

Lemma g238_all_hereditary : hereditary_class (fun _ : sgraph => True).
Proof. by split. Qed.

Lemma g238_all_tau1_bounded :
  exists f : nat -> nat, forall (G : sgraph) (t : nat), True -> x238_tau G 1 t -> χ([set: G]) <= f t.
Proof. by exists id => G t _ /g238_tau1_card ->; exact: g238_chi_le_card. Qed.

Definition g238_hered_hyp_claim : Prop :=
  [/\ hereditary_class (fun _ : sgraph => True),
      (exists f : nat -> nat, forall (G : sgraph) (t : nat), True -> x238_tau G 1 t -> χ([set: G]) <= f t) &
      (tau_bounded_hereditary_polynomial_statement ->
         exists p : seq nat, forall (G : sgraph) (t : nat), x238_tau G 1 t -> χ([set: G]) <= horner_nat p t)].

Theorem g238_hered_hyp_inhabited : g238_hered_hyp_claim.
Proof.
split; [exact: g238_all_hereditary | exact: g238_all_tau1_bounded |].
move=> h; have [p hp] := h _ 1 g238_all_hereditary (leqnn 1) g238_all_tau1_bounded.
by exists p => G t; exact: hp G t I.
Qed.

(** The strengthened conclusion, one constant bound, is false: for the class of all graphs, d = 1
    and f = id, K_(c+1) has tau_1 = chi = c + 1.  It implies the row (p = [:: c]). *)
Definition g238_hered_constant_bound : Prop :=
  forall (C : sgraph -> Prop) (d : nat), hereditary_class C -> 1 <= d ->
    (exists f : nat -> nat, forall (G : sgraph) (t : nat), C G -> x238_tau G d t -> χ([set: G]) <= f t) ->
    exists c : nat, forall (G : sgraph) (t : nat), C G -> x238_tau G d t -> χ([set: G]) <= c.

Definition g238_hered_ntt_claim : Prop :=
  ~ g238_hered_constant_bound /\ (g238_hered_constant_bound -> tau_bounded_hereditary_polynomial_statement).

Theorem g238_hered_not_trivially_true : g238_hered_ntt_claim.
Proof.
split.
- move=> h; have [c hc] := h _ 1 g238_all_hereditary (leqnn 1) g238_all_tau1_bounded.
  have tau : x238_tau 'K_(c.+1) 1 c.+1 by have := g238_tau1 'K_(c.+1); rewrite card_ord.
  by have := hc 'K_(c.+1) c.+1 I tau; rewrite g238_chi_K ltnn.
- move=> h C d hC d1 hf; have [c hc] := h C d hC d1 hf; exists [:: c] => G t inC tau.
  by rewrite horner_nat_cons horner_nat_nil muln0 addn0; exact: hc inC tau.
Qed.

(** ** The helper [x238_tau] (both rows) *)

Definition g238_tau_helper_claim : Prop :=
  [/\ x238_tau 'K_1 1 1, (forall G : sgraph, x238_tau G 1 #|G|), x238_tau 'K_3 2 1,
      ~ x238_tau 'K_1 1 0 & ~ x238_tau 'K_3 2 2].

Theorem g238_tau_helper_sanity : g238_tau_helper_claim.
Proof.
split; [exact: g238_tau_K1 | exact: g238_tau1 | exact: g238_tau_K3_2 | exact: g238_not_tau_K1_0
       | exact: g238_not_tau_K3_2_2].
Qed.
