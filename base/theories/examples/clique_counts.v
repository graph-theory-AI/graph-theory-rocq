(** Downstream use of the three clique counts of [GTBase.clique_counts], without corpus imports: complete
    graphs, edgeless graphs and the K_0/K_1/K_2/K_3 corners.  The three views give different numbers. *)
From GTBase Require Import base clique_counts.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** In a complete graph every vertex set is a clique. *)
Lemma Kn_cliques (n : nat) (S : {set 'K_n}) : S \in cliques [set: 'K_n].
Proof. by rewrite in_cliquesT; apply/cliqueP => x y _ _. Qed.

Example Kn_all (n : nat) : all_clique_count 'K_n = 2 ^ n.
Proof.
have -> : all_clique_count 'K_n = #|powerset [set: 'K_n]|.
  by apply: eq_card => S; rewrite Kn_cliques powersetE subsetT.
by rewrite card_powerset cardsT card_ord.
Qed.

Example Kn_nonempty (n : nat) : nonempty_clique_count 'K_n = (2 ^ n).-1.
Proof. by rewrite -(Kn_all n) -nonempty_clique_countS. Qed.

Example Kn_size (n r : nat) : clique_count_size 'K_n r = 'C(n, r).
Proof.
have -> : clique_count_size 'K_n r = #|[set S : {set 'K_n} | #|S| == r]|.
  by apply: eq_card => S; rewrite inE Kn_cliques inE.
by rewrite card_draws card_ord.
Qed.

(** An edgeless graph on [n] vertices: its cliques are exactly the sets of at most one vertex. *)
Definition edgeless (n : nat) : sgraph :=
  @SGraph 'I_n (fun _ _ => false) (fun _ _ => erefl) (fun _ => erefl).

Lemma edgeless_cliqueb (n : nat) (S : {set edgeless n}) : cliqueb S = (#|S| <= 1).
Proof.
apply/cliqueP/idP => [cl|S1]; last exact: small_clique.
rewrite leqNgt; apply/negP => /card_gt1P[x [y [xS yS xy]]].
by have := cl x y xS yS xy.
Qed.

Example edgeless_nonempty (n : nat) : nonempty_clique_count (edgeless n) = n.
Proof.
rewrite -[RHS]card_ord -(clique_count_size1 (edgeless n)); apply: eq_card => S.
by rewrite !inE subsetT edgeless_cliqueb -card_gt0; case: #|S| => [|[|]].
Qed.

Example edgeless_size2 (n : nat) : clique_count_size (edgeless n) 2 = 0.
Proof.
apply/eqP; rewrite cards_eq0; apply/eqP/setP => S.
by rewrite !inE subsetT edgeless_cliqueb; case: #|S| => [|[|[|]]].
Qed.

(** The corners. *)
Example K0_counts :
  [/\ all_clique_count 'K_0 = 1, nonempty_clique_count 'K_0 = 0 & clique_count_size 'K_0 0 = 1].
Proof. by rewrite Kn_all Kn_nonempty clique_count_size0. Qed.

Example K1_counts : all_clique_count 'K_1 = 2 /\ nonempty_clique_count 'K_1 = 1.
Proof. by rewrite Kn_all Kn_nonempty. Qed.

Example K2_counts :
  [/\ all_clique_count 'K_2 = 4, nonempty_clique_count 'K_2 = 3 & clique_count_size 'K_2 2 = 1].
Proof. by rewrite Kn_all Kn_nonempty Kn_size. Qed.

Example K3_triangles : clique_count_size 'K_3 3 = 1.
Proof. by rewrite Kn_size. Qed.

Example two_isolated_vertices :
  [/\ all_clique_count (edgeless 2) = 3, nonempty_clique_count (edgeless 2) = 2
    & clique_count_size (edgeless 2) 2 = 0].
Proof. by rewrite -nonempty_clique_countS edgeless_nonempty edgeless_size2. Qed.

Print Assumptions Kn_all.
Print Assumptions Kn_size.
Print Assumptions two_isolated_vertices.
