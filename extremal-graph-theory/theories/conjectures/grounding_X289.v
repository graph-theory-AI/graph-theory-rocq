(** * Extremal.conjectures.grounding_X289 -- grounding certificates of wave X289.

    hyp_inhabited and not_trivially_true for the three rows (the wave has no helper).  Every witness is K_5, through
    applications/kiraly_four_regular_disproof.v: it is 4-regular, has 10 edges and at least 37 cycles.
    - O(1.4^m): the bound applies to K_5 and forces a constant C > 1; with C = 1 it fails at K_5
      (7^10 = 49^5 < 50^5 = 32 * 5^10 <= 37 * 5^10), and that variant implies the row.
    - 1.99^(m/2) for 4-regular graphs: K_5 meets the hypothesis, and the row then bounds its count; without
      "4-regular" the variant fails at K_5 (the row itself fails there, kiraly_four_regular_cycle_count_disproved)
      and implies the row.
    - O(kappa_1^m): (p, r) = (3, 2) meets 0 < r and 2 r^2 <= p^2, and the row then bounds c(G)^5 by C (5/1)^m; with
      C = 1 the variant fails at K_5 for (3, 2) (10^10 = 100^5 < 148^5 = 37^5 * 2^10), and implies the row.
    No goal mentioning a cycle count of a concrete graph is closed by computation: the counts enter only through
    [kiraly_k5_cycle_count]. *)

From mathcomp Require Import all_boot.
From GraphTheory Require Import preliminaries digraph sgraph.
From GTBase Require Import base.
From Extremal.foundations Require Import edge_cycles.
From Extremal.conjectures Require Import X289.
From Extremal.applications Require Import kiraly_four_regular_disproof.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Arithmetic at K_5 (m = 10), symbolic: numerals stay below 200 *)

Lemma g289_seven_ten : 7 ^ 10 < 37 * 5 ^ 10.
Proof.
apply: (@leq_trans (32 * 5 ^ 10)); last exact: (leq_mul (isT : 32 <= 37) (leqnn _)).
have -> : 7 ^ 10 = (7 ^ 2) ^ 5 by rewrite -expnM.
have -> : 5 ^ 10 = (5 ^ 2) ^ 5 by rewrite -expnM.
rewrite -[32]/(2 ^ 5) -expnMn.
by rewrite ltn_exp2r.
Qed.

Lemma g289_ten_ten : 10 ^ 10 < 37 ^ 5 * 2 ^ 10.
Proof.
have -> : 10 ^ 10 = (10 ^ 2) ^ 5 by rewrite -expnM.
have -> : 2 ^ 10 = (2 ^ 2) ^ 5 by rewrite -expnM.
by rewrite -expnMn ltn_exp2r.
Qed.

(** ** Row studies:std_kir_ly_s_cycle_count_conjecture *)

Definition g289_k14_hyp_claim : Prop :=
  [/\ 37 <= edge_family_cycle_count ('K_5), #|E('K_5)| = 10 &
      (kiraly_cycle_count_one_point_four_statement ->
         exists2 C : nat, 1 < C & forall G : sgraph,
           edge_family_cycle_count G * 5 ^ #|E(G)| <= C * 7 ^ #|E(G)|)].

Theorem g289_k14_hyp_inhabited : g289_k14_hyp_claim.
Proof.
split; [exact: kiraly_k5_cycle_count | exact: kiraly_k5_edges |].
case=> C hC; exists C; last exact: hC.
rewrite ltnNge; apply/negP => C1.
move: (hC 'K_5); rewrite kiraly_k5_edges => h.
have h37 : 37 * 5 ^ 10 <= C * 7 ^ 10.
  exact: leq_trans (leq_mul kiraly_k5_cycle_count (leqnn _)) h.
have h1 : C * 7 ^ 10 <= 7 ^ 10.
  rewrite -[X in _ <= X]mul1n; exact: leq_mul C1 (leqnn _).
by move: (leq_trans h37 h1); rewrite leqNgt g289_seven_ten.
Qed.

Definition g289_k14_unit_constant : Prop :=
  forall G : sgraph, edge_family_cycle_count G * 5 ^ #|E(G)| <= 7 ^ #|E(G)|.

Definition g289_k14_ntt_claim : Prop :=
  ~ g289_k14_unit_constant /\ (g289_k14_unit_constant -> kiraly_cycle_count_one_point_four_statement).

Theorem g289_k14_not_trivially_true : g289_k14_ntt_claim.
Proof.
split; last by move=> h; exists 1; move=> G; rewrite mul1n; exact: h.
move=> h; move: (h 'K_5); rewrite kiraly_k5_edges => h1.
have h37 := leq_trans (leq_mul kiraly_k5_cycle_count (leqnn (5 ^ 10))) h1.
by move: h37; rewrite leqNgt g289_seven_ten.
Qed.

(** ** Row studies:std_kir_ly_s_cycle_count_conjecture_for_4_regular_gr *)

Definition g289_k4r_hyp_claim : Prop :=
  [/\ regular 'K_5 4, 37 <= edge_family_cycle_count ('K_5) &
      (kiraly_four_regular_cycle_count_statement ->
         edge_family_cycle_count 'K_5 ^ 2 * 100 ^ 10 <= 199 ^ 10)].

Theorem g289_k4r_hyp_inhabited : g289_k4r_hyp_claim.
Proof.
split; [exact: kiraly_k5_regular | exact: kiraly_k5_cycle_count |].
move=> h; move: (h 'K_5 kiraly_k5_regular); rewrite kiraly_k5_edges => h1; exact: h1.
Qed.

Definition g289_k4r_any_graph : Prop :=
  forall G : sgraph, edge_family_cycle_count G ^ 2 * 100 ^ #|E(G)| <= 199 ^ #|E(G)|.

Definition g289_k4r_ntt_claim : Prop :=
  ~ g289_k4r_any_graph /\ (g289_k4r_any_graph -> kiraly_four_regular_cycle_count_statement).

Theorem g289_k4r_not_trivially_true : g289_k4r_ntt_claim.
Proof.
split; last by move=> h G _; exact: h.
by move=> h; apply: kiraly_four_regular_cycle_count_disproved => G _; exact: h.
Qed.

(** ** Row arxiv:1907.12091#00 *)

Definition g289_kappa_hyp_claim : Prop :=
  [/\ 0 < 2, 2 * 2 ^ 2 <= 3 ^ 2 &
      (cycle_count_kappa_one_statement ->
         exists C : nat, forall G : sgraph,
           edge_family_cycle_count G ^ 5 * 2 ^ #|E(G)| <= C * 10 ^ #|E(G)|)].

Theorem g289_kappa_hyp_inhabited : g289_kappa_hyp_claim.
Proof.
split; [by [] | by [] |].
case=> C h; exists C; move=> G.
exact: (h G 3 2 isT isT).
Qed.

Definition g289_kappa_unit_constant : Prop :=
  forall (G : sgraph) (p r : nat), 0 < r -> 2 * r ^ 2 <= p ^ 2 ->
    edge_family_cycle_count G ^ 5 * r ^ #|E(G)| <= (2 * r + 2 * p) ^ #|E(G)|.

Definition g289_kappa_ntt_claim : Prop :=
  ~ g289_kappa_unit_constant /\ (g289_kappa_unit_constant -> cycle_count_kappa_one_statement).

Theorem g289_kappa_not_trivially_true : g289_kappa_ntt_claim.
Proof.
split; last by move=> h; exists 1; move=> G p r r0 pr; rewrite mul1n; exact: h.
move=> h.
have h1 : edge_family_cycle_count 'K_5 ^ 5 * 2 ^ 10 <= 10 ^ 10.
  move: (h 'K_5 3 2 isT isT); rewrite kiraly_k5_edges => h1; exact: h1.
have c5 := @kiraly_leq_pow 37 (edge_family_cycle_count 'K_5) 5 kiraly_k5_cycle_count.
by move: (leq_trans (leq_mul c5 (leqnn (2 ^ 10))) h1); rewrite leqNgt g289_ten_ten.
Qed.
