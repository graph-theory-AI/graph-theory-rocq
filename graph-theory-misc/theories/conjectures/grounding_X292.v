(** * GTMisc.conjectures.grounding_X292 -- grounding lemmas for wave X292.

    Qed-closed, axiom-free certificates for the row of [X292.v] (hyp_inhabited, not_trivially_true; X292 declares
    no helper, so no helper_sanity).  The witness is K_4: it is planar under [wagner_planar] (no minor has more
    vertices than its host, GTBase [minor_card]) and wins the hat guessing game with 4 colours by the sum rule over
    'Z_4 (each vertex guesses its own name minus the sum of the others' hats; on K_4 every other vertex is a
    neighbour, so the rule is local).  [g292_K0_never_wins] records that the graph with no vertex wins with no
    number of colours.  They validate the statement; they do not prove it (it is false, arXiv:2107.05995v2
    l.104-107). *)

From mathcomp Require Import all_boot all_algebra.
From GraphTheory Require Import preliminaries digraph sgraph minor.
From GTBase Require Import base.
From GTMisc.conjectures Require Import X99 X292.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.

(* K_4 is planar: a minor never has more vertices than its host (minor_card), and 4 < 5, 4 < 6. *)
Lemma g292_K4_planar : wagner_planar 'K_4.
Proof.
split.
- move/minor_card; rewrite !card_ord; by [].
- move/minor_card; rewrite card_ord card_sum !card_ord; by [].
Qed.

(* The sum rule on K_4 with 4 colours, in 'Z_4 (= 'I_4): vertex v guesses v minus the others' hats. *)
Definition g292_K4_guess : x99_hat_strategy 'K_4 4 :=
  fun v hats => ((v : 'Z_4) - \sum_(u | u != v) (hats u : 'Z_4))%R.

Lemma g292_K4_local : x99_local_strategy g292_K4_guess.
Proof.
move=> v a b eq_ab; rewrite /g292_K4_guess; congr (_ - _)%R.
by apply: eq_bigr => u uv; rewrite eq_ab // /edge_rel /= eq_sym.
Qed.

Lemma g292_K4_wins : x99_winning_hat_strategy 'K_4 4.
Proof.
exists g292_K4_guess; split; first exact: g292_K4_local.
move=> hats; apply/existsP.
pose s : 'Z_4 := (\sum_(u : 'K_4) (hats u : 'Z_4))%R.
exists (s : 'K_4); apply/eqP; rewrite /g292_K4_guess /s.
rewrite [X in (X - _)%R](bigD1 (\sum_u (hats u : 'Z_4))%R) //=.
by rewrite addrK.
Qed.

Definition g292_phg_hyp_claim : Prop :=
  [/\ wagner_planar ('K_4), x99_winning_hat_strategy ('K_4) 4 &
      (planar_hat_guessing_max_four_statement -> x99_hat_guessing_number_at_most 'K_4 4)].

Theorem g292_phg_hyp_inhabited : g292_phg_hyp_claim.
Proof.
split; [exact: g292_K4_planar | exact: g292_K4_wins |].
by case=> h _; exact: h _ g292_K4_planar.
Qed.

Definition g292_phg_bound_three : Prop :=
  (forall G : sgraph, wagner_planar G -> x99_hat_guessing_number_at_most G 3) /\
  (exists G : sgraph, wagner_planar G /\ x99_winning_hat_strategy G 3).

Definition g292_phg_ntt_claim : Prop :=
  ~ g292_phg_bound_three /\ (g292_phg_bound_three -> planar_hat_guessing_max_four_statement).

Theorem g292_phg_not_trivially_true : g292_phg_ntt_claim.
Proof.
split.
- by case=> h _; exact: (h _ g292_K4_planar 4 isT g292_K4_wins).
- case=> h _; split; last by exists 'K_4; split; [exact: g292_K4_planar | exact: g292_K4_wins].
  by move=> G pG q lt4q; apply: h pG q (ltnW lt4q).
Qed.

(* The graph with no vertex wins with no number of colours (so it is never an attainment witness). *)
Lemma g292_K0_never_wins (q : nat) : ~ x99_winning_hat_strategy 'K_0 q.
Proof.
case=> guess [_ win].
pose hats : ('K_0) -> 'I_q :=
  fun v => let: @Ordinal _ m h := v in False_rect _ (Bool.diff_true_false (etrans (esym h) (ltn0 m))).
by case/existsP: (win hats) => -[m h].
Qed.
