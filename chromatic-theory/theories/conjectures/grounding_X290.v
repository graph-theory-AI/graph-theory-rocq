(** * Chromatic.conjectures.grounding_X290 -- grounding certificates of wave X290.

    hyp_inhabited and not_trivially_true for the one row (the wave declares no helper; it reuses X218's).
    - Hypotheses: K_2 has connected tree-depth exactly 2 (K_2 - r is one vertex, of tree-depth 1; no graph with a
      vertex has tree-depth 0), and the row then bounds the defective chromatic number of the K_2-minor-free class
      by 1.
    - Without "~ ctd(H) <= k - 1" (only an upper bound on the connected tree-depth), the variant is false at H = K_1,
      k = 2: K_1 has connected tree-depth at most 2, and the variant would deny the bound 0 for the K_1-minor-free
      class, which holds only the graph with no vertex (every graph with a vertex has K_1 as a minor) and is
      0-colourable; the variant implies the row. *)

From mathcomp Require Import all_boot.
From GraphTheory Require Import preliminaries digraph sgraph minor.
From GTBase Require Import base.
From Chromatic.conjectures Require Import X194 X218 X290.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* A graph with at most one vertex has tree-depth at most 1 (no two distinct vertices). *)
Lemma g290_td_le1 (G : sgraph) : #|G| <= 1 -> x194_treedepth_at_most G 1.
Proof.
move=> small; exists (fun _ => ord0) => x y p xy.
by move: xy; rewrite (card_le1_eqP small x y) ?inE // eqxx.
Qed.

(* A graph with a vertex has no ranking into 'I_0. *)
Lemma g290_td_not0 (G : sgraph) (v : G) : ~ x194_treedepth_at_most G 0.
Proof. by case=> rank _; case: (rank v). Qed.

Lemma g290_K2_ctd2 : x218_ctd_at_most ('K_2) 2.
Proof.
split=> //; exists ord0; apply: g290_td_le1.
by rewrite card_sig cardsC1 card_ord.
Qed.

Lemma g290_K2_not_ctd1 : ~ x218_ctd_at_most ('K_2) 1.
Proof.
case=> _ [r]; have [v vr] : exists v : ('K_2), v != r.
  by exists (if r == ord0 then ord_max else ord0); case: (r) => -[|[|]] //= _; rewrite /eq_op /=.
have vin : v \in ~: [set r] by rewrite !inE.
exact: (g290_td_not0 (Sub v vin : induced (~: [set r]))).
Qed.

Lemma g290_K1_ctd2 : x218_ctd_at_most ('K_1) 2.
Proof.
split=> //; exists ord0; apply: g290_td_le1.
by rewrite card_sig cardsC1 card_ord.
Qed.

(* A graph with a vertex has ('K_1) as a minor: one vertex as the only bag. *)
Lemma g290_minor_K1 (G : sgraph) (v : G) : minor G ('K_1).
Proof.
exists (fun x => if x == v then Some ord0 else None); split.
- by move=> y; exists v; rewrite eqxx (ord1 y).
- move=> y; have -> : (fun x : G => if x == v then Some ord0 else None) @^-1 Some y = [set v].
    by apply/setP => x; rewrite !inE (ord1 y); case: (x == v).
  exact: connected1.
- by move=> x y; rewrite (ord1 x) (ord1 y) sgP.
Qed.

(* The ('K_1)-minor-free class (only the graph with no vertex) has defective chromatic number 0. *)
Lemma g290_K1_free_class_le0 : x218_defective_chromatic_class_le (fun G : sgraph => ~ minor G 'K_1) 0.
Proof.
exists 0 => G noK1.
have emp : forall v : G, False by move=> v; apply: noK1; exact: g290_minor_K1 v.
by exists (fun v => False_rect _ (emp v)) => v; case: (emp v).
Qed.

Definition g290_oow_hyp_claim : Prop :=
  [/\ x218_ctd_at_most ('K_2) 2, ~ x218_ctd_at_most ('K_2) 1 &
      (ossona_de_mendez_oum_wood_defective_minor_statement ->
         x218_defective_chromatic_class_le (fun G : sgraph => ~ minor G 'K_2) 1)].

Theorem g290_oow_hyp_inhabited : g290_oow_hyp_claim.
Proof.
split; [exact: g290_K2_ctd2 | exact: g290_K2_not_ctd1 |].
by move=> h; case: (h ('K_2) 2 g290_K2_ctd2 g290_K2_not_ctd1).
Qed.

Definition g290_oow_upper_ctd_only : Prop :=
  forall (H : sgraph) (k : nat),
    x218_ctd_at_most H k ->
    x218_defective_chromatic_class_le (fun G : sgraph => ~ minor G H) (k - 1) /\
    (forall j : nat, j.+1 < k -> ~ x218_defective_chromatic_class_le (fun G : sgraph => ~ minor G H) j).

Definition g290_oow_ntt_claim : Prop :=
  ~ g290_oow_upper_ctd_only /\ (g290_oow_upper_ctd_only -> ossona_de_mendez_oum_wood_defective_minor_statement).

Theorem g290_oow_not_trivially_true : g290_oow_ntt_claim.
Proof.
split; last by move=> h H k hk _; exact: h.
move=> h; case: (h ('K_1) 2 g290_K1_ctd2) => _ low.
exact: (low 0 isT g290_K1_free_class_le0).
Qed.
