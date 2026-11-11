(** * Minor.conjectures.grounding_X296 -- grounding certificates for wave X296 (2026-11-06)

    For the one row (the Lescure-Meyniel conjecture): hyp_inhabited (the row's instance holds at every complete
    graph, and the statement gives it there) and not_trivially_true (the variant with K_(k + 1) for K_k implies the
    statement and is false).  X296 has no helper, so no helper_sanity.
    - an immersion of K_m restricts to one of K_t for t <= m (g296_immersion_K_le), every graph immerses itself
      (g296_immersion_refl) and K_0 (g296_immersion_K0);
    - hyp: K_n immerses K_(chi(K_n)), since chi(K_n) <= n (coq-graph-theory's leq_chi);
    - ntt: no graph with no vertex immerses K_1, so "every graph immerses K_(chi(G) + 1)" fails at K_0;
    - g296_equiv_U7: the row is equivalent to U7's coloring_and_immersion_statement. *)

From GTBase Require Import base.
From Minor.conjectures Require Import U7 X296.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* An immersion of K_m gives one of K_t for t <= m: compose with the inclusion widen_ord of 'I_t into 'I_m. *)
Lemma g296_immersion_K_le (G : sgraph) (m t : nat) :
  t <= m -> immersion G 'K_m -> immersion G 'K_t.
Proof.
move=> le [f [P [finj [fP fdis]]]].
pose g : 'K_t -> 'K_m := fun i : 'I_t => widen_ord le i.
have ginj : injective g by move=> x y /(congr1 (@nat_of_ord m)) /= /ord_inj.
have gadj : forall u v : ('K_t), u -- v -> g u -- g v
  by move=> u v uv; rewrite /edge_rel /= (inj_eq ginj); exact: uv.
exists (f \o g), (fun u v => P (g u) (g v)).
split; first exact: inj_comp finj ginj.
split.
- move=> u v uv; exact: fP (gadj _ _ uv).
- move=> u1 v1 u2 v2 e1 e2 ne; apply: fdis; [exact: gadj | exact: gadj |].
  apply: contra ne => /eqP E; apply/eqP.
  apply: (imset_inj ginj); by rewrite !imsetU1 !imset_set1.
Qed.

(* Every graph immerses K_0 (no vertex, no edge). *)
Lemma g296_immersion_K0 (G : sgraph) : immersion G 'K_0.
Proof.
exists (fun i : 'I_0 => False_rect G (notF (ltn_ord i))), (fun _ _ => [::]).
by split; [case | split; case].
Qed.

(* Every graph immerses itself: the identity, and the one-edge walk [:: v] for each edge uv. *)
Lemma g296_immersion_refl (G : sgraph) : immersion G G.
Proof.
exists id, (fun _ v => [:: v]).
split; first by [].
split; first by move=> u v uv /=; rewrite uv.
move=> u1 v1 u2 v2 e1 e2 ne; rewrite /path_edges /seq_edge_set /=.
rewrite -setI_eq0; apply/eqP/setP => e; rewrite !inE.
by apply/negP => /andP [/eqP -> /eqP E]; rewrite E eqxx in ne.
Qed.

(* The row's instance at K_n: chi(K_n) <= n, and K_n immerses itself. *)
Lemma g296_LM_complete (n : nat) : immersion 'K_n 'K_(χ([set: 'K_n])).
Proof.
apply: (g296_immersion_K_le _ (g296_immersion_refl 'K_n)).
by have := leq_chi [set: 'K_n]; rewrite cardsT card_ord.
Qed.

(* ** hyp_inhabited: the instance holds at every complete graph, and the statement gives it there. *)
Definition g296_lm_hyp_claim : Prop :=
  (forall n : nat, immersion 'K_n 'K_(χ([set: 'K_n]))) /\
  (lescure_meyniel_weak_immersion_statement ->
   forall n : nat, immersion 'K_n 'K_(χ([set: 'K_n]))).

Theorem g296_lm_hyp_inhabited : g296_lm_hyp_claim.
Proof. by split=> [|S] n; [exact: g296_LM_complete | exact: S]. Qed.

(* ** not_trivially_true: K_(chi(G) + 1) for every graph implies the row and fails at K_0. *)
Definition g296_plus_one : Prop :=
  forall G : sgraph, immersion G 'K_(χ([set: G]).+1).

Definition g296_lm_ntt_claim : Prop :=
  ~ g296_plus_one /\ (g296_plus_one -> lescure_meyniel_weak_immersion_statement).

Theorem g296_lm_not_trivially_true : g296_lm_ntt_claim.
Proof.
split.
- move=> V; have [f _] := V 'K_0; by case: (f ord0).
- move=> V G; exact: g296_immersion_K_le (leqnSn _) (V G).
Qed.

(* The row and U7's coloring_and_immersion_statement are equivalent: a K_(chi(G)) immersion restricts to K_t for
   t <= chi(G); conversely U7 at t = chi(G) when chi(G) > 0, and K_0 when chi(G) = 0. *)
Theorem g296_equiv_U7 :
  lescure_meyniel_weak_immersion_statement <-> coloring_and_immersion_statement.
Proof.
split.
- move=> LM t G _ le; exact: g296_immersion_K_le le (LM G).
- move=> CI G; case: (posnP χ([set: G])) => [->|pos]; first exact: g296_immersion_K0.
  exact: CI.
Qed.
