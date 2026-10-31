(** * Minor.conjectures.grounding_X271 -- grounding certificates for wave X271 (2026-10-31)

    For each of the four rows: hyp_inhabited (the body's conditions hold together at a small instance, and the
    statement gives its consequence), not_trivially_true (a variant without one hypothesis is false and implies
    the statement), and helper_sanity for the one local helper of X271.v.
    - odd Hadwiger, chromatic form: chi(K_3) = 3 and K_3 has an odd K_3 minor (singleton branch sets, one colour).
      Without "t <= chi(G)" the row is false: K_1 has no odd K_2 minor (two disjoint nonempty branch sets need two
      vertices).  The instances t <= 1 hold outright (g271_ohc_small).
    - odd Hadwiger, colouring form: at t = 2, K_1 has no odd K_2 minor and the statement gives chi(K_1) <= 1.
      Without "no odd K_t minor" the row is false at t = 2 and G = K_2 (chi = 2).
    - H-Hadwiger: K_1 has no K_2 minor and the statement gives chi(K_1) <= 1.  Without "no H minor" the row is
      false at G = H = K_2 (chi = 2 > 1).
    - Hajos at five: chi(K_5) = 5 and K_5 contains a subdivision of itself.  Without "chi(G) = 5" the row is false
      at K_1 (a subdivision of K_5 has five distinct branch vertices). *)

From GTBase Require Import base.
From GraphTheory Require Import minor.
From Minor.foundations Require Import containment.
From Minor.conjectures Require Import X271.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Complete graphs ******************************************************* *)

Definition g271_o1 : 'I_2 := @Ordinal 2 1 isT.

(** The chromatic number of K_n is n. *)
Lemma g271_chi_Kn (n : nat) : χ([set: 'K_n]) = n.
Proof. by rewrite (chi_clique (@Kn_clique n)) cardsT card_ord. Qed.

(** K_n has an odd K_n minor: singleton branch sets, every vertex coloured alike. *)
Lemma g271_Kn_odd (n : nat) : x271_odd_minor_tree_model 'K_n 'K_n.
Proof.
exists (fun x => [set x]), (fun _ => true); split.
- by move=> x; apply/set0Pn; exists x; rewrite inE.
- by move=> x u v; rewrite !inE => /eqP -> /eqP ->; exact: connect0.
- by move=> x y xy; rewrite disjoints1 in_set1 (negbTE xy).
- by move=> x y xy; exists x, y; rewrite !inE !eqxx.
Qed.

(** K_1 has no odd K_2 minor: its one vertex cannot lie in two disjoint nonempty branch sets. *)
Lemma g271_K1_no_odd_K2 : ~ x271_odd_minor_tree_model 'K_1 'K_2.
Proof.
case=> B [sigma [ne _ dis _]].
have [u uB0] := set0Pn _ (ne ord0).
have [v vB1] := set0Pn _ (ne g271_o1).
have uv : u = v by rewrite (ord1 u) (ord1 v).
move: (dis ord0 g271_o1 isT); rewrite disjoint_subset => /subsetP/(_ u uB0).
by rewrite inE uv vB1.
Qed.

(** ** studies:std_odd_hadwiger_conjecture ********************************** *)

(** hyp_inhabited: chi(K_3) = 3 >= 3, and the statement gives an odd K_3 minor of K_3. *)
Definition g271_ohc_hyp_claim : Prop :=
  3 <= χ([set: 'K_3]) /\
  (odd_hadwiger_chromatic_odd_minor_statement -> x271_odd_minor_tree_model 'K_3 'K_3).

Theorem g271_ohc_hyp_inhabited : g271_ohc_hyp_claim.
Proof.
have c3 : 3 <= χ([set: 'K_3]) by rewrite g271_chi_Kn.
by split=> // h; exact: h 3 'K_3 c3.
Qed.

(** not_trivially_true: without "t <= chi(G)" the statement is false (K_1 has no odd K_2 minor). *)
Definition g271_ohc_no_chi : Prop :=
  forall (t : nat) (G : sgraph), x271_odd_minor_tree_model G 'K_t.

Definition g271_ohc_ntt_claim : Prop :=
  ~ g271_ohc_no_chi /\ (g271_ohc_no_chi -> odd_hadwiger_chromatic_odd_minor_statement).

Theorem g271_ohc_not_trivially_true : g271_ohc_ntt_claim.
Proof.
split; first by move=> h; exact: g271_K1_no_odd_K2 (h 2 'K_1).
by move=> h t G _; exact: h.
Qed.

(** The instances t = 0 and t = 1 hold: no branch set, resp. one vertex as its own branch set. *)
Lemma g271_ohc_small (t : nat) (G : sgraph) :
  t <= 1 -> t <= χ([set: G]) -> x271_odd_minor_tree_model G 'K_t.
Proof.
case: t => [_ _|[|//] _ c1].
  by exists (fun _ => set0), (fun _ => true); split; case.
case: (set_0Vmem [set: G]) => [E0|[w _]]; first by move: c1; rewrite E0 chi0.
exists (fun _ => [set w]), (fun _ => true); split.
- by move=> x; apply/set0Pn; exists w; rewrite inE.
- by move=> x u v; rewrite !inE => /eqP -> /eqP ->; exact: connect0.
- by move=> x y; rewrite (ord1 x) (ord1 y) eqxx.
- by move=> x y; rewrite (ord1 x) (ord1 y) sg_irrefl.
Qed.

(** ** studies:std_odd_hadwiger_conjecture_411 ****************************** *)

(** hyp_inhabited: at t = 2, K_1 has no odd K_2 minor, and the statement gives chi(K_1) <= 1. *)
Definition g271_ohf_hyp_claim : Prop :=
  [/\ 2 <= 2, ~ x271_odd_minor_tree_model 'K_1 'K_2 &
      (odd_hadwiger_odd_minor_free_colourable_statement -> χ([set: 'K_1]) <= 1)].

Theorem g271_ohf_hyp_inhabited : g271_ohf_hyp_claim.
Proof.
split=> //; first exact: g271_K1_no_odd_K2.
by move=> h; exact: h 2 'K_1 isT g271_K1_no_odd_K2.
Qed.

(** not_trivially_true: without "no odd K_t minor" the statement is false at t = 2, G = K_2 (chi = 2). *)
Definition g271_ohf_no_free : Prop :=
  forall (t : nat) (G : sgraph), 2 <= t -> χ([set: G]) <= t.-1.

Definition g271_ohf_ntt_claim : Prop :=
  ~ g271_ohf_no_free /\ (g271_ohf_no_free -> odd_hadwiger_odd_minor_free_colourable_statement).

Theorem g271_ohf_not_trivially_true : g271_ohf_ntt_claim.
Proof.
split; first by move=> h; have := h 2 'K_2 isT; rewrite g271_chi_Kn.
by move=> h t G t2 _; exact: h.
Qed.

(** ** studies:std_h_hadwiger_conjecture ************************************ *)

(** K_1 has no K_2 minor (a minor has at most as many vertices as its host). *)
Lemma g271_K1_no_minor_K2 : ~ minor 'K_1 'K_2.
Proof. by move/minor_card; rewrite !card_ord. Qed.

(** hyp_inhabited: K_1 has no K_2 minor, and the statement gives chi(K_1) <= v(K_2) - 1 = 1. *)
Definition g271_hh_hyp_claim : Prop :=
  ~ minor 'K_1 'K_2 /\ (h_hadwiger_minor_free_colourable_statement -> χ([set: 'K_1]) <= 1).

Theorem g271_hh_hyp_inhabited : g271_hh_hyp_claim.
Proof.
split; first exact: g271_K1_no_minor_K2.
by move=> h; have := h 'K_2 'K_1 g271_K1_no_minor_K2; rewrite card_ord.
Qed.

(** not_trivially_true: without "no H minor" the statement is false at G = H = K_2 (chi = 2 > 1). *)
Definition g271_hh_no_free : Prop :=
  forall H G : sgraph, χ([set: G]) <= #|H|.-1.

Definition g271_hh_ntt_claim : Prop :=
  ~ g271_hh_no_free /\ (g271_hh_no_free -> h_hadwiger_minor_free_colourable_statement).

Theorem g271_hh_not_trivially_true : g271_hh_ntt_claim.
Proof.
split; first by move=> h; have := h 'K_2 'K_2; rewrite g271_chi_Kn card_ord.
by move=> h H G _; exact: h.
Qed.

(** ** studies:std_haj_s_conjecture_k_5 ************************************* *)

(** hyp_inhabited: chi(K_5) = 5, and the statement gives a subdivision of K_5 in K_5. *)
Definition g271_hj_hyp_claim : Prop :=
  χ([set: 'K_5]) = 5 /\ (hajos_k5_subdivision_statement -> has_subdivision 'K_5 'K_5).

Theorem g271_hj_hyp_inhabited : g271_hj_hyp_claim.
Proof.
split; first exact: g271_chi_Kn.
by move=> h; exact: h 'K_5 (g271_chi_Kn 5).
Qed.

(** not_trivially_true: without "chi(G) = 5" the statement is false at K_1 (five distinct branch vertices). *)
Definition g271_hj_no_chi : Prop :=
  forall G : sgraph, has_subdivision G 'K_5.

Definition g271_hj_ntt_claim : Prop :=
  ~ g271_hj_no_chi /\ (g271_hj_no_chi -> hajos_k5_subdivision_statement).

Theorem g271_hj_not_trivially_true : g271_hj_ntt_claim.
Proof.
split; first by move=> h; move: (has_subdivision_card (h 'K_1)); rewrite !card_ord.
by move=> h G _; exact: h.
Qed.

(** ** helper_sanity ********************************************************* *)

(** [x271_odd_minor_tree_model]: K_3 has an odd K_3 minor, K_1 has no odd K_2 minor. *)
Definition g271_om_helper_claim : Prop :=
  x271_odd_minor_tree_model 'K_3 'K_3 /\ ~ x271_odd_minor_tree_model 'K_1 'K_2.

Theorem g271_om_helper_sanity : g271_om_helper_claim.
Proof. by split; [exact: g271_Kn_odd | exact: g271_K1_no_odd_K2]. Qed.
