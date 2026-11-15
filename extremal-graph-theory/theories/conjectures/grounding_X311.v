(** * Extremal.conjectures.grounding_X311 -- grounding certificates of wave X311.

    hyp_inhabited and not_trivially_true for the one row (the not_trivially_true claim in X299's form: a variant that
    implies the row and is false); the wave adds no helper, so there is no helper_sanity.
    - [g311_family G k s t F]: the row's conclusion at one graph G for k, tau = s / t and the family F (the body of
      the statement after its quantifiers).
    - Hypotheses: the complete graph K_3 has independence number 1 ([g311_K3_alpha]), so alpha = 1/3 (p = 1, q = 3,
      2 < 3) is met by it; the family {V(K_3)} with k = 3 and tau = 1 satisfies (1)-(3) (every maximum independent set
      is a single vertex, which V(K_3) contains), and the statement gives the conclusion at K_3 too.
    - Without k free (the variant at k = 1: every A_i a single vertex lying in every maximum independent set) the row
      fails at K_3: every vertex x misses the maximum independent set {u} of another vertex u, so the family is
      empty and (2) fails; the variant implies the row (k := 1). *)

From mathcomp Require Import all_boot.
From GraphTheory Require Import preliminaries digraph sgraph.
From GTBase Require Import base common.
From Extremal.conjectures Require Import X311.
From mathcomp Require Import zify.
From Stdlib Require Import Lia.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** The row's conclusion at one graph. *)
Definition g311_family (G : sgraph) (k s t : nat) (F : {set {set G}}) : Prop :=
  [/\ {in F &, forall A B : {set G}, A != B -> [disjoint A & B]},
      {in F, forall A : {set G}, #|A| = k},
      s * #|G| <= t * #|cover F| &
      forall S : {set G}, stable S -> #|S| = α([set: G]) ->
        {in F, forall A : {set G}, ~~ [disjoint S & A]}].

(** ** K_3: independence number 1 *)

Lemma g311_Kn_stable (N : nat) (S : {set 'K_N}) : stable S -> #|S| <= 1.
Proof.
move/stableP => st; apply/card_le1_eqP => x y xS yS; apply/eqP/negPn/negP => xy.
by move: (st x y xS yS); rewrite /edge_rel /= eq_sym xy.
Qed.

Lemma g311_K3_alpha : α([set: 'K_3]) = 1.
Proof.
apply/eqP; rewrite eqn_leq; apply/andP; split.
  by rewrite /alpha_mem; apply/bigmax_leqP => S /stabsetsP [_ st]; exact: g311_Kn_stable.
have [x _] : exists (x : 'K_3), x \in [set: 'K_3] by apply/card_gt0P; rewrite cardsT card_ord.
apply: (@leq_trans #|[set x]|); first by rewrite cards1.
apply: stabset_bound; apply/stabsetsP; split; first exact: subsetT.
by apply/stableP => a b /set1P -> /set1P ->; rewrite sg_irrefl.
Qed.

Lemma g311_K3_ratio : 3 * α([set: 'K_3]) = 1 * #|'K_3|.
Proof. by rewrite g311_K3_alpha card_ord. Qed.

(** ** hyp_inhabited *)

Lemma g311_K3_family : g311_family 3 1 1 [set [set: 'K_3]].
Proof.
split.
- by move=> A B /set1P -> /set1P ->; rewrite eqxx.
- by move=> A /set1P ->; rewrite cardsT card_ord.
- by rewrite /cover big_set1 cardsT card_ord.
- move=> S _ cS A /set1P ->.
  have [x xS] : exists x, x \in S by apply/card_gt0P; rewrite cS g311_K3_alpha.
  by apply/negP => /disjointP dis; exact: (dis x xS (in_setT x)).
Qed.

(** hyp_inhabited: alpha = 1/3 is in (0, 1/2), K_3 meets the hypothesis, the family {V(K_3)} witnesses the
    conclusion, and the statement gives a conclusion at K_3. *)
Definition g311_hyp_claim : Prop :=
  [/\ 0 < 1 /\ 2 * 1 < 3, 3 * α([set: 'K_3]) = 1 * #|'K_3|,
      exists F : {set {set 'K_3}}, g311_family 3 1 1 F &
      (friedgut_kalai_kindler_maximum_independent_set_hitting_statement ->
         exists k s t : nat, [/\ 0 < k, 0 < s, 0 < t & exists F : {set {set 'K_3}}, g311_family k s t F])].

Theorem g311_hyp_inhabited : g311_hyp_claim.
Proof.
split; [by [] | exact: g311_K3_ratio | by exists [set [set: 'K_3]]; exact: g311_K3_family |].
move=> h; have [k [s [t [k0 s0 t0 hG]]]] := h 1 3 isT isT.
by exists k, s, t; split=> //; exact: hG _ g311_K3_ratio.
Qed.

(** ** not_trivially_true: the variant at k = 1 is false at K_3 and implies the row *)

Definition g311_at_k1 : Prop :=
  forall p q : nat, 0 < p -> 2 * p < q ->
    exists s t : nat, [/\ 0 < s, 0 < t &
      forall G : sgraph, q * α([set: G]) = p * #|G| -> exists F : {set {set G}}, g311_family 1 s t F].

Definition g311_ntt_claim : Prop :=
  ~ g311_at_k1 /\ (g311_at_k1 -> friedgut_kalai_kindler_maximum_independent_set_hitting_statement).

Theorem g311_not_trivially_true : g311_ntt_claim.
Proof.
split; last first.
  move=> h p q p0 pq; have [s [t [s0 t0 hG]]] := h p q p0 pq.
  by exists 1, s, t; split=> // G e; exact: hG G e.
move=> h; have [s [t [s0 t0 hG]]] := h 1 3 isT isT.
have [F [_ cF cov hit]] := hG _ g311_K3_ratio.
have cv : cover F = set0.
  apply/eqP; rewrite -subset0; apply/subsetP; rewrite /cover => x /bigcupP [A AF xA].
  have [u] : exists u, u \in [set~ x] by apply/card_gt0P; rewrite cardsC1 card_ord.
  rewrite in_setC1 => ux.
  have su : stable [set u] by apply/stableP => a b /set1P -> /set1P ->; rewrite sg_irrefl.
  have cu : #|[set u]| = α([set: 'K_3]) by rewrite cards1 g311_K3_alpha.
  have dA : [disjoint [set u] & A].
    have [y Ay] : exists y, A = [set y] by apply/cards1P; rewrite (cF A AF).
    rewrite Ay; apply/disjointP => z /set1P -> /set1P uy.
    by move: xA; rewrite Ay => /set1P xy; rewrite uy -xy eqxx in ux.
  by have := hit _ su cu A AF; rewrite dA.
move: cov s0; rewrite cv cards0 muln0 card_ord; lia.
Qed.
