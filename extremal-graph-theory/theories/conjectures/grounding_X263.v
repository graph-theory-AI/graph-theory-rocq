(** * Extremal.conjectures.grounding_X263 -- grounding certificates of wave X263.

    For each of the two rows: hyp_inhabited (the hypotheses hold on a concrete instance, and the statement then
    yields its conclusion there or on the class) and not_trivially_true in the contract form of
    meta/EXPANSION_PLAN.md 4.4 (a variant obtained from the body by deleting one hypothesis is false and implies the
    row): erdos:777 without the second clause's density hypothesis m^2 <= p * edges (all 2^K subsets of [K] break
    m^2 <= K 2^n); erdos:1031 without its hypothesis on cliques and stable sets (K_N has no non-trivial regular induced
    subgraph: every induced subgraph of a complete graph is complete).  The concrete instances: the chain
    {set0, {0}} on [1] (2 members, 1 comparable pair, so m^2 <= 4 * edges), and K_32,32 on 64 = 2^6 vertices, where
    every set of at least 10 log_2 64 = 60 vertices meets both sides twice, so it is neither a clique nor stable, the
    whole vertex set meets the threshold (the hypothesis is not vacuous there), and G[V] is 32-regular, non-trivial,
    with log_2 64 <= 64.  The threshold first bites at n = 59 (the least n >= 2 with n^10 <= 2^n); for
    2 <= n <= 58 the hypothesis holds vacuously and K_n refutes the clause, so N is load-bearing (X263.v Notes).
    helper_sanity (x263_comparable_pairs): the chain {set0, {0}} has 1 pair (one per unordered comparable pair), the
    antichain {{0}, {1}} on [2] has 0, and every family has at most m^2 pairs. *)

From Extremal.conjectures Require Import X263.
From GTBase Require Import base common.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Comparable pairs: a 2-chain and an antichain ****************************** *)

Local Notation e0 := (@Ordinal 1 0 isT).
Local Notation a0 := (@Ordinal 2 0 isT).
Local Notation a1 := (@Ordinal 2 1 isT).

Definition g263_chain : {set {set 'I_1}} := [set set0; [set e0]].

Lemma g263_set0_neq1 : (set0 : {set 'I_1}) != [set e0].
Proof. by apply/eqP => /setP /(_ e0); rewrite !inE eqxx. Qed.

Lemma g263_chain_card : #|g263_chain| = 2.
Proof. by rewrite cards2 g263_set0_neq1. Qed.

Lemma g263_chain_pairs : x263_comparable_pairs g263_chain = 1.
Proof.
rewrite /x263_comparable_pairs (_ : [set p | _] = [set (set0, [set e0])]) ?cards1 //.
apply/setP => [[A B]]; rewrite in_set in_set1 /=; apply/idP/idP.
- case/and3P => /set2P [] -> /set2P [] -> //; rewrite ?properxx //.
  by rewrite properE sub0set andbF.
- case/eqP => -> ->; rewrite /g263_chain !in_set2 !eqxx ?orbT /= proper0.
  by apply/set0Pn; exists e0; rewrite inE.
Qed.

Lemma g263_singleton_proper (i j : 'I_2) : i != j -> ([set i] \proper [set j]) = false.
Proof. by move=> ij; rewrite properE sub1set in_set1 (negbTE ij). Qed.

Definition g263_antichain : {set {set 'I_2}} := [set [set a0]; [set a1]].

Lemma g263_antichain_pairs : x263_comparable_pairs g263_antichain = 0.
Proof.
rewrite /x263_comparable_pairs (_ : [set p | _] = set0) ?cards0 //.
apply/setP => [[A B]]; rewrite in_set inE /= in_set0 !in_set1.
apply/negbTE; apply/and3P => [[/orP hA /set2P hB]].
by case: hA => /eqP ->; case: hB => ->; rewrite ?properxx ?g263_singleton_proper.
Qed.

Lemma g263_pairs_le (n : nat) (F : {set {set 'I_n}}) : x263_comparable_pairs F <= #|F| ^ 2.
Proof.
rewrite /x263_comparable_pairs expnS expn1 -cardsX; apply: subset_leq_card.
by apply/subsetP => [[A B]]; rewrite !inE /= => /and3P [-> -> _].
Qed.

Definition g263_cp_helper_claim : Prop :=
  [/\ x263_comparable_pairs g263_chain = 1, x263_comparable_pairs g263_antichain = 0 &
      forall (n : nat) (F : {set {set 'I_n}}), x263_comparable_pairs F <= #|F| ^ 2].

Theorem g263_cp_helper_sanity : g263_cp_helper_claim.
Proof. by split; [exact: g263_chain_pairs | exact: g263_antichain_pairs | exact: g263_pairs_le]. Qed.

(** ** erdos:777 ********************************************************************** *)

Definition g263_cf_hyp_claim : Prop :=
  [/\ #|g263_chain| = 2, x263_comparable_pairs g263_chain = 1,
      #|g263_chain| ^ 2 <= 4 * x263_comparable_pairs g263_chain &
      (set_family_comparability_statement -> exists K : nat, #|g263_chain| ^ 2 <= K * 2 ^ 1)].

Theorem g263_cf_hyp_inhabited : g263_cf_hyp_claim.
Proof.
split; [exact: g263_chain_card | exact: g263_chain_pairs | by rewrite g263_chain_card g263_chain_pairs |].
case=> _ h _; have [K hK] := h 4 isT; exists K; apply: hK.
by rewrite g263_chain_card g263_chain_pairs.
Qed.

(** The second clause without its hypothesis on the number of comparable pairs. *)
Definition g263_cf_no_density : Prop :=
  [/\ (forall p : nat, 1 <= p -> exists N : nat, forall (n : nat) (F : {set {set 'I_n}}), N <= n ->
         p ^ 2 * #|F| ^ 2 <= (2 * p - 1) ^ 2 * 2 ^ n -> x263_comparable_pairs F < 2 ^ n),
      (forall p : nat, 1 <= p -> exists K : nat, forall (n : nat) (F : {set {set 'I_n}}),
         #|F| ^ 2 <= K * 2 ^ n) &
      (forall p : nat, 1 <= p -> exists q : nat, 1 <= q /\ forall (n : nat) (F : {set {set 'I_n}}),
         #|F| ^ (2 * q - 1) < x263_comparable_pairs F ^ q -> p ^ n * #|F| ^ 2 < (2 * p + 1) ^ n)].

Definition g263_cf_ntt_claim : Prop :=
  ~ g263_cf_no_density /\ (g263_cf_no_density -> set_family_comparability_statement).

Lemma g263_card_all_sets (n : nat) : #|[set: {set 'I_n}]| = 2 ^ n.
Proof. by rewrite -powersetT card_powerset cardsT card_ord. Qed.

Theorem g263_cf_not_trivially_true : g263_cf_ntt_claim.
Proof.
split.
- case=> _ h _; have [K hK] := h 1 isT; have := hK K [set: {set 'I_K}].
  rewrite g263_card_all_sets expnS expn1 leq_pmul2r ?expn_gt0 //.
  by rewrite leqNgt ltn_expl.
- case=> h1 h2 h3; split => // p hp; have [K hK] := h2 p hp; exists K => n F _; exact: hK.
Qed.

(** ** Induced subgraphs on all vertices, and K_32,32 ************************************ *)

Lemma g263_induced_setT_deg (G : sgraph) (v : induced [set: G]) : #|N(v)| = #|N(val v)|.
Proof.
rewrite -(card_imset _ val_inj); apply: eq_card => w; apply/imsetP/idP.
- by case=> u uv ->; move: uv; rewrite !inE.
- by rewrite !inE => vw; exists (Sub w (in_setT w)); rewrite ?inE.
Qed.

Lemma g263_regular_setT (G : sgraph) (d : nat) : regular G d -> regular (induced [set: G]) d.
Proof. by move=> h v; rewrite g263_induced_setT_deg. Qed.

Lemma g263_KB_deg (x : 'K_32,32) : #|N(x)| = 32.
Proof.
case: x => i.
- rewrite (_ : N(_) = [set (inr j : 'K_32,32) | j in [set: 'I_32]]).
    apply/setP => y; rewrite in_opn; case: y => j.
      by symmetry; apply/negbTE/imsetP => [[k _]].
    by symmetry; apply/imsetP; exists j.
  by rewrite (card_imset _ inr_inj) cardsT card_ord.
- rewrite (_ : N(_) = [set (inl j : 'K_32,32) | j in [set: 'I_32]]).
    apply/setP => y; rewrite in_opn; case: y => j.
      by symmetry; apply/imsetP; exists j.
    by symmetry; apply/negbTE/imsetP => [[k _]].
  by rewrite (card_imset _ inl_inj) cardsT card_ord.
Qed.

Lemma g263_KB_card : #|'K_32,32| = 64.
Proof. by rewrite card_sum !card_ord. Qed.

(** Every set of at least 60 vertices of K_32,32 meets both sides in two vertices. *)
Lemma g263_KB_hyp (S : {set 'K_32,32}) : #|'K_32,32| ^ 10 <= 2 ^ #|S| -> ~~ cliqueb S && ~~ stable S.
Proof.
rewrite g263_KB_card (_ : 64 = 2 ^ 6) // -expnM leq_exp2l // => hS.
pose L := [set x in S | is_inl x]; pose R := [set x in S | ~~ is_inl x].
have hLR : #|S| = #|L| + #|R|.
  by rewrite -(cardsID [set x | is_inl x] S) /L /R; congr (_ + _); apply: eq_card => x; rewrite !inE andbC.
have hL : #|L| <= 32.
  apply: (@leq_trans #|[set (inl j : 'K_32,32) | j in [set: 'I_32]]|).
    apply: subset_leq_card; apply/subsetP => x; rewrite inE.
    by case: x => j /andP [_ //] _; apply/imsetP; exists j.
  by rewrite (leq_trans (leq_imset_card _ _)) // cardsT card_ord.
have hR : #|R| <= 32.
  apply: (@leq_trans #|[set (inr j : 'K_32,32) | j in [set: 'I_32]]|).
    apply: subset_leq_card; apply/subsetP => x; rewrite inE.
    by case: x => j /andP [_ //] _; apply/imsetP; exists j.
  by rewrite (leq_trans (leq_imset_card _ _)) // cardsT card_ord.
have hL2 : 1 < #|L|.
  move: hS; rewrite hLR => hS; apply: contraLR hS; rewrite -!ltnNge => h.
  by rewrite (leq_trans (leq_add h hR)).
have hR1 : 0 < #|R|.
  move: hS; rewrite hLR lt0n => hS; apply/eqP => h; move: hS; rewrite h addn0 => hS.
  by have := leq_trans hS hL.
have [x [y [xL yL xy]]] : exists x y, [/\ x \in L, y \in L & x != y].
  by have /card_gt1P [x [y [xL yL xy]]] := hL2; exists x, y.
have [z zR] : exists z, z \in R by apply/card_gt0P.
move: xL yL zR; rewrite !inE => /andP [xS xl] /andP [yS yl] /andP [zS zl].
apply/andP; split.
- apply/negP => /cliqueP cl; have := cl x y xS yS xy.
  by case: x xy xS xl => // i; case: y yS yl => // j.
- apply/negP => /stableP st; have := st x z xS zS.
  by clear xy; case: x xS xl => // i; case: z zS zl => // j.
Qed.

(** In a complete graph every induced subgraph is complete: no regular one is non-trivial. *)
Lemma g263_complete_trivial (n d : nat) (S : {set 'K_n}) : regular (induced S) d -> d.+1 < #|S| -> False.
Proof.
case: (set_0Vmem S) => [-> | [x xS]]; first by rewrite cards0.
move=> /(_ (Sub x xS)) hd; rewrite -hd.
have -> : N(Sub x xS : induced S) = [set~ Sub x xS].
  apply/setP => w; rewrite !inE induced_edge /=.
  by rewrite /edge_rel /= -val_eqE eq_sym.
by rewrite cardsC1 card_sig; case: #|_| => // k; rewrite ltnn.
Qed.

(** ** erdos:1031 ********************************************************************* *)

Definition g263_ri_hyp_claim : Prop :=
  [/\ forall S : {set 'K_32,32}, #|'K_32,32| ^ 10 <= 2 ^ #|S| -> ~~ cliqueb S && ~~ stable S,
      #|'K_32,32| ^ 10 <= 2 ^ #|[set: 'K_32,32]|,
      [/\ regular (induced [set: 'K_32,32]) 32, 0 < 32, 32.+1 < #|[set: 'K_32,32]| &
          #|'K_32,32| <= 2 ^ (1 * #|[set: 'K_32,32]|)] &
      (regular_induced_subgraph_statement ->
         exists q N : nat, forall G : sgraph, N <= #|G| ->
           (forall S : {set G}, #|G| ^ 10 <= 2 ^ #|S| -> ~~ cliqueb S && ~~ stable S) ->
           exists S : {set G}, 3 <= #|S| /\ #|G| <= 2 ^ (q * #|S|))].

Theorem g263_ri_hyp_inhabited : g263_ri_hyp_claim.
Proof.
(* No goal may show 2 ^ 64 as a numeral power: nat is unary, so a closing [done] would compute it. *)
have e64 : #|'K_32,32| = 2 ^ 6 by rewrite g263_KB_card.
split; first exact: g263_KB_hyp.
- by rewrite cardsT {1}e64 -expnM (leq_exp2l _ _ (ltnSn 1)) g263_KB_card.
- split; first by apply: g263_regular_setT => v; exact: g263_KB_deg.
  + by [].
  + by rewrite cardsT g263_KB_card.
  + by rewrite cardsT mul1n; apply: ltnW; apply: ltn_expl.
- case=> q [N hN]; exists q, N => G hG hyp; have [S [d [_ d0 dS hS]]] := hN G hG hyp.
  exists S; split; last exact: hS.
  by apply: (leq_trans _ dS); rewrite !ltnS.
Qed.

(** The statement without its Ramsey hypothesis. *)
Definition g263_ri_no_ramsey : Prop :=
  exists q N : nat, forall G : sgraph, N <= #|G| ->
    exists (S : {set G}) (d : nat),
      [/\ regular (induced S) d, 0 < d, d.+1 < #|S| & #|G| <= 2 ^ (q * #|S|)].

Definition g263_ri_ntt_claim : Prop :=
  ~ g263_ri_no_ramsey /\ (g263_ri_no_ramsey -> regular_induced_subgraph_statement).

Theorem g263_ri_not_trivially_true : g263_ri_ntt_claim.
Proof.
split.
- case=> q [N hN]; have [S [d [hreg _ dS _]]] := hN 'K_N (eq_leq (esym (card_ord N))).
  exact: g263_complete_trivial hreg dS.
- case=> q [N hN]; exists q, N => G hG _; exact: hN G hG.
Qed.

Print Assumptions g263_cp_helper_sanity.
Print Assumptions g263_cf_hyp_inhabited.
Print Assumptions g263_cf_not_trivially_true.
Print Assumptions g263_ri_hyp_inhabited.
Print Assumptions g263_ri_not_trivially_true.
