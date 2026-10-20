(** * Digraph.ck3_main — Conjecture 1 at δ = 3: every oriented graph with
      minimum out-degree 3 has a directed path of length 6

    The δ = 3 endgame (dossier §3, E0–E5) on top of the Lemma 7 kernel,
    and the main theorem (dossier MAIN = the k3 hand proof's headline):

    - [no_short_strong3]: no strong 3-outregular oriented digraph has
      ℓ ≤ 5 — E0 kills ℓ ≤ 4 by the average bound; at ℓ = 5 the kernel
      forces |S| = 3 with all inner out-degrees 1 and a = 1 (E1), v₅ ∈ S
      (E2), the full fan-out of S onto C∖S (E3), σ-closure of S under the
      cycle predecessor (E4), and walking the closure four steps from v₅
      swallows all five cycle vertices (E5) — contradiction;
    - [ck_conj1_delta3]: δ⁺(D) ≥ 3 ⟹ ℓ(D) ≥ 6 (with 0 < #|D|: the empty
      digraph vacuously satisfies the hypothesis but has no path —
      dossier landmine 3);
    - [ck_conj1_delta3_path]: the unfolded exists-a-path form (D11). *)

From HB Require Import structures.
From mathcomp Require Import all_boot.
From Digraph Require Import prelude digraph oriented dipath strong lemma7.
Set SsrOldRewriteGoalsOrder.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** The endgame: no strong 3-outregular oriented digraph has ℓ ≤ 5 *)

Lemma no_short_strong3 (H : orientedDigraph) :
  (forall v : H, outdeg v = 3) -> 0 < #|H| -> strongb H ->
  ell H <= 5 -> False.
Proof.
move=> hreg hn0 hstr hell5.
have hell : ell H < 2 * 3 by rewrite (leq_ltn_trans hell5).
have [x [s [a [[ps sL a1 ale] [dcC szC cardC] [Scard Ble Bge yS] cl12 cnt]]]]
  := kernel_full hreg isT hn0 hstr hell.
set Cs := ckC x s a in dcC szC cardC cl12.
set Ss : {set H} := ckS x s a in Scard yS cl12 cnt.
set Bs : {set H} := ckB x s a in Scard Ble Bge.
have SsubC : forall z, z \in Ss -> z \in Cs.
  move=> z /imsetP[b bB ->].
  by rewrite mem_prev; move: bB; rewrite inE => /andP[].
have Sn0 : Ss != set0 by apply/set0Pn; exists (last x s).
have deg1 : forall v, v \in Ss -> 1 <= outdeg_in Ss v.
  move=> v vS; have [_ h2] := cnt v vS.
  apply: leq_trans h2.
  by rewrite subn_gt0 (leq_ltn_trans hell5).
have Sle3 : #|Ss| <= 3 by rewrite Scard.
have S3 : #|Ss| = 3.
  have [xx xxS xxle] := oriented_avg_bound Sn0.
  have := leq_trans (deg1 _ xxS) xxle.
  move=> h; apply/eqP; rewrite eqn_leq Sle3 /=.
  by move: h; rewrite half_gt0 ltn_subRL addn1.
have sumarcs : \sum_(v in Ss) outdeg_in Ss v <= 3.
  have := oriented_arcs_bound Ss.
  by rewrite S3 /= -[3 * (3 - 1)]/(2 * 3) leq_pmul2l.
have deg_eq1 : forall v, v \in Ss -> outdeg_in Ss v = 1.
  move=> v vS; apply/eqP; rewrite eqn_leq deg1 // andbT.
  rewrite leqNgt; apply/negP=> ge2.
  suff : 4 <= \sum_(v0 in Ss) outdeg_in Ss v0.
    by move=> h4; have := leq_trans h4 sumarcs.
  rewrite (big_setD1 v) //=.
  have step : 2 <= \sum_(v0 in Ss :\ v) outdeg_in Ss v0.
    apply: leq_trans (_ : \sum_(v0 in Ss :\ v) 1 <= _); last first.
      by apply: leq_sum => v0; rewrite inE => /andP[_ v0S]; exact: deg1.
    rewrite sum1_card.
    by move: (cardsD1 v Ss); rewrite vS S3 add1n => -[->].
  by rewrite -[4]/(2 + 2); exact: leq_add ge2 step.
have [hc _] := cnt _ yS.
rewrite S3 (deg_eq1 _ yS) cardC in hc.
have aLe : (ell H).+1 - a <= ell H.
  by rewrite leq_subLR addnC -addn1 leq_add2l.
have L5 : ell H = 5.
  apply/eqP; rewrite eqn_leq hell5 /=.
  by apply: leq_trans hc aLe.
have aE1 : a = 1.
  have : 3 + 3 - 1 <= (ell H).+1 - a by [].
  rewrite L5 /=.
  move=> h6; apply/eqP; rewrite eqn_leq a1 andbT.
  rewrite -(leq_add2r a) in h6.
  move: h6; rewrite subnK /=; last first.
    by apply: leq_trans (leq_addr 3 a) (leq_trans ale _); rewrite L5.
  by rewrite -[3 + 3 - 1]/5 -[6]/(5 + 1) leq_add2l.
have CsS : Cs = s by rewrite /Cs /ckC aE1 /= drop0.
have szCs5 : size Cs = 5 by rewrite szC L5 aE1.
have uCs : uniq Cs by case/and3P: dcC.
have cardC5 : #|ckCset x s a| = 5 by rewrite cardC L5 aE1.
have SsubC' : Ss \subset ckCset x s a.
  by apply/subsetP=> z zS; rewrite inE SsubC.
have cardCD : #|ckCset x s a :\: Ss| = 2.
  by rewrite cardsD (setIidPr SsubC') cardC5 S3.
have E3 : forall v t, v \in Ss -> t \in ckCset x s a :\: Ss -> v --> t.
  move=> v t vS tD.
  pose Av := [set z : H | v --> z].
  have AvC : Av \subset ckCset x s a.
    by apply/subsetP=> z; rewrite !inE => az; exact: cl12 vS az.
  have cardAv : #|Av| = 3 by rewrite -[RHS](hreg v).
  have cardAvS : #|Av :&: Ss| = 1.
    rewrite -(deg_eq1 _ vS) /outdeg_in.
    by apply: eq_card => z; rewrite !inE andbC.
  have cardAvD : #|Av :\: Ss| = 2 by rewrite cardsD cardAvS cardAv.
  have sub3 : Av :\: Ss \subset ckCset x s a :\: Ss.
    apply/subsetP=> z; rewrite !inE => /andP[zNS zA].
    rewrite zNS /=.
    by have := subsetP AvC z; rewrite !inE => h; exact: h.
  have eqD : Av :\: Ss = ckCset x s a :\: Ss.
    by apply/eqP; rewrite eqEcard sub3 cardAvD cardCD /=.
  have : t \in Av :\: Ss by rewrite eqD.
  by case/setDP=> + _; rewrite inE.
have E4 : forall z, z \in Ss -> prev Cs z \in Ss.
  move=> z zS.
  case pS : (prev Cs z \in Ss) => //; exfalso.
  have zC : z \in Cs by exact: SsubC.
  have pC : prev Cs z \in Cs by rewrite mem_prev.
  have arcZ : z --> prev Cs z.
    by apply: E3 zS _; rewrite !inE pS andTb pC.
  have arcP : prev Cs z --> z by exact: dicycle_prev dcC zC.
  by have := arc_asymm _ _ arcP; rewrite arcZ.
have preveq : forall i, i.+1 < size Cs ->
    prev Cs (nth x Cs i.+1) = nth x Cs i.
  move=> i ilt.
  rewrite prev_nth (mem_nth x ilt).
  case ECs : Cs ilt uCs => [|c0 c'] //= ilt /andP[_ uc'].
  rewrite index_uniq //.
  by apply: set_nth_default; rewrite /= ltnW.
have n4 : nth x Cs 4 \in Ss.
  have yE : last x s = nth x Cs 4.
    by rewrite CsS (last_nth x) sL L5.
  by rewrite -yE.
have n3 : nth x Cs 3 \in Ss.
  by have := E4 _ n4; rewrite preveq // szCs5.
have n2 : nth x Cs 2 \in Ss.
  by have := E4 _ n3; rewrite preveq // szCs5.
have n1 : nth x Cs 1 \in Ss.
  by have := E4 _ n2; rewrite preveq // szCs5.
have n0' : nth x Cs 0 \in Ss.
  by have := E4 _ n1; rewrite preveq // szCs5.
have : ckCset x s a \subset Ss.
  apply/subsetP=> t; rewrite inE => tC.
  case/(nthP x): tC => i; rewrite szCs5 => ilt <-.
  by case: i ilt => [|[|[|[|[|]]]]].
move/subset_leq_card.
by rewrite cardC5 S3.
Qed.

(** ** The main theorem: Conjecture 1 at δ = 3 *)

Theorem ck_conj1_delta3 (D : orientedDigraph) :
  0 < #|D| -> (forall v : D, 3 <= outdeg v) -> 6 <= ell D.
Proof.
move=> n0 dmin.
rewrite ltnNge; apply/negP=> hell5.
have [W [hn0 hstr hreg hell hcard]] := reduction n0 dmin.
apply: (no_short_strong3 hreg hn0 hstr).
exact: leq_trans hell hell5.
Qed.

(** Unfolded form: an explicit directed simple path with 6 arcs. *)
Corollary ck_conj1_delta3_path (D : orientedDigraph) :
  0 < #|D| -> (forall v : D, 3 <= outdeg v) ->
  exists x : D, exists s : seq D, dipath x s /\ size s = 6.
Proof.
move=> n0 dmin.
have h6 : 6 <= ell D by exact: ck_conj1_delta3.
have [x [s [ps sE]]] := ellP n0.
exists x, (take 6 s); split; first exact: dipath_take.
by rewrite size_takel // sE.
Qed.

(** Conjecture-1-shaped alias. *)
Corollary ck_conj1_at_3 (D : orientedDigraph) :
  0 < #|D| -> (forall v : D, 3 <= outdeg v) -> 2 * 3 <= ell D.
Proof. exact: ck_conj1_delta3. Qed.
