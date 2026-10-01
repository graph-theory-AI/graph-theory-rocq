(** * Gateway facts for the CK seven-outregular C12, a=1 shape. *)

From HB Require Import structures.
From mathcomp Require Import all_boot zify.
From Stdlib Require Import Lia.
From Digraph Require Import
  prelude digraph oriented dipath strong ckpath_cycle_tools
  ckpath_even_gateway ckpath_rotation_paths.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section C12Gateway.
Variable D : orientedDigraph.
Variables (c : seq D) (S : {set D}).

Hypothesis Hreg : forall v : D, outdeg v = 7.
Hypothesis Hstr : strongb D.
Hypothesis Hell : ell D = 12.
Hypothesis Hcycle : dicycle c.
Hypothesis Hcsize : size c = 12.
Hypothesis HScard : #|S| = 7.
Hypothesis HSsub : S \subset even_cycle_set c.
Hypothesis HSclosed :
  forall u v, u \in S -> u --> v -> v \in even_cycle_set c.
Hypothesis Horder : 15 <= #|D|.

Local Notation C := (even_cycle_set c).
Local Notation R := (even_outside c).
Local Notation Q := (even_gateway_set c S).
Local Notation A := (even_active_set c).
Local Notation eCR := (even_cross_arcs c).

Lemma c12_cycle_card : #|C| = 12.
Proof. by rewrite /even_cycle_set (dicycle_set_card Hcycle) Hcsize. Qed.

Lemma c12_outside_card_ge3 : 3 <= #|R|.
Proof.
have hsplit := cardsC C.
move: Horder.
rewrite -hsplit c12_cycle_card.
by rewrite -[15]/(12 + 3) leq_add2l.
Qed.

Lemma c12_cycle_plus_one_forbidden : size c + 1 <= ell D -> False.
Proof. by rewrite Hcsize Hell. Qed.

Lemma c12_outside_points_cycle x :
  x \in R -> exists2 z, z \in C & x --> z.
Proof.
move=> xR.
case: (boolP [exists z in C, x --> z]) =>
    [/exists_inP[z zC axz]|hno].
  by exists z.
rewrite negb_exists_in in hno.
move/forall_inP: hno => xno.
have Sn0 : S != set0 by rewrite -card_gt0 HScard.
move/set0Pn: Sn0 => [z zS].
have zC : z \in C := subsetP HSsub z zS.
have /strongP str := Hstr.
case/connectP: (str x z) => p pp lastE.
have xNC : x \notin C by move: xR; rewrite /R /even_outside inE.
have lastC : last x p \in C by rewrite -lastE.
have xno' : forall w, x --> w -> w \notin C.
  move=> w axw; apply/negP=> wC.
  by move: (xno w wC); rewrite axw.
have [u [v [w /and5P[uNC vNC wC auv avw]]]] :=
  path_first_entry_two_outside pp xNC lastC xno'.
have uNc : u \notin c by move: uNC; rewrite /C /even_cycle_set inE.
have vNc : v \notin c by move: vNC; rewrite /C /even_cycle_set inE.
have wc : w \in c by move: wC; rewrite /C /even_cycle_set inE.
have uDv : u != v.
  apply/eqP=> uv.
  by move: auv; rewrite uv arc_irrefl.
exfalso.
apply: c12_cycle_plus_one_forbidden.
exact: two_outside_cycle_ell Hcycle wc uNc vNc uDv auv avw.
Qed.

Lemma c12_outside_independent x y :
  x \in R -> y \in R -> x --> y = false.
Proof.
move=> xR yR; apply/negP=> axy.
have [z zC ayz] := c12_outside_points_cycle yR.
have xNc : x \notin c
  by move: xR; rewrite /R /even_outside /C /even_cycle_set !inE.
have yNc : y \notin c
  by move: yR; rewrite /R /even_outside /C /even_cycle_set !inE.
have zc : z \in c by move: zC; rewrite /C /even_cycle_set inE.
have xDy : x != y.
  apply/eqP=> xy.
  by move: axy; rewrite xy arc_irrefl.
apply: c12_cycle_plus_one_forbidden.
exact: two_outside_cycle_ell Hcycle zc xNc yNc xDy axy ayz.
Qed.

Lemma c12_outside_out_closed x :
  x \in R -> forall z, x --> z -> z \in C.
Proof.
move=> xR z axz.
case zC: (z \in C) => //.
have zR : z \in R by rewrite /R /even_outside inE zC.
by move: (c12_outside_independent xR zR); rewrite axz.
Qed.

Lemma c12_outside_outdeg_cycle x :
  x \in R -> outdeg_in C x = 7.
Proof.
move=> xR.
rewrite /outdeg_in -[RHS](Hreg x) /outdeg.
apply: eq_card => z; rewrite !inE andb_idl //.
move=> axz.
move: (c12_outside_out_closed xR axz).
by rewrite /C /even_cycle_set inE.
Qed.

Lemma c12_active_subset_gateway : A \subset Q.
Proof.
apply/subsetP=> q.
rewrite /A /even_active_set /Q /even_gateway_set !inE.
move=> /andP[qC qpos].
apply/andP; split; last exact: qC.
apply/negP=> qS.
move: qpos; rewrite /outdeg_in card_gt0 => /set0Pn[x].
rewrite inE => /andP[xR aqx].
have xC := HSclosed qS aqx.
by move: xR; rewrite /R /even_outside inE xC.
Qed.

Lemma c12_active_witness q :
  q \in A -> exists2 x, x \in R & q --> x.
Proof.
rewrite /A /even_active_set inE => /andP[_ qpos].
move: qpos; rewrite /outdeg_in card_gt0 => /set0Pn[x].
rewrite inE => /andP[xR aqx].
by exists x.
Qed.

Lemma c12_outside_second x :
  x \in R -> exists2 y, y \in R & y != x.
Proof.
move=> xR.
have Rx0 : R :\ x != set0.
  apply/negP=> /eqP Rx0.
  have hcard := cardsD1 x R.
  move: c12_outside_card_ge3.
  rewrite hcard xR Rx0 cards0 /=.
  by [].
move/set0Pn: Rx0 => [y].
rewrite inE => /andP[yDx yR].
exists y => //.
by move: yDx; rewrite inE.
Qed.

Lemma c12_active_successor_omitted q y :
  q \in A -> y \in R -> y --> next c q = false.
Proof.
move=> qA yR; apply/negP=> ayp.
have qC : q \in c.
  move: qA; rewrite /A /even_active_set /C /even_cycle_set !inE.
  by move=> /andP[].
have [x xR aqx] := c12_active_witness qA.
case: (eqVneq y x) => [yx|yDx].
- move: ayp; rewrite yx => axp.
  have [z zR zDx] := c12_outside_second xR.
  have [w wC azw] := c12_outside_points_cycle zR.
  have xNc : x \notin c
    by move: xR; rewrite /R /even_outside /C /even_cycle_set !inE.
  have zNc : z \notin c
    by move: zR; rewrite /R /even_outside /C /even_cycle_set !inE.
  have wc : w \in c by move: wC; rewrite /C /even_cycle_set inE.
  apply: c12_cycle_plus_one_forbidden.
  rewrite addn1.
  exact: (@cycle_sandwich_ell D c q x z w
    Hcycle qC xNc zNc zDx aqx axp wc azw).
- have xDy : x != y by rewrite eq_sym.
  have uc : uniq c by case/and3P: Hcycle.
  set p := next c q.
  have pc : p \in c by rewrite /p mem_next qC.
  have [s [ps szs cov _ lastE]] := dicycle_unroll Hcycle pc.
  have lastq : last p s = q by rewrite lastE /p prev_next.
  have xNc : x \notin c
    by move: xR; rewrite /R /even_outside /C /even_cycle_set !inE.
  have yNc : y \notin c
    by move: yR; rewrite /R /even_outside /C /even_cycle_set !inE.
  have xNps : x \notin p :: s by rewrite cov xNc.
  have yNps : y \notin p :: s by rewrite cov yNc.
  have hsplice := hamilton_splice_ell ps lastq xNps yNps xDy aqx ayp.
  have cpos : 0 < size c.
    move: Hcycle; rewrite /dicycle /nilp.
    by move=> /and3P[n0 _ _]; rewrite lt0n.
  apply: c12_cycle_plus_one_forbidden.
  move: hsplice; rewrite szs.
  by rewrite (prednK cpos) addn1.
Qed.

Lemma c12_gateway_card : #|Q| = 5.
Proof.
rewrite /Q /even_gateway_set cardsD (setIidPr HSsub)
        c12_cycle_card HScard.
by [].
Qed.

Lemma c12_successor_subset_cycle (B : {set D}) :
  B \subset C -> even_successor_set c B \subset C.
Proof.
move=> Bsub; apply/subsetP=> z.
rewrite /even_successor_set => /imsetP[q qB ->].
have qC := subsetP Bsub q qB.
move: qC; rewrite /C /even_cycle_set !inE.
by rewrite mem_next.
Qed.

Lemma c12_successor_card (B : {set D}) :
  #|even_successor_set c B| = #|B|.
Proof.
have uc : uniq c by case/and3P: Hcycle.
exact: card_imset (can_inj (prev_next uc)).
Qed.

Lemma c12_active_card_upper : #|A| <= 4.
Proof.
rewrite leqNgt; apply/negP=> hbig.
have AsubQ := c12_active_subset_gateway.
have AleQ := subset_leq_card AsubQ.
rewrite c12_gateway_card in AleQ.
have cardA : #|A| = 5.
  by apply/eqP; rewrite eqn_leq AleQ hbig.
have AQ : A = Q.
  apply/eqP; rewrite eqEcard AsubQ cardA c12_gateway_card.
  by [].
have QsubC : Q \subset C.
  apply/subsetP=> q.
  by rewrite /Q /even_gateway_set inE => /andP[_].
set T := even_successor_set c Q.
have TsubC : T \subset C by exact: c12_successor_subset_cycle QsubC.
have cardT : #|T| = 5 by rewrite /T c12_successor_card c12_gateway_card.
have cardCT : #|C :\: T| = 7.
  rewrite cardsD (setIidPr TsubC) c12_cycle_card cardT.
  by [].
have outE : forall x, x \in R -> [set z : D | x --> z] = C :\: T.
  move=> x xR.
  have Osub : [set z : D | x --> z] \subset C :\: T.
    apply/subsetP=> z; rewrite !inE => axz.
    have zC := c12_outside_out_closed xR axz.
    have zc : z \in c by move: zC; rewrite /C /even_cycle_set inE.
    apply/andP; split; last exact: zc.
    apply/negP=> zT.
    move: zT; rewrite /T /even_successor_set => /imsetP[q qQ zE].
    have qA : q \in A by rewrite AQ.
    have omit := c12_active_successor_omitted qA xR.
    by move: axz; rewrite zE omit.
  apply/eqP; rewrite eqEcard Osub cardCT.
  by rewrite /= -[7](Hreg x) /outdeg.
have QsubT : Q \subset T.
  apply/subsetP=> q qQ.
  have qA : q \in A by rewrite AQ.
  have [x xR aqx] := c12_active_witness qA.
  have qC := subsetP QsubC q qQ.
  case qT: (q \in T) => //.
  have qCT : q \in C :\: T by rewrite inE qT qC.
  have eqO := outE x xR.
  move: qCT; rewrite -eqO inE.
  by rewrite (arc_asymm _ _ aqx).
have QT : Q = T.
  apply/eqP; rewrite eqEcard QsubT cardT c12_gateway_card.
  by [].
have Qclosed : forall q, q \in Q -> next c q \in Q.
  move=> q qQ.
  have nqT : next c q \in T.
    rewrite /T /even_successor_set.
    by apply/imsetP; exists q.
  by rewrite QT.
have Qn0 : Q != set0 by rewrite -card_gt0 c12_gateway_card.
have QC : Q = C := next_closed_dicycle Hcycle Qn0 QsubC Qclosed.
have Sn0 : S != set0 by rewrite -card_gt0 HScard.
move/set0Pn: Sn0 => [s sS].
have sC := subsetP HSsub s sS.
have sQ : s \in Q by rewrite QC.
by move: sQ; rewrite /Q /even_gateway_set inE sS sC.
Qed.

Lemma c12_cross_balance :
  (\sum_(q in C) outdeg_in C q) + eCR = 84.
Proof.
rewrite /eCR /even_cross_arcs -big_split /=.
under eq_bigr do rewrite -outdeg_split_set Hreg.
by rewrite sum_nat_const c12_cycle_card.
Qed.

Lemma c12_cycle_internal_upper :
  \sum_(q in C) outdeg_in C q <= 66.
Proof.
have hb := oriented_arcs_bound C.
rewrite c12_cycle_card /= in hb.
change (is_true (2 * (\sum_(q in C) outdeg_in C q) <= 132)) in hb.
move: hb.
by rewrite -[132]/(2 * 66) leq_pmul2l.
Qed.

Lemma c12_cross_lower : 18 <= eCR.
Proof.
have bal := c12_cross_balance.
have iub := c12_cycle_internal_upper.
have h := leq_add iub (leqnn eCR).
rewrite bal in h.
move: h.
by rewrite -[84]/(66 + 18) leq_add2l.
Qed.

Lemma c12_active_outside_cap q : q \in A -> outdeg_in R q <= 6.
Proof.
move=> qA.
have qC : q \in C.
  by move: qA; rewrite /A /even_active_set inE => /andP[].
have qc : q \in c by move: qC; rewrite /C /even_cycle_set inE.
have nqc0 : next c q \in c by rewrite mem_next.
have nqc : next c q \in C.
  by move: nqc0; rewrite /C /even_cycle_set inE.
have aqn : q --> next c q := dicycle_next Hcycle qc.
have oneC : 1 <= outdeg_in C q.
  rewrite /outdeg_in card_gt0.
  apply/set0Pn; exists (next c q).
  by rewrite inE nqc aqn.
have split := outdeg_split_set C q.
rewrite Hreg in split.
have h := leq_add oneC (leqnn (outdeg_in R q)).
rewrite -split in h.
by move: h; rewrite add1n ltnS.
Qed.

Lemma c12_cross_active_sum :
  eCR = \sum_(q in A) outdeg_in R q.
Proof.
rewrite /eCR /even_cross_arcs (bigID (mem A)) /=.
have firstE :
    \sum_(q in C | q \in A) outdeg_in R q =
    \sum_(q in A) outdeg_in R q.
  apply: eq_bigl => q.
  case qA: (q \in A).
  - have qC : q \in C.
      by move: qA; rewrite /A /even_active_set inE => /andP[].
    by rewrite qC.
  - by rewrite andbF.
rewrite firstE.
have -> : \sum_(q in C | q \notin A) outdeg_in R q = 0.
  apply: big1 => q /andP[qC qNA].
  case hqR: (outdeg_in R q) => [|m] //.
  exfalso; move: qNA.
  rewrite /A /even_active_set inE qC hqR /=.
  by [].
by rewrite addn0.
Qed.

Lemma c12_cross_upper : eCR <= #|A| * 6.
Proof.
rewrite c12_cross_active_sum.
apply: leq_trans (_ : \sum_(q in A) 6 <= _).
  exact: leq_sum (fun q qA => c12_active_outside_cap qA).
by rewrite sum_nat_const mulnC.
Qed.

Theorem c12_active_card34 : 3 <= #|A| <= 4.
Proof.
apply/andP; split; last exact: c12_active_card_upper.
have hlo := c12_cross_lower.
have hup := c12_cross_upper.
apply/ltP.
by nia.
Qed.

(** The lower cross-arc bound is tight if there are only three active
    gateways.  We expose the equality chain separately because it is useful
    when translating the C12 finite certificate. *)
Lemma c12_cross_eq18 (HcardA : #|A| = 3) : eCR = 18.
Proof.
apply/eqP; rewrite eqn_leq c12_cross_lower andbT.
have := c12_cross_upper.
by rewrite HcardA.
Qed.

Lemma c12_cycle_internal_eq66 (HcardA : #|A| = 3) :
  \sum_(q in C) outdeg_in C q = 66.
Proof.
have bal := c12_cross_balance.
rewrite (c12_cross_eq18 HcardA) in bal.
have bal' :
    (\sum_(q in C) outdeg_in C q) + 18 = 66 + 18.
  by move: bal; rewrite /=.
apply/eqP.
rewrite -(eqn_add2r 18).
apply/eqP.
exact: bal'.
Qed.

Lemma c12_cycle_remove_card u : u \in C -> #|C :\ u| = 11.
Proof.
move=> uC.
have h := cardsD1 u C.
move: h; rewrite uC c12_cycle_card /= add1n => h.
have hp := congr1 predn h.
move: hp; rewrite /= => hp.
exact: esym hp.
Qed.

(** Equality in the oriented arc bound makes the twelve-cycle projection a
    tournament. *)
Lemma c12_cycle_total (HcardA : #|A| = 3) u v :
  u \in C -> v \in C -> u != v -> (u --> v) || (v --> u).
Proof.
move=> uC vC uDv.
case auv: (u --> v) => //.
case avu: (v --> u) => //.
exfalso.
have uCv : u \in (C :\ v).
  rewrite !inE.
  have uc : u \in c by move: uC; rewrite /C /even_cycle_set inE.
  by rewrite uDv uc.
have cardCvu : #|(C :\ v) :\ u| = 10.
  have h := cardsD1 u (C :\ v).
  move: h; rewrite uCv (c12_cycle_remove_card vC) /= add1n => h.
  have hp := congr1 predn h.
  move: hp; rewrite /= => hp.
  exact: esym hp.
have rowu : \sum_(z in C) ((u --> z) + (z --> u)) <= 10.
  rewrite (big_setD1 v vC) /= auv avu.
  have h := even_pair_sum_bound (C :\ v) u.
  by rewrite cardCvu in h.
have rows_rest :
    \sum_(x in C :\ u) \sum_(z in C) ((x --> z) + (z --> x))
      <= 11 * 11.
  rewrite -{1}(c12_cycle_remove_card uC) -sum_nat_const.
  apply: leq_sum => x.
  rewrite inE => /andP[_ xC].
  have h := even_pair_sum_bound C x.
  by rewrite (c12_cycle_remove_card xC) in h.
have total_le :
    \sum_(x in C) \sum_(z in C) ((x --> z) + (z --> x)) <= 131.
  rewrite (big_setD1 u uC) /=.
  apply: leq_trans (leq_add rowu rows_rest) _.
  by [].
have hd := even_double_internal C.
rewrite (c12_cycle_internal_eq66 HcardA) /= in hd.
move: total_le; rewrite -hd.
by [].
Qed.

Lemma c12_active_remove_card (HcardA : #|A| = 3) q :
  q \in A -> #|A :\ q| = 2.
Proof.
move=> qA.
have h := cardsD1 q A.
move: h; rewrite qA HcardA /= add1n => h.
have hp := congr1 predn h.
move: hp; rewrite /= => hp.
exact: esym hp.
Qed.

Lemma c12_active_outside_eq6 (HcardA : #|A| = 3) q :
  q \in A -> outdeg_in R q = 6.
Proof.
move=> qA.
apply/eqP; rewrite eqn_leq; apply/andP; split.
- exact: c12_active_outside_cap qA.
- rewrite leqNgt; apply/negP=> qlt.
  have restle :
      \sum_(u in A :\ q) outdeg_in R u <= 2 * 6.
    rewrite -[2](c12_active_remove_card HcardA qA) -sum_nat_const.
    apply: leq_sum => u uA.
    have uA0 : u \in A by move: uA; rewrite !inE => /andP[].
    rewrite (c12_active_remove_card HcardA qA) /=.
    exact: c12_active_outside_cap uA0.
  have sumsplit :
      eCR = outdeg_in R q + \sum_(u in A :\ q) outdeg_in R u.
    by rewrite c12_cross_active_sum (big_setD1 q qA).
  have elt : eCR < 3 * 6.
    rewrite sumsplit.
    apply: leq_ltn_trans (leq_add (leqnn _) restle) _.
    change (outdeg_in R q + 12 < 6 + 12).
    by rewrite ltn_add2r.
  move: elt.
  by rewrite (c12_cross_eq18 HcardA) ltnn.
Qed.

Lemma c12_active_cycle_eq1 (HcardA : #|A| = 3) q :
  q \in A -> outdeg_in C q = 1.
Proof.
move=> qA.
have split := outdeg_split_set C q.
rewrite Hreg (c12_active_outside_eq6 HcardA qA) in split.
have split' : outdeg_in C q + 6 = 1 + 6.
  by move: split; rewrite /=.
apply/eqP.
rewrite -(eqn_add2r 6).
apply/eqP.
exact: split'.
Qed.

Lemma c12_active_pair_total (HcardA : #|A| = 3) u v :
  u \in A -> v \in A ->
  (u --> v) + (v --> u) = (u != v : nat).
Proof.
move=> uA vA.
case: (eqVneq u v) => [->|uDv].
  by rewrite !arc_irrefl.
have AsubC : A \subset C.
  apply/subsetP=> q.
  by rewrite /A /even_active_set inE => /andP[].
have uC := subsetP AsubC u uA.
have vC := subsetP AsubC v vA.
have /orP[auv|avu] := c12_cycle_total HcardA uC vC uDv.
- by rewrite auv (arc_asymm _ _ auv).
- by rewrite avu (arc_asymm _ _ avu) add0n.
Qed.

Lemma c12_active_internal_arcs (HcardA : #|A| = 3) :
  \sum_(q in A) outdeg_in A q = 3.
Proof.
have pairE :
    \sum_(u in A) \sum_(v in A) ((u --> v) + (v --> u)) = 6.
  have rowE u : u \in A ->
      \sum_(v in A) ((u --> v) + (v --> u)) = 2.
    move=> uA.
    under eq_bigr do rewrite (c12_active_pair_total HcardA uA) //.
    rewrite even_neq_sum_card.
    exact: (c12_active_remove_card HcardA (q := u) uA).
  under eq_bigr do rewrite rowE //.
  by rewrite sum_nat_const HcardA.
have hd := even_double_internal A.
rewrite pairE in hd.
have hd' :
    (\sum_(q in A) outdeg_in A q).*2 = 3.*2.
  by move: hd; rewrite mul2n.
exact: double_inj hd'.
Qed.

Lemma c12_active_internal_eq1 (HcardA : #|A| = 3) q :
  q \in A -> outdeg_in A q = 1.
Proof.
move=> qA.
have AsubC : A \subset C.
  apply/subsetP=> z.
  by rewrite /A /even_active_set inE => /andP[].
have qle : outdeg_in A q <= 1.
  rewrite -(c12_active_cycle_eq1 HcardA qA).
  exact: @outdeg_in_mono D A C q AsubC.
apply/eqP; rewrite eqn_leq; apply/andP; split; first exact: qle.
rewrite leqNgt; apply/negP=> qzero.
have qE0 : outdeg_in A q = 0.
  apply/eqP.
  move: qzero.
  by rewrite ltnS leqn0.
have restle :
    \sum_(u in A :\ q) outdeg_in A u <= 2 * 1.
  rewrite -[2](c12_active_remove_card HcardA qA) -sum_nat_const.
  apply: leq_sum => u uA.
  have uA0 : u \in A by move: uA; rewrite !inE => /andP[].
  rewrite -(c12_active_cycle_eq1 HcardA uA0).
  exact: @outdeg_in_mono D A C u AsubC.
have sumsplit :
    \sum_(u in A) outdeg_in A u =
      outdeg_in A q + \sum_(u in A :\ q) outdeg_in A u.
  by rewrite (big_setD1 q qA).
have hsum_le : \sum_(u in A) outdeg_in A u <= 2.
  rewrite sumsplit qE0 add0n.
  exact: restle.
move: hsum_le.
by rewrite (c12_active_internal_arcs HcardA).
Qed.

Lemma c12_active_successor_closed (HcardA : #|A| = 3) q :
  q \in A -> next c q \in A.
Proof.
move=> qA.
have AsubC : A \subset C.
  apply/subsetP=> z.
  by rewrite /A /even_active_set inE => /andP[].
have qC := subsetP AsubC q qA.
have qc : q \in c by move: qC; rewrite /C /even_cycle_set inE.
have nqc0 : next c q \in c by rewrite mem_next.
have nqc : next c q \in C by move: nqc0; rewrite /C /even_cycle_set inE.
have aqn : q --> next c q := dicycle_next Hcycle qc.
pose NA : {set D} := [set z in A | q --> z].
pose NC : {set D} := [set z in C | q --> z].
have Nsub : NA \subset NC.
  apply/subsetP=> z; rewrite /NA /NC !inE.
  move=> /andP[zA aqz].
  move/andP: zA => [zc _].
  by rewrite zc aqz.
have cardNA : #|NA| = 1 by
  exact: (c12_active_internal_eq1 HcardA (q := q) qA).
have cardNC : #|NC| = 1 by
  exact: (c12_active_cycle_eq1 HcardA (q := q) qA).
have NAC : NA = NC.
  apply/eqP; rewrite eqEcard Nsub cardNA cardNC.
  by [].
have nqNC : next c q \in NC by rewrite /NC inE nqc aqn.
rewrite -NAC /NA inE in nqNC.
by case/andP: nqNC.
Qed.

Lemma c12_active3_impossible : #|A| = 3 -> False.
Proof.
move=> HcardA.
have AsubC : A \subset C.
  apply/subsetP=> q.
  by rewrite /A /even_active_set inE => /andP[].
have An0 : A != set0 by rewrite -card_gt0 HcardA.
have AC : A = C :=
  next_closed_dicycle Hcycle An0 AsubC (c12_active_successor_closed HcardA).
have hcard : #|A| = #|C| by rewrite AC.
move: hcard.
by rewrite HcardA c12_cycle_card.
Qed.

Theorem c12_active_card4 : #|A| = 4.
Proof.
have /andP[hlo hup] := c12_active_card34.
apply/eqP; rewrite eqn_leq hup /=.
rewrite leqNgt; apply/negP=> hlt4.
have HcardA : #|A| = 3.
  apply/eqP; rewrite eqn_leq hlo andbT.
  exact: hlt4.
exact: c12_active3_impossible HcardA.
Qed.

(** A Hamilton ordering of C ending at an active gateway cannot start at
    an outneighbor of any outside vertex. *)
Lemma c12_hamilton_start_omitted root y endpoint path x tail :
  root \in c -> y \in R -> cycle_label c root endpoint \in A ->
  size path = size c ->
  labelled_numeric_path c root path = x :: tail ->
  dipath x tail -> [set z in x :: tail] = C ->
  last x tail = cycle_label c root endpoint ->
  y --> x = false.
Proof.
move=> rootc yR qA pathsz labE hpath hset hlast.
move: (c12_active_witness qA) => [u uR qu].
have uout : u \notin x :: tail.
  apply/negP => uin.
  have uC : u \in C by rewrite -hset in_set uin.
  move: uR; rewrite /even_outside inE uC /=.
  by [].
have yout : y \notin x :: tail.
  apply/negP => yin.
  have yC : y \in C by rewrite -hset in_set yin.
  move: yR; rewrite /even_outside inE yC /=.
  by [].
have tailsz : (size tail).+1 = size c.
  move: (congr1 size labE).
  rewrite /labelled_numeric_path size_map /= pathsz.
  by [].
have elltail : ell D < (size tail).+2 by lia.
case: (eqVneq y u) => [->|yu].
- move: (c12_outside_second uR) => [v vR vu].
  move: (c12_outside_points_cycle vR) => [z zC vz].
  have vout : v \notin x :: tail.
    apply/negP => vin.
    have vC : v \in C by rewrite -hset in_set vin.
    move: vR; rewrite /even_outside inE vC /=.
    by [].
  have zinset : z \in [set z in x :: tail] by rewrite hset.
  have zin : z \in x :: tail by move: zinset; rewrite in_set.
  have uv : u != v by rewrite eq_sym.
  exact: (hamilton_active_start_omitted hpath hlast uout vout uv qu zin vz
            elltail).
- have uy : u != y by rewrite eq_sym.
  exact: (hamilton_start_omitted hpath hlast uout yout uy qu elltail).
Qed.

End C12Gateway.
