(** * The hand elimination of the CK six-outregular C10, a=1 shape *)

From HB Require Import structures.
From mathcomp Require Import all_boot.
From Stdlib Require Import Lia.
From Digraph Require Import
  prelude digraph oriented dipath strong ckpath_cycle_tools.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Definitions.
Variable D : diGraphType.

Definition even_cycle_set (c : seq D) : {set D} := [set z in c].
Definition even_outside (c : seq D) : {set D} := ~: even_cycle_set c.
Definition even_gateway_set (c : seq D) (S : {set D}) : {set D} :=
  even_cycle_set c :\: S.
Definition even_active_set (c : seq D) : {set D} :=
  [set q in even_cycle_set c | 0 < outdeg_in (even_outside c) q].
Definition even_successor_set (c : seq D) (A : {set D}) : {set D} :=
  [set next c q | q in A].
Definition even_cross_arcs (c : seq D) : nat :=
  \sum_(q in even_cycle_set c) outdeg_in (even_outside c) q.

End Definitions.

Section EvenGateway.
Variable D : orientedDigraph.
Variables (c : seq D) (S : {set D}).

Hypothesis Hreg : forall v : D, outdeg v = 6.
Hypothesis Hstr : strongb D.
Hypothesis Hell : ell D = 10.
Hypothesis Hcycle : dicycle c.
Hypothesis Hcsize : size c = 10.
Hypothesis HScard : #|S| = 6.
Hypothesis HSsub : S \subset even_cycle_set c.
Hypothesis HSclosed :
  forall u v, u \in S -> u --> v -> v \in even_cycle_set c.
Hypothesis Horder : 13 <= #|D|.

Local Notation C := (even_cycle_set c).
Local Notation R := (even_outside c).
Local Notation Q := (even_gateway_set c S).
Local Notation A := (even_active_set c).
Local Notation eCR := (even_cross_arcs c).

Lemma even_cycle_card : #|C| = 10.
Proof. by rewrite /even_cycle_set (dicycle_set_card Hcycle) Hcsize. Qed.

Lemma even_outside_card_ge3 : 3 <= #|R|.
Proof.
have hsplit := cardsC C.
move: Horder.
rewrite -hsplit even_cycle_card.
by rewrite -[13]/(10 + 3) leq_add2l.
Qed.

Lemma even_cycle_plus_one_forbidden : size c + 1 <= ell D -> False.
Proof. by rewrite Hcsize Hell. Qed.

Lemma even_outside_points_cycle x :
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
apply: even_cycle_plus_one_forbidden.
exact: two_outside_cycle_ell Hcycle wc uNc vNc uDv auv avw.
Qed.

Lemma even_outside_independent x y :
  x \in R -> y \in R -> x --> y = false.
Proof.
move=> xR yR; apply/negP=> axy.
have [z zC ayz] := even_outside_points_cycle yR.
have xNc : x \notin c
  by move: xR; rewrite /R /even_outside /C /even_cycle_set !inE.
have yNc : y \notin c
  by move: yR; rewrite /R /even_outside /C /even_cycle_set !inE.
have zc : z \in c by move: zC; rewrite /C /even_cycle_set inE.
have xDy : x != y.
  apply/eqP=> xy.
  by move: axy; rewrite xy arc_irrefl.
apply: even_cycle_plus_one_forbidden.
exact: two_outside_cycle_ell Hcycle zc xNc yNc xDy axy ayz.
Qed.

Lemma even_outside_out_closed x :
  x \in R -> forall z, x --> z -> z \in C.
Proof.
move=> xR z axz.
case zC: (z \in C) => //.
have zR : z \in R by rewrite /R /even_outside inE zC.
by move: (even_outside_independent xR zR); rewrite axz.
Qed.

Lemma even_outside_outdeg_cycle x :
  x \in R -> outdeg_in C x = 6.
Proof.
move=> xR.
rewrite /outdeg_in -[RHS](Hreg x) /outdeg.
apply: eq_card => z; rewrite !inE andb_idl //.
move=> axz.
move: (even_outside_out_closed xR axz).
by rewrite /C /even_cycle_set inE.
Qed.

Lemma even_active_subset_gateway : A \subset Q.
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

Lemma even_active_witness q :
  q \in A -> exists2 x, x \in R & q --> x.
Proof.
rewrite /A /even_active_set inE => /andP[_ qpos].
move: qpos; rewrite /outdeg_in card_gt0 => /set0Pn[x].
rewrite inE => /andP[xR aqx].
by exists x.
Qed.

Lemma even_outside_second x :
  x \in R -> exists2 y, y \in R & y != x.
Proof.
move=> xR.
have Rx0 : R :\ x != set0.
  apply/negP=> /eqP Rx0.
  have hcard := cardsD1 x R.
  move: even_outside_card_ge3.
  rewrite hcard xR Rx0 cards0 /=.
  by [].
move/set0Pn: Rx0 => [y].
rewrite inE => /andP[yDx yR].
exists y => //.
by move: yDx; rewrite inE.
Qed.

Lemma even_active_successor_omitted q y :
  q \in A -> y \in R -> y --> next c q = false.
Proof.
move=> qA yR; apply/negP=> ayp.
have qC : q \in c.
  move: qA; rewrite /A /even_active_set /C /even_cycle_set !inE.
  by move=> /andP[].
have [x xR aqx] := even_active_witness qA.
case: (eqVneq y x) => [yx|yDx].
- move: ayp; rewrite yx => axp.
  have [z zR zDx] := even_outside_second xR.
  have [w wC azw] := even_outside_points_cycle zR.
  have xNc : x \notin c
    by move: xR; rewrite /R /even_outside /C /even_cycle_set !inE.
  have zNc : z \notin c
    by move: zR; rewrite /R /even_outside /C /even_cycle_set !inE.
  have wc : w \in c by move: wC; rewrite /C /even_cycle_set inE.
  apply: even_cycle_plus_one_forbidden.
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
  apply: even_cycle_plus_one_forbidden.
  move: hsplice; rewrite szs.
  by rewrite (prednK cpos) addn1.
Qed.

Lemma even_gateway_card : #|Q| = 4.
Proof.
rewrite /Q /even_gateway_set cardsD (setIidPr HSsub)
        even_cycle_card HScard.
by [].
Qed.

Lemma even_successor_subset_cycle (B : {set D}) :
  B \subset C -> even_successor_set c B \subset C.
Proof.
move=> Bsub; apply/subsetP=> z.
rewrite /even_successor_set => /imsetP[q qB ->].
have qC := subsetP Bsub q qB.
move: qC; rewrite /C /even_cycle_set !inE.
by rewrite mem_next.
Qed.

Lemma even_successor_card (B : {set D}) :
  #|even_successor_set c B| = #|B|.
Proof.
have uc : uniq c by case/and3P: Hcycle.
exact: card_imset (can_inj (prev_next uc)).
Qed.

Lemma even_active_card_upper : #|A| <= 3.
Proof.
rewrite leqNgt; apply/negP=> hbig.
have AsubQ := even_active_subset_gateway.
have AleQ := subset_leq_card AsubQ.
rewrite even_gateway_card in AleQ.
have cardA : #|A| = 4.
  by apply/eqP; rewrite eqn_leq AleQ hbig.
have AQ : A = Q.
  apply/eqP; rewrite eqEcard AsubQ cardA even_gateway_card.
  by [].
have QsubC : Q \subset C.
  apply/subsetP=> q.
  by rewrite /Q /even_gateway_set inE => /andP[_].
set T := even_successor_set c Q.
have TsubC : T \subset C by exact: even_successor_subset_cycle QsubC.
have cardT : #|T| = 4 by rewrite /T even_successor_card even_gateway_card.
have cardCT : #|C :\: T| = 6.
  rewrite cardsD (setIidPr TsubC) even_cycle_card cardT.
  by [].
have outE : forall x, x \in R -> [set z : D | x --> z] = C :\: T.
  move=> x xR.
  have Osub : [set z : D | x --> z] \subset C :\: T.
    apply/subsetP=> z; rewrite !inE => axz.
    have zC := even_outside_out_closed xR axz.
    have zc : z \in c by move: zC; rewrite /C /even_cycle_set inE.
    apply/andP; split; last exact: zc.
    apply/negP=> zT.
    move: zT; rewrite /T /even_successor_set => /imsetP[q qQ zE].
    have qA : q \in A by rewrite AQ.
    have omit := even_active_successor_omitted qA xR.
    by move: axz; rewrite zE omit.
  apply/eqP; rewrite eqEcard Osub cardCT.
  by rewrite /= -[6](Hreg x) /outdeg.
have QsubT : Q \subset T.
  apply/subsetP=> q qQ.
  have qA : q \in A by rewrite AQ.
  have [x xR aqx] := even_active_witness qA.
  have qC := subsetP QsubC q qQ.
  case qT: (q \in T) => //.
  have qCT : q \in C :\: T by rewrite inE qT qC.
  have eqO := outE x xR.
  move: qCT; rewrite -eqO inE.
  by rewrite (arc_asymm _ _ aqx).
have QT : Q = T.
  apply/eqP; rewrite eqEcard QsubT cardT even_gateway_card.
  by [].
have Qclosed : forall q, q \in Q -> next c q \in Q.
  move=> q qQ.
  have nqT : next c q \in T.
    rewrite /T /even_successor_set.
    by apply/imsetP; exists q.
  by rewrite QT.
have Qn0 : Q != set0 by rewrite -card_gt0 even_gateway_card.
have QC : Q = C := next_closed_dicycle Hcycle Qn0 QsubC Qclosed.
have Sn0 : S != set0 by rewrite -card_gt0 HScard.
move/set0Pn: Sn0 => [s sS].
have sC := subsetP HSsub s sS.
have sQ : s \in Q by rewrite QC.
by move: sQ; rewrite /Q /even_gateway_set inE sS sC.
Qed.

Lemma even_cross_balance :
  (\sum_(q in C) outdeg_in C q) + eCR = 60.
Proof.
rewrite /eCR /even_cross_arcs -big_split /=.
under eq_bigr do rewrite -outdeg_split_set Hreg.
by rewrite sum_nat_const even_cycle_card.
Qed.

Lemma even_cycle_internal_upper :
  \sum_(q in C) outdeg_in C q <= 45.
Proof.
have hb := oriented_arcs_bound C.
rewrite even_cycle_card /= in hb.
change (is_true (2 * (\sum_(q in C) outdeg_in C q) <= 90)) in hb.
move: hb.
by rewrite -[90]/(2 * 45) leq_pmul2l.
Qed.

Lemma even_cross_lower : 15 <= eCR.
Proof.
have bal := even_cross_balance.
have iub := even_cycle_internal_upper.
have h := leq_add iub (leqnn eCR).
rewrite bal in h.
move: h.
by rewrite -[60]/(45 + 15) leq_add2l.
Qed.

Lemma even_active_outside_cap q : q \in A -> outdeg_in R q <= 5.
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

Lemma even_cross_active_sum :
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

Lemma even_cross_upper : eCR <= #|A| * 5.
Proof.
rewrite even_cross_active_sum.
apply: leq_trans (_ : \sum_(q in A) 5 <= _).
  exact: leq_sum (fun q qA => even_active_outside_cap qA).
by rewrite sum_nat_const mulnC.
Qed.

Lemma even_active_card : #|A| = 3.
Proof.
apply/eqP; rewrite eqn_leq; apply/andP; split.
- exact: even_active_card_upper.
-
have hlo := even_cross_lower.
have hup := even_cross_upper.
have hprod : 3 * 5 <= #|A| * 5 by exact: leq_trans hlo hup.
by move: hprod; rewrite leq_pmul2r.
Qed.

Lemma even_cross_eq15 : eCR = 15.
Proof.
apply/eqP; rewrite eqn_leq even_cross_lower andbT.
have := even_cross_upper.
by rewrite even_active_card.
Qed.

Lemma even_cycle_internal_eq45 :
  \sum_(q in C) outdeg_in C q = 45.
Proof.
have bal := even_cross_balance.
rewrite even_cross_eq15 in bal.
have bal' :
    (\sum_(q in C) outdeg_in C q) + 15 = 45 + 15.
  by move: bal; rewrite /=.
apply/eqP.
rewrite -(eqn_add2r 15).
apply/eqP.
exact: bal'.
Qed.

(** Equality in the oriented arc count makes the cycle projection a
    tournament.  The next two helpers expose the equality case without
    introducing a separate tournament structure. *)
Lemma even_neq_sum_card (B : {set D}) u :
  \sum_(v in B) ((u != v) : nat) = #|B :\ u|.
Proof.
rewrite -sum1dep_card big_mkcond [RHS]big_mkcond /=.
apply: eq_bigr => v _; rewrite !inE eq_sym andbC.
by case: (v \in B); case: (v != u).
Qed.

Lemma even_pair_sum_bound (B : {set D}) u :
  \sum_(v in B) ((u --> v) + (v --> u)) <= #|B :\ u|.
Proof.
apply: leq_trans (_ : \sum_(v in B) ((u != v) : nat) <= _).
  apply: leq_sum => v _.
  exact: arc_pair_bound.
rewrite even_neq_sum_card.
by [].
Qed.

Lemma even_double_internal (B : {set D}) :
  2 * (\sum_(u in B) outdeg_in B u) =
  \sum_(u in B) \sum_(v in B) ((u --> v) + (v --> u)).
Proof.
rewrite mul2n -addnn.
under eq_bigr do rewrite outdeg_in_sumE.
rewrite {2}exchange_big /= -big_split /=.
apply: eq_bigr => u _.
by rewrite -big_split /=.
Qed.

Lemma even_cycle_remove_card u : u \in C -> #|C :\ u| = 9.
Proof.
move=> uC.
have h := cardsD1 u C.
move: h; rewrite uC even_cycle_card /= add1n => h.
have hp := congr1 predn h.
move: hp; rewrite /= => hp.
exact: esym hp.
Qed.

Lemma even_cycle_total u v :
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
have cardCvu : #|(C :\ v) :\ u| = 8.
  have h := cardsD1 u (C :\ v).
  move: h; rewrite uCv (even_cycle_remove_card vC) /= add1n => h.
  have hp := congr1 predn h.
  move: hp; rewrite /= => hp.
  exact: esym hp.
have rowu : \sum_(z in C) ((u --> z) + (z --> u)) <= 8.
  rewrite (big_setD1 v vC) /= auv avu.
  have h := even_pair_sum_bound (C :\ v) u.
  by rewrite cardCvu in h.
have rows_rest :
    \sum_(x in C :\ u) \sum_(z in C) ((x --> z) + (z --> x))
      <= 9 * 9.
  rewrite -{1}(even_cycle_remove_card uC) -sum_nat_const.
  apply: leq_sum => x.
  rewrite inE => /andP[_ xC].
  have h := even_pair_sum_bound C x.
  by rewrite (even_cycle_remove_card xC) in h.
have total_le :
    \sum_(x in C) \sum_(z in C) ((x --> z) + (z --> x)) <= 89.
  rewrite (big_setD1 u uC) /=.
  apply: leq_trans (leq_add rowu rows_rest) _.
  by [].
have hd := even_double_internal C.
rewrite even_cycle_internal_eq45 /= in hd.
move: total_le; rewrite -hd.
by [].
Qed.

Lemma even_active_remove_card q : q \in A -> #|A :\ q| = 2.
Proof.
move=> qA.
have h := cardsD1 q A.
move: h; rewrite qA even_active_card /= add1n => h.
have hp := congr1 predn h.
move: hp; rewrite /= => hp.
exact: esym hp.
Qed.

Lemma even_active_outside_eq5 q :
  q \in A -> outdeg_in R q = 5.
Proof.
move=> qA.
apply/eqP; rewrite eqn_leq; apply/andP; split.
- exact: even_active_outside_cap qA.
-
rewrite leqNgt; apply/negP=> qlt.
have restle :
    \sum_(u in A :\ q) outdeg_in R u <= 2 * 5.
  rewrite -[2](even_active_remove_card qA) -sum_nat_const.
  apply: leq_sum => u uA.
  have uA0 : u \in A by move: uA; rewrite !inE => /andP[].
  rewrite (even_active_remove_card qA) /=.
  exact: even_active_outside_cap uA0.
have sumsplit :
    eCR = outdeg_in R q + \sum_(u in A :\ q) outdeg_in R u.
  by rewrite even_cross_active_sum (big_setD1 q qA).
have elt : eCR < 3 * 5.
  rewrite sumsplit.
  apply: leq_ltn_trans (leq_add (leqnn _) restle) _.
  change (outdeg_in R q + 10 < 5 + 10).
  by rewrite ltn_add2r.
move: elt.
by rewrite even_cross_eq15 ltnn.
Qed.

Lemma even_active_cycle_eq1 q :
  q \in A -> outdeg_in C q = 1.
Proof.
move=> qA.
have split := outdeg_split_set C q.
rewrite Hreg (even_active_outside_eq5 qA) in split.
have split' : outdeg_in C q + 5 = 1 + 5.
  by move: split; rewrite /=.
apply/eqP.
rewrite -(eqn_add2r 5).
apply/eqP.
exact: split'.
Qed.

Lemma even_active_pair_total u v :
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
have /orP[auv|avu] := even_cycle_total uC vC uDv.
- by rewrite auv (arc_asymm _ _ auv).
- by rewrite avu (arc_asymm _ _ avu) add0n.
Qed.

Lemma even_active_internal_arcs :
  \sum_(q in A) outdeg_in A q = 3.
Proof.
have pairE :
    \sum_(u in A) \sum_(v in A) ((u --> v) + (v --> u)) = 6.
  have rowE u : u \in A ->
      \sum_(v in A) ((u --> v) + (v --> u)) = 2.
    move=> uA.
    under eq_bigr do rewrite even_active_pair_total //.
    rewrite even_neq_sum_card.
    exact: even_active_remove_card uA.
  under eq_bigr do rewrite rowE //.
  by rewrite sum_nat_const even_active_card.
have hd := even_double_internal A.
rewrite pairE in hd.
have hd' :
    (\sum_(q in A) outdeg_in A q).*2 = 3.*2.
  by move: hd; rewrite mul2n.
exact: double_inj hd'.
Qed.

Lemma even_active_internal_eq1 q :
  q \in A -> outdeg_in A q = 1.
Proof.
move=> qA.
have AsubC : A \subset C.
  apply/subsetP=> z.
  by rewrite /A /even_active_set inE => /andP[].
have qle : outdeg_in A q <= 1.
  rewrite -(even_active_cycle_eq1 qA).
  exact: @outdeg_in_mono D A C q AsubC.
apply/eqP; rewrite eqn_leq; apply/andP; split; first exact: qle.
rewrite leqNgt; apply/negP=> qzero.
have qE0 : outdeg_in A q = 0.
  apply/eqP.
  move: qzero.
  by rewrite ltnS leqn0.
have restle :
    \sum_(u in A :\ q) outdeg_in A u <= 2 * 1.
  rewrite -[2](even_active_remove_card qA) -sum_nat_const.
  apply: leq_sum => u uA.
  have uA0 : u \in A by move: uA; rewrite !inE => /andP[].
  rewrite -(even_active_cycle_eq1 uA0).
  exact: @outdeg_in_mono D A C u AsubC.
have sumsplit :
    \sum_(u in A) outdeg_in A u =
      outdeg_in A q + \sum_(u in A :\ q) outdeg_in A u.
  by rewrite (big_setD1 q qA).
have hsum_le : \sum_(u in A) outdeg_in A u <= 2.
  rewrite sumsplit qE0 add0n.
  exact: restle.
move: hsum_le.
by rewrite even_active_internal_arcs.
Qed.

Lemma even_active_successor_closed q :
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
have cardNA : #|NA| = 1 by exact: even_active_internal_eq1 qA.
have cardNC : #|NC| = 1 by exact: even_active_cycle_eq1 qA.
have NAC : NA = NC.
  apply/eqP; rewrite eqEcard Nsub cardNA cardNC.
  by [].
have nqNC : next c q \in NC by rewrite /NC inE nqc aqn.
rewrite -NAC /NA inE in nqNC.
by case/andP: nqNC.
Qed.

(** The exact a=1 CK shape supplies [ell D = 10].  Under that shape the
    ten-cycle gateway configuration is impossible by hand. *)
Theorem no_even_gateway6_c10 : False.
Proof.
have AsubC : A \subset C.
  apply/subsetP=> q.
  by rewrite /A /even_active_set inE => /andP[].
have An0 : A != set0 by rewrite -card_gt0 even_active_card.
have AC : A = C :=
  next_closed_dicycle Hcycle An0 AsubC even_active_successor_closed.
have hcard : #|A| = #|C| by rewrite AC.
move: hcard.
by rewrite even_active_card even_cycle_card.
Qed.

End EvenGateway.
