(** * Odd-cycle gateway obstruction for the small Cheng--Keevash cases. *)

From HB Require Import structures.
From mathcomp Require Import all_boot zify.
From Stdlib Require Import Lia.
From Digraph Require Import
  prelude digraph oriented dipath strong ckpath_cycle_tools.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Definitions.
Variable D : diGraphType.

Definition odd_cycle_set (c : seq D) : {set D} := [set z in c].
Definition odd_outside (c : seq D) : {set D} := ~: odd_cycle_set c.
Definition odd_gateway_set (c : seq D) (S : {set D}) : {set D} :=
  odd_cycle_set c :\: S.
Definition odd_active_set (c : seq D) : {set D} :=
  [set q in odd_cycle_set c | 0 < outdeg_in (odd_outside c) q].
Definition odd_successor_set (c : seq D) (A : {set D}) : {set D} :=
  [set next c q | q in A].
Definition odd_cross_arcs (c : seq D) : nat :=
  \sum_(q in odd_cycle_set c) outdeg_in (odd_outside c) q.

End Definitions.

Section OddGateway.
Variable D : orientedDigraph.
Variables (d : nat) (c : seq D) (S : {set D}).

Hypothesis Hd2 : 2 <= d.
Hypothesis Hreg : forall v : D, outdeg v = d.
Hypothesis Hstr : strongb D.
Hypothesis Hell : ell D < 2 * d.
Hypothesis Hcycle : dicycle c.
Hypothesis Hcsize : size c = 2 * d - 1.
Hypothesis HScard : #|S| = d.
Hypothesis HSsub : S \subset odd_cycle_set c.
Hypothesis HSclosed :
  forall u v, u \in S -> u --> v -> v \in odd_cycle_set c.
Hypothesis Horder : 2 * d + 1 <= #|D|.

Local Notation C := (odd_cycle_set c).
Local Notation R := (odd_outside c).
Local Notation Q := (odd_gateway_set c S).
Local Notation A := (odd_active_set c).
Local Notation eCR := (odd_cross_arcs c).

Lemma odd_cycle_card : #|C| = 2 * d - 1.
Proof. by rewrite /odd_cycle_set (dicycle_set_card Hcycle) Hcsize. Qed.

Lemma odd_outside_card_ge2 : 2 <= #|R|.
Proof.
apply/leP.
have horder : Peano.le (2 * d + 1) #|D| := leP Horder.
have hsplit := cardsC C.
have hc := odd_cycle_card.
change (#|C| + #|R| = #|D|)%N in hsplit.
lia.
Qed.

Lemma odd_cycle_plus_one_forbidden :
  size c + 1 <= ell D -> False.
Proof. by lia. Qed.

Lemma odd_outside_points_cycle x :
  x \in R -> exists2 z, z \in C & x --> z.
Proof.
move=> xR.
case: (boolP [exists z in C, x --> z]) =>
    [/exists_inP[z zC axz]|hno].
  by exists z.
rewrite negb_exists_in in hno.
move/forall_inP: hno => xno.
have Sn0 : S != set0.
  rewrite -card_gt0 HScard.
  exact: (leq_trans Hd2 (leqnSn d)).
move/set0Pn: Sn0 => [z zS].
have zC : z \in C := subsetP HSsub z zS.
have /strongP str := Hstr.
case/connectP: (str x z) => p pp lastE.
have xNC : x \notin C.
  by move: xR; rewrite /R /odd_outside inE.
have lastC : last x p \in C by rewrite -lastE.
have xno' : forall w, x --> w -> w \notin C.
  move=> w axw; apply/negP=> wC.
  by move: (xno w wC); rewrite axw.
have [u [v [w /and5P[uNC vNC wC auv avw]]]] :=
  path_first_entry_two_outside pp xNC lastC xno'.
have uNc : u \notin c by move: uNC; rewrite /C /odd_cycle_set inE.
have vNc : v \notin c by move: vNC; rewrite /C /odd_cycle_set inE.
have wc : w \in c by move: wC; rewrite /C /odd_cycle_set inE.
have uDv : u != v.
  apply/eqP=> uv.
  by move: auv; rewrite uv arc_irrefl.
exfalso.
have hlong := two_outside_cycle_ell Hcycle wc uNc vNc uDv auv avw.
have dpos : 0 < d by exact: leq_ltn_trans (leq0n 1) Hd2.
have h2d : 0 < 2 * d by rewrite muln_gt0; apply/andP; split.
move: hlong; rewrite Hcsize (subnK h2d) => hlong'.
by have := leq_ltn_trans hlong' Hell; rewrite ltnn.
Qed.

Lemma odd_outside_independent x y :
  x \in R -> y \in R -> x --> y = false.
Proof.
move=> xR yR; apply/negP=> axy.
have [z zC ayz] := odd_outside_points_cycle yR.
have xNc : x \notin c
  by move: xR; rewrite /R /odd_outside /C /odd_cycle_set !inE.
have yNc : y \notin c
  by move: yR; rewrite /R /odd_outside /C /odd_cycle_set !inE.
have zc : z \in c by move: zC; rewrite /C /odd_cycle_set inE.
have xDy : x != y.
  apply/eqP=> xy.
  by move: axy; rewrite xy arc_irrefl.
have hlong := two_outside_cycle_ell Hcycle zc xNc yNc xDy axy ayz.
have dpos : 0 < d by exact: leq_ltn_trans (leq0n 1) Hd2.
have h2d : 0 < 2 * d by rewrite muln_gt0; apply/andP; split.
move: hlong; rewrite Hcsize (subnK h2d) => hlong'.
by have := leq_ltn_trans hlong' Hell; rewrite ltnn.
Qed.

Lemma odd_outside_out_closed x :
  x \in R -> forall z, x --> z -> z \in C.
Proof.
move=> xR z axz.
case zC: (z \in C) => //.
have zR : z \in R by rewrite /R /odd_outside inE zC.
by move: (odd_outside_independent xR zR); rewrite axz.
Qed.

Lemma odd_outside_outdeg_cycle x :
  x \in R -> outdeg_in C x = d.
Proof.
move=> xR.
rewrite /outdeg_in -[RHS](Hreg x) /outdeg.
apply: eq_card => z; rewrite !inE andb_idl //.
move=> axz.
move: (odd_outside_out_closed xR axz).
by rewrite /C /odd_cycle_set inE.
Qed.

Lemma odd_active_subset_gateway : A \subset Q.
Proof.
apply/subsetP=> q.
rewrite /A /odd_active_set /Q /odd_gateway_set !inE.
move=> /andP[qC qpos].
apply/andP; split; last exact: qC.
apply/negP=> qS.
move: qpos; rewrite /outdeg_in card_gt0 => /set0Pn[x].
rewrite inE => /andP[xR aqx].
have xC := HSclosed qS aqx.
by move: xR; rewrite /R /odd_outside inE xC.
Qed.

Lemma odd_active_witness q :
  q \in A -> exists2 x, x \in R & q --> x.
Proof.
rewrite /A /odd_active_set inE => /andP[_ qpos].
move: qpos; rewrite /outdeg_in card_gt0 => /set0Pn[x].
rewrite inE => /andP[xR aqx].
by exists x.
Qed.

Lemma odd_outside_second x :
  x \in R -> exists2 y, y \in R & y != x.
Proof.
move=> xR.
have Rx0 : R :\ x != set0.
  apply/negP=> /eqP Rx0.
  have hcard := cardsD1 x R.
  move: odd_outside_card_ge2.
  rewrite hcard xR Rx0 cards0 /=.
  by [].
move/set0Pn: Rx0 => [y].
rewrite inE => /andP[yDx yR].
exists y => //.
by move: yDx; rewrite inE.
Qed.

Lemma odd_active_successor_omitted q y :
  q \in A -> y \in R -> y --> next c q = false.
Proof.
move=> qA yR; apply/negP=> ayp.
have qC : q \in c.
  move: qA; rewrite /A /odd_active_set /C /odd_cycle_set !inE.
  by move=> /andP[].
have [x xR aqx] := odd_active_witness qA.
case: (eqVneq y x) => [yx|yDx].
- move: ayp; rewrite yx => axp.
  have [z zR zDx] := odd_outside_second xR.
  have [w wC azw] := odd_outside_points_cycle zR.
  have xNc : x \notin c
    by move: xR; rewrite /R /odd_outside /C /odd_cycle_set !inE.
  have zNc : z \notin c
    by move: zR; rewrite /R /odd_outside /C /odd_cycle_set !inE.
  have wc : w \in c by move: wC; rewrite /C /odd_cycle_set inE.
  apply: odd_cycle_plus_one_forbidden.
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
    by move: xR; rewrite /R /odd_outside /C /odd_cycle_set !inE.
  have yNc : y \notin c
    by move: yR; rewrite /R /odd_outside /C /odd_cycle_set !inE.
  have xNps : x \notin p :: s by rewrite cov xNc.
  have yNps : y \notin p :: s by rewrite cov yNc.
  have hsplice :=
    hamilton_splice_ell ps lastq xNps yNps xDy aqx ayp.
  have cpos : 0 < size c.
    move: Hcycle; rewrite /dicycle /nilp.
    by move=> /and3P[n0 _ _]; rewrite lt0n.
  apply: odd_cycle_plus_one_forbidden.
  move: hsplice; rewrite szs.
  by rewrite (prednK cpos) addn1.
Qed.

Lemma odd_gateway_card : #|Q| = d - 1.
Proof.
rewrite /Q /odd_gateway_set cardsD (setIidPr HSsub)
        odd_cycle_card HScard.
lia.
Qed.

Lemma odd_successor_subset_cycle (B : {set D}) :
  B \subset C -> odd_successor_set c B \subset C.
Proof.
move=> Bsub; apply/subsetP=> z.
rewrite /odd_successor_set => /imsetP[q qB ->].
have qC := subsetP Bsub q qB.
move: qC; rewrite /C /odd_cycle_set !inE.
by rewrite mem_next.
Qed.

Lemma odd_successor_card (B : {set D}) :
  #|odd_successor_set c B| = #|B|.
Proof.
have uc : uniq c by case/and3P: Hcycle.
exact: card_imset (can_inj (prev_next uc)).
Qed.

Lemma odd_active_card_upper : #|A| <= d - 2.
Proof.
rewrite leqNgt; apply/negP=> hbig.
have AsubQ := odd_active_subset_gateway.
have AleQ := subset_leq_card AsubQ.
rewrite odd_gateway_card in AleQ.
have cardA : #|A| = d - 1 by lia.
have AQ : A = Q.
  apply/eqP; rewrite eqEcard AsubQ cardA odd_gateway_card.
  by lia.
have QsubC : Q \subset C.
  apply/subsetP=> q.
  by rewrite /Q /odd_gateway_set inE => /andP[_].
set T := odd_successor_set c Q.
have TsubC : T \subset C by exact: odd_successor_subset_cycle QsubC.
have cardT : #|T| = d - 1
  by rewrite /T odd_successor_card odd_gateway_card.
have cardCT : #|C :\: T| = d.
  rewrite cardsD (setIidPr TsubC) odd_cycle_card cardT.
  lia.
have outE : forall x, x \in R -> [set z : D | x --> z] = C :\: T.
  move=> x xR.
  have Osub : [set z : D | x --> z] \subset C :\: T.
    apply/subsetP=> z; rewrite !inE => axz.
    have zC := odd_outside_out_closed xR axz.
    have zc : z \in c by move: zC; rewrite /C /odd_cycle_set inE.
    apply/andP; split; last exact: zc.
    apply/negP=> zT.
    move: zT; rewrite /T /odd_successor_set => /imsetP[q qQ zE].
    have qA : q \in A by rewrite AQ.
    have omit := odd_active_successor_omitted qA xR.
    by move: axz; rewrite zE omit.
  apply/eqP; rewrite eqEcard Osub cardCT.
  by rewrite /= -[d](Hreg x) /outdeg.
have QsubT : Q \subset T.
  apply/subsetP=> q qQ.
  have qA : q \in A by rewrite AQ.
  have [x xR aqx] := odd_active_witness qA.
  have qC := subsetP QsubC q qQ.
  case qT: (q \in T) => //.
  have qCT : q \in C :\: T by rewrite inE qT qC.
  have eqO := outE x xR.
  move: qCT; rewrite -eqO inE.
  by rewrite (arc_asymm _ _ aqx).
have QT : Q = T.
  apply/eqP; rewrite eqEcard QsubT cardT odd_gateway_card.
  by lia.
have Qclosed : forall q, q \in Q -> next c q \in Q.
  move=> q qQ.
  have nqT : next c q \in T.
    rewrite /T /odd_successor_set.
    by apply/imsetP; exists q.
  by rewrite QT.
have Qn0 : Q != set0.
  rewrite -card_gt0 odd_gateway_card.
  by lia.
have QC : Q = C := next_closed_dicycle Hcycle Qn0 QsubC Qclosed.
have Sn0 : S != set0.
  rewrite -card_gt0 HScard.
  by lia.
move/set0Pn: Sn0 => [s sS].
have sC := subsetP HSsub s sS.
have sQ : s \in Q by rewrite QC.
by move: sQ; rewrite /Q /odd_gateway_set inE sS sC.
Qed.

Lemma odd_cross_arcs_lower : 2 * d - 1 <= eCR.
Proof.
have hsplit :
    (\sum_(q in C) d) =
      (\sum_(q in C) outdeg_in C q) + eCR.
  rewrite /eCR /odd_cross_arcs -big_split.
  apply: eq_bigr => q qC.
  rewrite -(Hreg q).
  exact: outdeg_split_set C q.
have hbound :
    2 * (\sum_(q in C) outdeg_in C q) <= #|C| * (#|C| - 1) :=
  oriented_arcs_bound C.
rewrite sum_nat_const odd_cycle_card in hsplit.
rewrite odd_cycle_card in hbound.
apply/leP.
by lia.
Qed.

Lemma odd_cross_arcs_upper : eCR <= #|A| * (d - 1).
Proof.
have active_bound q : q \in A -> outdeg_in R q <= d - 1.
  move=> qA.
  have qC : q \in c.
    move: qA; rewrite /A /odd_active_set /C /odd_cycle_set !inE.
    by move=> /andP[].
  have hpos : 0 < outdeg_in C q.
    rewrite /outdeg_in card_gt0.
    apply/set0Pn; exists (next c q); rewrite inE.
    apply/andP; split.
    - move: qC; rewrite /C /odd_cycle_set !inE.
      by rewrite mem_next.
    - exact: dicycle_next Hcycle qC.
  have hsplit := outdeg_split_set C q.
  rewrite Hreg in hsplit.
  apply/leP.
  change (outdeg_in (~: C) q <= d - 1)%coq_nat.
  move/ltP: hpos => hpos.
  lia.
have inactive_zero q :
    q \in C -> q \notin A -> outdeg_in R q = 0.
  move=> qC qNA; apply/eqP; rewrite -leqn0.
  move: qNA; rewrite /A /odd_active_set inE qC /=.
  by rewrite -leqNgt.
rewrite /eCR /odd_cross_arcs (bigID (mem A)) /=.
have inactive_sum :
    \sum_(i in C | i \notin A) outdeg_in R i = 0.
  apply: big1 => q /andP[qC qNA].
  exact: inactive_zero qC qNA.
rewrite inactive_sum addn0.
apply: (leq_trans (n := \sum_(i in C | i \in A) (d - 1))).
  apply: leq_sum => q /andP[_ qA].
  exact: active_bound qA.
rewrite sum_nat_const.
have hcard :
    #|(fun i : D => (i \in C) && (i \in A))| <= #|A|.
  apply: subset_leq_card.
  apply/subsetP=> i /andP[_ iA].
  exact iA.
exact: leq_mul hcard (leqnn (d - 1)).
Qed.

Lemma odd_active_card_lower : 3 <= #|A|.
Proof.
have hlo := odd_cross_arcs_lower.
have hup := odd_cross_arcs_upper.
apply/ltP.
by nia.
Qed.

Theorem odd_gateway_d4_impossible : d = 4 -> False.
Proof.
move=> d4.
have hlo := odd_active_card_lower.
have hup := odd_active_card_upper.
by lia.
Qed.

Theorem odd_gateway_d5_active3 : d = 5 -> #|A| = 3.
Proof.
move=> d5.
have hlo := odd_active_card_lower.
have hup := odd_active_card_upper.
by lia.
Qed.

Theorem odd_gateway_d6_active34 : d = 6 -> 3 <= #|A| <= 4.
Proof.
move=> d6.
apply/andP; split.
- exact: odd_active_card_lower.
- have hup := odd_active_card_upper.
  by lia.
Qed.

Theorem odd_gateway_d7_active345 : d = 7 -> 3 <= #|A| <= 5.
Proof.
move=> d7.
apply/andP; split.
- exact: odd_active_card_lower.
- have hup := odd_active_card_upper.
  by lia.
Qed.

End OddGateway.
