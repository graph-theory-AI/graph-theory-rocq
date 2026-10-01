(** * Hand reduction for the CK six-outregular C10, a=2 shape *)

From HB Require Import structures.
From mathcomp Require Import all_boot.
From Stdlib Require Import Lia.
From Digraph Require Import
  prelude digraph oriented dipath ckpath_cycle_tools.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Definitions.
Variable D : diGraphType.

Definition c10_cycle_set (c : seq D) : {set D} := [set z in c].
Definition c10_outside (c : seq D) : {set D} := ~: c10_cycle_set c.
Definition c10_gateway_set (c : seq D) (S : {set D}) : {set D} :=
  c10_cycle_set c :\: S.

(** These are the endpoints forced to be Hamilton-bad by the hand splice.
    The finite certificate uses a different Boolean mark for Hamilton
    badness; the bridge only needs the inclusion proved below. *)
Definition c10_bad_endpoints (c : seq D) (S : {set D}) : {set D} :=
  [set q in c10_gateway_set c S |
     3 <= outdeg_in (c10_outside c) q].

Definition c10_successor_set (c : seq D) (S : {set D}) : {set D} :=
  [set next c s | s in S].

Definition c10_hamilton_order
    (c : seq D) (start : D) (tail : seq D) (endpoint : D) : Prop :=
  [ /\ dipath start tail,
      last start tail = endpoint,
      size tail = 9
    & forall z, (z \in start :: tail) = (z \in c) ].

Definition c10_hamilton_from
    (c : seq D) (B : {set D}) (endpoint : D) : Prop :=
  exists start tail,
    start \in B /\ c10_hamilton_order c start tail endpoint.

End Definitions.

Section C10Hand.
Variable D : orientedDigraph.
Variables (c : seq D) (S : {set D}).

Hypothesis Hreg : forall v : D, outdeg v = 6.
Hypothesis Hell : ell D = 11.
Hypothesis Hcycle : dicycle c.
Hypothesis Hcsize : size c = 10.
Hypothesis HScard : #|S| = 6.
Hypothesis HSsub : S \subset c10_cycle_set c.
Hypothesis HSclosed :
  forall s z, s \in S -> s --> z -> z \in c10_cycle_set c.

Local Notation C := (c10_cycle_set c).
Local Notation R := (c10_outside c).
Local Notation Q := (c10_gateway_set c S).
Local Notation Bad := (c10_bad_endpoints c S).
Local Notation B := (c10_successor_set c S).

Lemma c10_cycle_card : #|C| = 10.
Proof.
by rewrite /C /c10_cycle_set (dicycle_set_card Hcycle) Hcsize.
Qed.

Lemma c10_gateway_card : #|Q| = 4.
Proof.
rewrite /Q /c10_gateway_set cardsD (setIidPr HSsub)
        c10_cycle_card HScard.
by [].
Qed.

Lemma c10_selected_internal_eq6 s :
  s \in S -> outdeg_in C s = 6.
Proof.
move=> sS.
rewrite /outdeg_in -[RHS](Hreg s) /outdeg.
apply: eq_card => z; rewrite !inE andb_idl //.
move=> asz.
move: (HSclosed sS asz).
by rewrite /C /c10_cycle_set inE.
Qed.

Lemma c10_selected_internal_sum :
  \sum_(s in S) outdeg_in C s = 36.
Proof.
under eq_bigr do rewrite c10_selected_internal_eq6 //.
by rewrite sum_nat_const HScard.
Qed.

Lemma c10_cycle_internal_upper :
  \sum_(q in C) outdeg_in C q <= 45.
Proof.
have h := oriented_arcs_bound C.
rewrite c10_cycle_card /= in h.
have h' :
    (\sum_(q in C) outdeg_in C q).*2 <= 45.*2.
  move: h.
  by rewrite mul2n.
move: h'.
by rewrite leq_double.
Qed.

Lemma c10_cycle_internal_partition :
  \sum_(q in C) outdeg_in C q =
    \sum_(s in S) outdeg_in C s +
    \sum_(q in Q) outdeg_in C q.
Proof.
rewrite (bigID (mem S)) /=.
have firstE :
    \sum_(q in C | q \in S) outdeg_in C q =
    \sum_(q in S) outdeg_in C q.
  apply: eq_bigl => q.
  case qS: (q \in S).
  - have qC := subsetP HSsub q qS.
    by rewrite qC.
  - by rewrite andbF.
have secondE :
    \sum_(q in C | q \notin S) outdeg_in C q =
    \sum_(q in Q) outdeg_in C q.
  apply: eq_bigl => q.
  rewrite /Q /c10_gateway_set /C /c10_cycle_set !inE.
  by rewrite andbC.
by rewrite firstE secondE.
Qed.

Lemma c10_gateway_internal_upper :
  \sum_(q in Q) outdeg_in C q <= 9.
Proof.
have hup := c10_cycle_internal_upper.
rewrite c10_cycle_internal_partition c10_selected_internal_sum in hup.
move: hup.
by rewrite -[45]/(36 + 9) leq_add2l.
Qed.

Lemma c10_gateway_degree_balance :
  \sum_(q in Q) outdeg_in C q +
  \sum_(q in Q) outdeg_in R q = 24.
Proof.
have hsplit :
    \sum_(q in Q) 6 =
      \sum_(q in Q) outdeg_in C q +
      \sum_(q in Q) outdeg_in R q.
  rewrite -big_split.
  apply: eq_bigr => q _.
  rewrite -(Hreg q).
  exact: outdeg_split_set C q.
move: hsplit.
by rewrite sum_nat_const c10_gateway_card.
Qed.

Lemma c10_gateway_cross_lower :
  15 <= \sum_(q in Q) outdeg_in R q.
Proof.
have hbal := c10_gateway_degree_balance.
have hup := c10_gateway_internal_upper.
change (24 - 9 <= \sum_(q in Q) outdeg_in R q).
rewrite leq_subLR // -hbal leq_add2r.
exact: hup.
Qed.

Lemma c10_gateway_outside_cap q :
  q \in Q -> outdeg_in R q <= 5.
Proof.
move=> qQ.
have qc : q \in c.
  move: qQ.
  by rewrite /Q /c10_gateway_set /C /c10_cycle_set !inE => /andP[].
have nqc0 : next c q \in c by rewrite mem_next.
have nqc : next c q \in C.
  by move: nqc0; rewrite /C /c10_cycle_set inE.
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

Lemma c10_bad_subset_gateway : Bad \subset Q.
Proof.
apply/subsetP=> q.
by rewrite /Bad /c10_bad_endpoints inE => /andP[].
Qed.

Lemma c10_bad_indicator_sum :
  \sum_(q in Q) ((q \in Bad) : nat) = #|Bad|.
Proof.
rewrite -sum1dep_card big_mkcond [RHS]big_mkcond /=.
apply: eq_bigr => q _.
case qBad: (q \in Bad).
- have /andP[qQ qhi] : (q \in Q) && (2 < outdeg_in R q).
    by move: qBad; rewrite /Bad /c10_bad_endpoints inE.
  by rewrite qQ qhi.
- have qcond : ((q \in Q) && (2 < outdeg_in R q)) = false.
    by move: qBad; rewrite /Bad /c10_bad_endpoints inE.
  by rewrite qcond; case: (q \in Q).
Qed.

Lemma c10_gateway_cross_bad_upper :
  \sum_(q in Q) outdeg_in R q <= 2 * #|Q| + 3 * #|Bad|.
Proof.
apply: leq_trans
  (_ : \sum_(q in Q) (2 + 3 * ((q \in Bad) : nat)) <= _).
- apply: leq_sum => q qQ.
  case qBad: (q \in Bad).
  - rewrite /=.
    exact: c10_gateway_outside_cap qQ.
  - rewrite /= addn0.
    move: qBad.
    rewrite /Bad /c10_bad_endpoints inE qQ /=.
    move=> qhiF.
    by rewrite leqNgt qhiF.
- rewrite big_split /= sum_nat_const.
  rewrite -big_distrr c10_bad_indicator_sum mulnC.
  by [].
Qed.

(** The hand arc count forces at least three high outside-degree endpoints. *)
Theorem c10_bad_card_ge3 : 3 <= #|Bad|.
Proof.
rewrite leqNgt; apply/negP=> hsmall.
have hlo := c10_gateway_cross_lower.
have hup := c10_gateway_cross_bad_upper.
have hbad2 : #|Bad| <= 2 by move: hsmall; rewrite ltnS.
have hmul : 3 * #|Bad| <= 3 * 2 by rewrite leq_pmul2l.
have hrhs : 2 * #|Q| + 3 * #|Bad| <= 14.
  rewrite c10_gateway_card.
  apply: leq_trans (leq_add (leqnn (2 * 4)) hmul) _.
  by [].
have hcross := leq_trans hup hrhs.
have himpossible := leq_trans hlo hcross.
by move: himpossible.
Qed.

Variables (v0 v1 : D).
Hypothesis Hv0R : v0 \in R.
Hypothesis Hv1R : v1 \in R.
Hypothesis Hv0Dv1 : v0 != v1.
Hypothesis Hv0v1 : v0 --> v1.
Hypothesis Hv1next : forall s, s \in S -> v1 --> next c s.

Lemma c10_bad_third_outneighbor q :
  q \in Bad ->
  exists z, [&& z \in R, q --> z, z != v0 & z != v1].
Proof.
move=> qBad.
have qdeg : 3 <= outdeg_in R q.
  move: qBad.
  by rewrite /Bad /c10_bad_endpoints inE => /andP[].
pose O : {set D} := [set z in R | q --> z].
have cardO : #|O| = outdeg_in R q by [].
have hcardO : 3 <= #|O| by rewrite cardO.
have Onsub : ~~ (O \subset [set v0; v1]).
  apply/negP=> Osub.
  have Ole := subset_leq_card Osub.
  have paircard : #|[set v0; v1]| = 2 by rewrite cards2 Hv0Dv1.
  have himpossible := leq_trans hcardO Ole.
  by move: himpossible; rewrite paircard.
have /subsetPn[z zO zNpair] := Onsub.
have zfacts : (z \in R) && (q --> z).
  by move: zO; rewrite /O inE.
have zdiff : (z != v0) && (z != v1).
  by move: zNpair; rewrite !inE negb_or.
exists z.
by case/andP: zfacts => -> ->; case/andP: zdiff => -> ->.
Qed.

(** A Hamilton ordering from [next(S)] to a high endpoint would splice with
    the two CK prefix vertices and a third outside out-neighbour, producing
    a 12-arc dipath against [ell D = 11]. *)
Lemma c10_bad_hamilton_splice q start tail :
  q \in Bad -> start \in B ->
  c10_hamilton_order c start tail q -> False.
Proof.
move=> qBad startB [hp lastq sizetail cover].
have [z /and4P[zR aqz zDv0 zDv1]] :=
  c10_bad_third_outneighbor qBad.
have v1start : v1 --> start.
  move: startB; rewrite /B /c10_successor_set.
  move=> /imsetP[s sS ->].
  exact: Hv1next s sS.
have outside_omit z0 : z0 \in R -> z0 \notin start :: tail.
  move=> z0R; apply/negP=> z0P.
  have z0c : z0 \in c by move: z0P; rewrite (cover z0).
  have z0C : z0 \in C by move: z0c; rewrite /C /c10_cycle_set inE.
  by move: z0R; rewrite /R /c10_outside inE z0C.
have zNpath := outside_omit z zR.
have v1Npath := outside_omit v1 Hv1R.
have v0Npath := outside_omit v0 Hv0R.
have hpz : dipath start (rcons tail z).
  by rewrite dipath_rcons hp lastq aqz zNpath.
have v1Dz : v1 != z by rewrite eq_sym.
have v1Nfull : v1 \notin start :: rcons tail z.
  move: v1Npath.
  by rewrite !inE mem_rcons !negb_or v1Dz => ->.
have hp1 : dipath v1 (start :: rcons tail z).
  rewrite /dipath /= v1start (dipath_path hpz) v1Nfull.
  by have := dipath_uniq hpz.
have v0Dz : v0 != z by rewrite eq_sym.
have v0Nfull : v0 \notin v1 :: start :: rcons tail z.
  move: v0Npath.
  by rewrite !inE mem_rcons !negb_or Hv0Dv1 v0Dz => ->.
have hp0 : dipath v0 (v1 :: start :: rcons tail z).
  rewrite /dipath /= Hv0v1 v1start (dipath_path hpz)
          v0Nfull v1Nfull /=.
  have uz := dipath_uniq hpz.
  by move: uz; rewrite /=.
have hlong := ell_max hp0.
move: hlong.
by rewrite /= size_rcons sizetail Hell.
Qed.

Theorem c10_bad_no_hamilton q :
  q \in Bad -> ~ c10_hamilton_from c B q.
Proof.
move=> qBad [start [tail [startB hham]]].
exact: c10_bad_hamilton_splice qBad startB hham.
Qed.

(** Bundled interface for the later finite-certificate bridge.  The order
    hypothesis is part of the CK shape, although the two conclusions below
    are in fact stronger and do not use it. *)
Theorem c10_hand_interface :
  13 <= #|D| ->
  [ /\ 3 <= #|Bad|
    & forall q, q \in Bad -> ~ c10_hamilton_from c B q ].
Proof.
move=> _; split.
- exact: c10_bad_card_ge3.
- exact: c10_bad_no_hamilton.
Qed.

End C10Hand.
