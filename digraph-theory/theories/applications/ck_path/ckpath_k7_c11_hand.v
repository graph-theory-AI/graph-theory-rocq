(** * Hand reduction for the CK seven-outregular C11, a=3 shape *)

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

Definition c11_k7_cycle_set (c : seq D) : {set D} := [set z in c].
Definition c11_k7_outside (c : seq D) : {set D} := ~: c11_k7_cycle_set c.
Definition c11_k7_gateway_set (c : seq D) (S : {set D}) : {set D} :=
  c11_k7_cycle_set c :\: S.
Definition c11_k7_bad_endpoints (c : seq D) (S : {set D}) : {set D} :=
  [set q in c11_k7_gateway_set c S |
     4 <= outdeg_in (c11_k7_outside c) q].
Definition c11_k7_successor_set (c : seq D) (S : {set D}) : {set D} :=
  [set next c s | s in S].

Definition c11_k7_hamilton_order
    (c : seq D) (start : D) (tail : seq D) (endpoint : D) : Prop :=
  [ /\ dipath start tail,
      last start tail = endpoint,
      size tail = 10
    & forall z, (z \in start :: tail) = (z \in c) ].

Definition c11_k7_hamilton_from
    (c : seq D) (B : {set D}) (endpoint : D) : Prop :=
  exists start tail,
    start \in B /\ c11_k7_hamilton_order c start tail endpoint.

End Definitions.

Section C11Hand.
Variable D : orientedDigraph.
Variables (c : seq D) (S : {set D}).

Hypothesis Hreg : forall v : D, outdeg v = 7.
Hypothesis Hell : ell D = 13.
Hypothesis Hcycle : dicycle c.
Hypothesis Hcsize : size c = 11.
Hypothesis HScard : #|S| = 6.
Hypothesis HSsub : S \subset c11_k7_cycle_set c.
Hypothesis HSclosed :
  forall s z, s \in S -> s --> z -> z \in c11_k7_cycle_set c.

Local Notation C := (c11_k7_cycle_set c).
Local Notation R := (c11_k7_outside c).
Local Notation Q := (c11_k7_gateway_set c S).
Local Notation Bad := (c11_k7_bad_endpoints c S).
Local Notation B := (c11_k7_successor_set c S).

Lemma c11_k7_cycle_card : #|C| = 11.
Proof.
by rewrite /C /c11_k7_cycle_set (dicycle_set_card Hcycle) Hcsize.
Qed.

Lemma c11_k7_gateway_card : #|Q| = 5.
Proof.
rewrite /Q /c11_k7_gateway_set cardsD (setIidPr HSsub)
        c11_k7_cycle_card HScard.
by [].
Qed.

Lemma c11_k7_selected_internal_eq7 s :
  s \in S -> outdeg_in C s = 7.
Proof.
move=> sS.
rewrite /outdeg_in -[RHS](Hreg s) /outdeg.
apply: eq_card => z; rewrite !inE andb_idl //.
move=> asz.
move: (HSclosed sS asz).
by rewrite /C /c11_k7_cycle_set inE.
Qed.

Lemma c11_k7_selected_internal_sum :
  \sum_(s in S) outdeg_in C s = 42.
Proof.
under eq_bigr do rewrite c11_k7_selected_internal_eq7 //.
by rewrite sum_nat_const HScard.
Qed.

Lemma c11_k7_cycle_internal_upper :
  \sum_(q in C) outdeg_in C q <= 55.
Proof.
have h := oriented_arcs_bound C.
rewrite c11_k7_cycle_card /= in h.
have h' : (\sum_(q in C) outdeg_in C q).*2 <= 55.*2.
  move: h.
  by rewrite mul2n.
move: h'.
by rewrite leq_double.
Qed.

Lemma c11_k7_cycle_internal_partition :
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
  rewrite /Q /c11_k7_gateway_set /C /c11_k7_cycle_set !inE.
  by rewrite andbC.
by rewrite firstE secondE.
Qed.

Lemma c11_k7_gateway_internal_upper :
  \sum_(q in Q) outdeg_in C q <= 13.
Proof.
have hup := c11_k7_cycle_internal_upper.
rewrite c11_k7_cycle_internal_partition c11_k7_selected_internal_sum in hup.
move: hup.
by rewrite -[55]/(42 + 13) leq_add2l.
Qed.

Lemma c11_k7_gateway_degree_balance :
  \sum_(q in Q) outdeg_in C q +
  \sum_(q in Q) outdeg_in R q = 35.
Proof.
have hsplit :
    \sum_(q in Q) 7 =
      \sum_(q in Q) outdeg_in C q +
      \sum_(q in Q) outdeg_in R q.
  rewrite -big_split.
  apply: eq_bigr => q _.
  rewrite -(Hreg q).
  exact: outdeg_split_set C q.
move: hsplit.
by rewrite sum_nat_const c11_k7_gateway_card.
Qed.

Lemma c11_k7_gateway_cross_lower :
  22 <= \sum_(q in Q) outdeg_in R q.
Proof.
have hbal := c11_k7_gateway_degree_balance.
have hup := c11_k7_gateway_internal_upper.
change (35 - 13 <= \sum_(q in Q) outdeg_in R q).
rewrite leq_subLR // -hbal leq_add2r.
exact: hup.
Qed.

Lemma c11_k7_gateway_outside_cap q :
  q \in Q -> outdeg_in R q <= 6.
Proof.
move=> qQ.
have qc : q \in c.
  move: qQ.
  by rewrite /Q /c11_k7_gateway_set /C /c11_k7_cycle_set !inE => /andP[].
have nqc0 : next c q \in c by rewrite mem_next.
have nqc : next c q \in C.
  by move: nqc0; rewrite /C /c11_k7_cycle_set inE.
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

Lemma c11_k7_bad_indicator_sum :
  \sum_(q in Q) ((q \in Bad) : nat) = #|Bad|.
Proof.
rewrite -sum1dep_card big_mkcond [RHS]big_mkcond /=.
apply: eq_bigr => q _.
case qBad: (q \in Bad).
- have /andP[qQ qhi] : (q \in Q) && (3 < outdeg_in R q).
    by move: qBad; rewrite /Bad /c11_k7_bad_endpoints inE.
  by rewrite qQ qhi.
- have qcond : ((q \in Q) && (3 < outdeg_in R q)) = false.
    by move: qBad; rewrite /Bad /c11_k7_bad_endpoints inE.
  by rewrite qcond; case: (q \in Q).
Qed.

Lemma c11_k7_gateway_cross_bad_upper :
  \sum_(q in Q) outdeg_in R q <= 3 * #|Q| + 3 * #|Bad|.
Proof.
apply: leq_trans
  (_ : \sum_(q in Q) (3 + 3 * ((q \in Bad) : nat)) <= _).
- apply: leq_sum => q qQ.
  case qBad: (q \in Bad).
  - rewrite /=.
    exact: c11_k7_gateway_outside_cap qQ.
  - rewrite /= addn0.
    move: qBad.
    rewrite /Bad /c11_k7_bad_endpoints inE qQ /=.
    move=> qhiF.
    by rewrite leqNgt qhiF.
- rewrite big_split /= sum_nat_const.
  rewrite -big_distrr c11_k7_bad_indicator_sum mulnC.
  by [].
Qed.

(** The 42-versus-55 count forces at least three high endpoints. *)
Theorem c11_k7_bad_card_ge3 : 3 <= #|Bad|.
Proof.
rewrite leqNgt; apply/negP=> hsmall.
have hlo := c11_k7_gateway_cross_lower.
have hup := c11_k7_gateway_cross_bad_upper.
have hbad2 : #|Bad| <= 2 by move: hsmall; rewrite ltnS.
have hmul : 3 * #|Bad| <= 3 * 2 by rewrite leq_pmul2l.
have hrhs : 3 * #|Q| + 3 * #|Bad| <= 21.
  rewrite c11_k7_gateway_card.
  apply: leq_trans (leq_add (leqnn (3 * 5)) hmul) _.
  by [].
have hcross := leq_trans hup hrhs.
have himpossible := leq_trans hlo hcross.
by move: himpossible.
Qed.

Variables (v0 v1 v2 : D).
Hypothesis Hv0R : v0 \in R.
Hypothesis Hv1R : v1 \in R.
Hypothesis Hv2R : v2 \in R.
Hypothesis Hv0Dv1 : v0 != v1.
Hypothesis Hv0Dv2 : v0 != v2.
Hypothesis Hv1Dv2 : v1 != v2.
Hypothesis Hv0v1 : v0 --> v1.
Hypothesis Hv1v2 : v1 --> v2.
Hypothesis Hv2next : forall s, s \in S -> v2 --> next c s.

Lemma c11_k7_bad_fourth_outneighbor q :
  q \in Bad ->
  exists z, [&& z \in R, q --> z, z != v0, z != v1 & z != v2].
Proof.
move=> qBad.
have qdeg : 4 <= outdeg_in R q.
  move: qBad.
  by rewrite /Bad /c11_k7_bad_endpoints inE => /andP[].
pose O : {set D} := [set z in R | q --> z].
have cardO : #|O| = outdeg_in R q by [].
have hcardO : 4 <= #|O| by rewrite cardO.
have cardprefix : #|[set v0; v1; v2]| = 3.
  by rewrite -setUA cardsU1 !inE negb_or Hv0Dv1 Hv0Dv2
             cards2 Hv1Dv2.
have Onsub : ~~ (O \subset [set v0; v1; v2]).
  apply/negP=> Osub.
  have Ole := subset_leq_card Osub.
  have himpossible := leq_trans hcardO Ole.
  by move: himpossible; rewrite cardprefix.
have /subsetPn[z zO zNprefix] := Onsub.
have zfacts : (z \in R) && (q --> z).
  by move: zO; rewrite /O inE.
have zDv0 : z != v0.
  apply/eqP=> zv0.
  by move: zNprefix; rewrite zv0 !inE eqxx.
have zDv1 : z != v1.
  apply/eqP=> zv1.
  by move: zNprefix; rewrite zv1 !inE eqxx orbT.
have zDv2 : z != v2.
  apply/eqP=> zv2.
  by move: zNprefix; rewrite zv2 !inE eqxx orbT.
have zdiff : [&& z != v0, z != v1 & z != v2].
  by rewrite zDv0 zDv1 zDv2.
exists z.
by case/andP: zfacts => -> ->; case/and3P: zdiff => -> -> ->.
Qed.

(** Three prefix arcs, an eleven-cycle Hamilton path, and a fourth outside
    out-neighbour produce a forbidden 14-arc dipath. *)
Lemma c11_k7_bad_hamilton_splice q start tail :
  q \in Bad -> start \in B ->
  c11_k7_hamilton_order c start tail q -> False.
Proof.
move=> qBad startB [hp lastq sizetail cover].
have [z /and5P[zR aqz zDv0 zDv1 zDv2]] :=
  c11_k7_bad_fourth_outneighbor qBad.
have v2start : v2 --> start.
  move: startB; rewrite /B /c11_k7_successor_set.
  move=> /imsetP[s sS ->].
  exact: Hv2next s sS.
have outside_omit z0 : z0 \in R -> z0 \notin start :: tail.
  move=> z0R; apply/negP=> z0P.
  have z0c : z0 \in c by move: z0P; rewrite (cover z0).
  have z0C : z0 \in C by move: z0c; rewrite /C /c11_k7_cycle_set inE.
  by move: z0R; rewrite /R /c11_k7_outside inE z0C.
have zNpath := outside_omit z zR.
have v2Npath := outside_omit v2 Hv2R.
have v1Npath := outside_omit v1 Hv1R.
have v0Npath := outside_omit v0 Hv0R.
have hpz : dipath start (rcons tail z).
  by rewrite dipath_rcons hp lastq aqz zNpath.
have v2Dz : v2 != z by rewrite eq_sym.
have v2Nfull : v2 \notin start :: rcons tail z.
  move: v2Npath.
  by rewrite !inE mem_rcons !negb_or v2Dz => ->.
have hp2 : dipath v2 (start :: rcons tail z).
  rewrite /dipath /= v2start (dipath_path hpz) v2Nfull.
  by have := dipath_uniq hpz.
have v1Dz : v1 != z by rewrite eq_sym.
have v1Nfull : v1 \notin v2 :: start :: rcons tail z.
  move: v1Npath.
  by rewrite !inE mem_rcons !negb_or Hv1Dv2 v1Dz => ->.
have hp1 : dipath v1 (v2 :: start :: rcons tail z).
  rewrite /dipath /= Hv1v2 v2start (dipath_path hpz)
          v1Nfull v2Nfull /=.
  have uz := dipath_uniq hpz.
  by move: uz; rewrite /=.
have v0Dz : v0 != z by rewrite eq_sym.
have v0Nfull : v0 \notin v1 :: v2 :: start :: rcons tail z.
  move: v0Npath.
  by rewrite !inE mem_rcons !negb_or Hv0Dv1 Hv0Dv2 v0Dz => ->.
have hp0 : dipath v0 (v1 :: v2 :: start :: rcons tail z).
  rewrite /dipath /= Hv0v1 Hv1v2 v2start (dipath_path hpz)
          v0Nfull v1Nfull v2Nfull /=.
  have uz := dipath_uniq hpz.
  by move: uz; rewrite /=.
have hlong := ell_max hp0.
move: hlong.
by rewrite /= size_rcons sizetail Hell.
Qed.

Theorem c11_k7_bad_no_hamilton q :
  q \in Bad -> ~ c11_k7_hamilton_from c B q.
Proof.
move=> qBad [start [tail [startB hham]]].
exact: c11_k7_bad_hamilton_splice qBad startB hham.
Qed.

Theorem c11_k7_hand_interface :
  [ /\ 3 <= #|Bad|
    & forall q, q \in Bad -> ~ c11_k7_hamilton_from c B q ].
Proof.
split.
- exact: c11_k7_bad_card_ge3.
- exact: c11_k7_bad_no_hamilton.
Qed.

End C11Hand.
