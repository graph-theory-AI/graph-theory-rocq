(** * Hand splice for the CK seven-outregular C12, a=2 shape

    A cycle vertex of internal out-degree at most four has at least three
    out-neighbours outside the cycle.  Two of those vertices may be the CK
    prefix, but a third one is fresh.  It can be appended to a Hamilton
    ordering of the cycle while the prefix is prepended, producing a
    forbidden fourteen-arc directed path. *)

From HB Require Import structures.
From mathcomp Require Import all_boot zify.
From Stdlib Require Import Lia.
From Digraph Require Import
  prelude digraph oriented dipath ckpath_cycle_tools ckpath_even_gateway
  ckpath_kernel_prefix_adapters.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Definitions.
Variable D : diGraphType.

Definition c12_k7_low_endpoints (c : seq D) : {set D} :=
  [set q in ckpath_cycle_set c |
     outdeg_in (ckpath_outside c) q >= 3].

Definition c12_k7_hamilton_order
    (c : seq D) (start : D) (tail : seq D) (endpoint : D) : Prop :=
  [ /\ dipath start tail,
      last start tail = endpoint,
      size tail = 11
    & forall z, (z \in start :: tail) = (z \in c) ].

Definition c12_k7_hamilton_from
    (c : seq D) (B : {set D}) (endpoint : D) : Prop :=
  exists start tail,
    start \in B /\ c12_k7_hamilton_order c start tail endpoint.

End Definitions.

Section C12LowHand.
Variable D : orientedDigraph.
Variables (c : seq D) (S : {set D}) (v0 v1 : D).

Hypothesis Hreg : forall v : D, outdeg v = 7.
Hypothesis Hell : ell D = 13.
Hypothesis Hprefix : ckpath_prefix2_data c S v0 v1.

Local Notation C := (ckpath_cycle_set c).
Local Notation R := (ckpath_outside c).
Local Notation Q := (C :\: S).
Local Notation Low := (c12_k7_low_endpoints c).
Local Notation B := (ckpath_successor_set c S).

(** The degree formulation used by the finite CNF is equivalent, in the
    seven-outregular graph, to having at least three outside neighbours. *)
Lemma c12_k7_internal_low_outside_ge3 q :
  q \in C -> outdeg_in C q <= 4 -> 3 <= outdeg_in R q.
Proof.
move=> _ qlow.
have hsplit := outdeg_split_set C q.
rewrite Hreg in hsplit.
change (7 = outdeg_in C q + outdeg_in R q) in hsplit.
have h := leq_add qlow (leqnn (outdeg_in R q)).
rewrite -hsplit in h.
move: h.
by rewrite -[7]/(4 + 3) leq_add2l.
Qed.

Lemma c12_k7_low_endpointP q :
  q \in Low = ((q \in C) && (outdeg_in C q <= 4)).
Proof.
rewrite /Low /c12_k7_low_endpoints inE.
case qC: (q \in C); last by [].
have hsplit := outdeg_split_set C q.
rewrite Hreg in hsplit.
change (7 = outdeg_in C q + outdeg_in R q) in hsplit.
apply/idP/idP.
- move=> qout.
  have h := leq_add (leqnn (outdeg_in C q)) qout.
  rewrite -hsplit in h.
  move: h.
  by rewrite -[7]/(4 + 3) leq_add2r.
- exact: c12_k7_internal_low_outside_ge3 qC.
Qed.

(** A row of internal out-degree one has a unique out-neighbour in the
    cycle.  Keeping this elementary cardinality fact local avoids turning
    the equality case below into a tournament-structure conversion. *)
Lemma c12_k7_one_internal_outneighbor q u w :
  outdeg_in C q = 1 ->
  u \in C -> w \in C -> q --> u -> q --> w -> u = w.
Proof.
move=> qdeg uC wC aqu aqw.
case: (eqVneq u w) => // uDw.
pose O : {set D} := [set z in C | q --> z].
have pairsub : [set u; w] \subset O.
  apply/subsetP=> z.
  move/set2P=> [->|->].
  - by rewrite /O inE uC aqu.
  - by rewrite /O inE wC aqw.
have hcard := subset_leq_card pairsub.
have paircard : #|[set u; w]| = 2 by rewrite cards2 uDw.
rewrite paircard in hcard.
have hO : #|O| = outdeg_in C q by rewrite /O /outdeg_in.
by move: hcard; rewrite hO qdeg.
Qed.

(** Delete one internal vertex of a path using a shortcut, then append that
    vertex at the other end.  The new vertex list is only a permutation of
    the old one, so simplicity is preserved. *)
Lemma c12_k7_skip_append_dipath
    (x : D) (a : seq D) (q r : D) (b : seq D) :
  dipath x (a ++ q :: r :: b) ->
  last x a --> r -> last r b --> q ->
  dipath x (a ++ r :: rcons b q).
Proof.
move=> /andP[hp up] har hrq.
apply/andP; split.
- have /and4P[hpa _ _ hrb] :
      [&& path arc x a, last x a --> q, q --> r & path arc r b].
    by move: hp; rewrite cat_path /=.
  by rewrite cat_path /= hpa har rcons_path hrb hrq.
- have hperm :
      perm_eq (x :: (a ++ r :: rcons b q))
              (x :: (a ++ q :: r :: b)).
    rewrite perm_cons perm_cat2l -cats1.
    by rewrite -cat_cons -cat1s perm_catC.
  by rewrite (perm_uniq hperm).
Qed.

(** A low endpoint has an outside out-neighbour different from both prefix
    vertices.  This is the exact fresh vertex needed by the splice. *)
Theorem c12_k7_low_fresh_outneighbor q :
  q \in Low ->
  exists z, [&& z \in R, q --> z, z != v0 & z != v1].
Proof.
move=> qLow.
have qdeg : 3 <= outdeg_in R q.
  move: qLow.
  by rewrite /Low /c12_k7_low_endpoints inE => /andP[].
pose O : {set D} := [set z in R | q --> z].
have cardO : #|O| = outdeg_in R q by [].
have hcardO : 3 <= #|O| by rewrite cardO.
have v0Dv1 : v0 != v1 := prefix2_distinct Hprefix.
have Onsub : ~~ (O \subset [set v0; v1]).
  apply/negP=> Osub.
  have Ole := subset_leq_card Osub.
  have paircard : #|[set v0; v1]| = 2 by rewrite cards2 v0Dv1.
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

(** Prepending the two CK prefix vertices and appending the fresh outside
    neighbour turns a Hamilton ordering of C12 into a fourteen-arc path. *)
Lemma c12_k7_low_hamilton_splice q start tail :
  q \in Low -> start \in B ->
  c12_k7_hamilton_order c start tail q -> False.
Proof.
move=> qLow startB [hp lastq sizetail cover].
have [z /and4P[zR aqz zDv0 zDv1]] :=
  c12_k7_low_fresh_outneighbor qLow.
have v0R : v0 \in R := prefix2_v0_outside Hprefix.
have v1R : v1 \in R := prefix2_v1_outside Hprefix.
have v0Dv1 : v0 != v1 := prefix2_distinct Hprefix.
have v0v1 : v0 --> v1 := prefix2_arc Hprefix.
have v1start : v1 --> start.
  move: startB; rewrite /B /ckpath_successor_set.
  move=> /imsetP[s sS ->].
  exact: prefix2_next Hprefix s sS.
have outside_omit z0 : z0 \in R -> z0 \notin start :: tail.
  move=> z0R; apply/negP=> z0P.
  have z0c : z0 \in c by move: z0P; rewrite (cover z0).
  have z0C : z0 \in C by move: z0c; rewrite /C /ckpath_cycle_set inE.
  by move: z0R; rewrite /R /ckpath_outside inE z0C.
have zNpath := outside_omit z zR.
have v1Npath := outside_omit v1 v1R.
have v0Npath := outside_omit v0 v0R.
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
  by rewrite !inE mem_rcons !negb_or v0Dv1 v0Dz => ->.
have hp0 : dipath v0 (v1 :: start :: rcons tail z).
  rewrite /dipath /= v0v1 v1start (dipath_path hpz)
          v0Nfull v1Nfull /=.
  have uz := dipath_uniq hpz.
  by move: uz; rewrite /=.
have hlong := ell_max hp0.
move: hlong.
by rewrite /= size_rcons sizetail Hell.
Qed.

Theorem c12_k7_low_no_hamilton q :
  q \in Low -> ~ c12_k7_hamilton_from c B q.
Proof.
move=> qLow [start [tail [startB hham]]].
exact: c12_k7_low_hamilton_splice qLow startB hham.
Qed.

Section LowCounting.

Hypothesis Hcycle : dicycle c.
Hypothesis Hcsize : size c = 12.
Hypothesis HScard : #|S| = 7.

Lemma c12_k7_low_cycle_card : #|C| = 12.
Proof.
by rewrite /C /ckpath_cycle_set (dicycle_set_card Hcycle) Hcsize.
Qed.

Lemma c12_k7_low_complement_card : #|Q| = 5.
Proof.
have SsubC : S \subset C := prefix2_S_subset Hprefix.
rewrite /Q cardsD (setIidPr SsubC) c12_k7_low_cycle_card HScard.
by [].
Qed.

Lemma c12_k7_low_selected_internal_eq7 s :
  s \in S -> outdeg_in C s = 7.
Proof.
move=> sS.
rewrite /outdeg_in -[RHS](Hreg s) /outdeg.
apply: eq_card => z; rewrite !inE andb_idl //.
move=> asz.
have zC := @prefix2_S_closed D c S v0 v1 Hprefix s z sS asz.
move: zC.
by rewrite /ckpath_cycle_set inE.
Qed.

Lemma c12_k7_low_selected_internal_sum :
  \sum_(s in S) outdeg_in C s = 49.
Proof.
under eq_bigr do rewrite c12_k7_low_selected_internal_eq7 //.
by rewrite sum_nat_const HScard.
Qed.

Lemma c12_k7_low_cycle_internal_upper :
  \sum_(q in C) outdeg_in C q <= 66.
Proof.
have h := oriented_arcs_bound C.
rewrite c12_k7_low_cycle_card /= in h.
have h' : (\sum_(q in C) outdeg_in C q).*2 <= 66.*2.
  move: h.
  by rewrite mul2n.
move: h'.
by rewrite leq_double.
Qed.

Lemma c12_k7_low_cycle_internal_partition :
  \sum_(q in C) outdeg_in C q =
    \sum_(s in S) outdeg_in C s +
    \sum_(q in Q) outdeg_in C q.
Proof.
have SsubC : S \subset C := prefix2_S_subset Hprefix.
rewrite (bigID (mem S)) /=.
have firstE :
    \sum_(q in C | q \in S) outdeg_in C q =
    \sum_(q in S) outdeg_in C q.
  apply: eq_bigl => q.
  case qS: (q \in S).
  - have qC := subsetP SsubC q qS.
    by rewrite qC.
  - by rewrite andbF.
have secondE :
    \sum_(q in C | q \notin S) outdeg_in C q =
    \sum_(q in Q) outdeg_in C q.
  apply: eq_bigl => q.
  rewrite /Q !inE.
  by rewrite andbC.
by rewrite firstE secondE.
Qed.

Lemma c12_k7_low_complement_internal_upper :
  \sum_(q in Q) outdeg_in C q <= 17.
Proof.
have hup := c12_k7_low_cycle_internal_upper.
rewrite c12_k7_low_cycle_internal_partition
        c12_k7_low_selected_internal_sum in hup.
move: hup.
by rewrite -[66]/(49 + 17) leq_add2l.
Qed.

Lemma c12_k7_low_complement_degree_balance :
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
by rewrite sum_nat_const c12_k7_low_complement_card.
Qed.

Lemma c12_k7_low_cross_lower :
  18 <= \sum_(q in Q) outdeg_in R q.
Proof.
have hbal := c12_k7_low_complement_degree_balance.
have hup := c12_k7_low_complement_internal_upper.
change (35 - 17 <= \sum_(q in Q) outdeg_in R q).
rewrite leq_subLR // -hbal leq_add2r.
exact: hup.
Qed.

Lemma c12_k7_low_outside_cap6 q :
  q \in Q -> outdeg_in R q <= 6.
Proof.
move=> qQ.
have qc : q \in c.
  move: qQ.
  by rewrite /Q /C /ckpath_cycle_set !inE => /andP[].
have nqc0 : next c q \in c by rewrite mem_next.
have nqc : next c q \in C.
  by move: nqc0; rewrite /C /ckpath_cycle_set inE.
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

Lemma c12_k7_low_subset_complement : Low \subset Q.
Proof.
apply/subsetP=> q qLow.
have /andP[qC qout] : (q \in C) && (3 <= outdeg_in R q).
  by move: qLow; rewrite /Low /c12_k7_low_endpoints inE.
rewrite /Q inE qC andbT.
apply/negP=> qS.
have qin := c12_k7_low_selected_internal_eq7 qS.
have split := outdeg_split_set C q.
rewrite Hreg qin in split.
have qout0 : outdeg_in (~: C) q = 0.
  have hzero : 7 + outdeg_in (~: C) q = 7 + 0.
    by rewrite addn0 -split.
  by move/addnI: hzero.
move: qout.
by rewrite /R /ckpath_outside qout0.
Qed.

Lemma c12_k7_low_nonlow_outside_cap2 q :
  q \in Q -> q \notin Low -> outdeg_in R q <= 2.
Proof.
move=> qQ qNLow.
have qC : q \in C.
  by move: qQ; rewrite /Q !inE => /andP[].
move: qNLow.
rewrite /Low /c12_k7_low_endpoints inE qC /= => qlowF.
by rewrite leqNgt qlowF.
Qed.

Lemma c12_k7_low_indicator_sum :
  \sum_(q in Q) ((q \in Low) : nat) = #|Low|.
Proof.
have LowSub := c12_k7_low_subset_complement.
rewrite -sum1dep_card big_mkcond [RHS]big_mkcond /=.
apply: eq_bigr => q _.
case qLow: (q \in Low).
- have qQ := subsetP LowSub q qLow.
  have /andP[qC qout] :
      (q \in C) && (3 <= outdeg_in R q).
    by move: qLow; rewrite /Low /c12_k7_low_endpoints inE.
  by rewrite qQ qC qout.
- have qcond : ((q \in C) && (3 <= outdeg_in R q)) = false.
    by move: qLow; rewrite /Low /c12_k7_low_endpoints inE.
  by rewrite qcond; case: (q \in Q).
Qed.

Lemma c12_k7_low_cross_upper :
  \sum_(q in Q) outdeg_in R q <= 2 * #|Q| + 4 * #|Low|.
Proof.
apply: leq_trans
  (_ : \sum_(q in Q) (2 + 4 * ((q \in Low) : nat)) <= _).
- apply: leq_sum => q qQ.
  case qLow: (q \in Low).
  + rewrite /=.
    exact: c12_k7_low_outside_cap6 qQ.
  + rewrite /= addn0.
    have qNLow : q \notin Low by rewrite qLow.
    exact: c12_k7_low_nonlow_outside_cap2 qQ qNLow.
- rewrite big_split /= sum_nat_const.
  rewrite -big_distrr c12_k7_low_indicator_sum mulnC.
  by [].
Qed.

Lemma c12_k7_low_card_ge2 : 2 <= #|Low|.
Proof.
rewrite leqNgt; apply/negP=> hsmall.
have hlo := c12_k7_low_cross_lower.
have hup := c12_k7_low_cross_upper.
have hLow1 : #|Low| <= 1 by move: hsmall; rewrite ltnS.
have hmul : 4 * #|Low| <= 4 * 1 by rewrite leq_pmul2l.
have hrhs : 2 * #|Q| + 4 * #|Low| <= 14.
  rewrite c12_k7_low_complement_card.
  apply: leq_trans (leq_add (leqnn (2 * 5)) hmul) _.
  by [].
have hcross := leq_trans hup hrhs.
have himpossible := leq_trans hlo hcross.
by move: himpossible.
Qed.

Lemma c12_k7_low_internal_lower1 q :
  q \in Low -> 1 <= outdeg_in C q.
Proof.
move=> qLow.
have qC : q \in C.
  by move: qLow; rewrite c12_k7_low_endpointP => /andP[].
have qc : q \in c by move: qC; rewrite /C /ckpath_cycle_set inE.
have nqc0 : next c q \in c by rewrite mem_next.
have nqc : next c q \in C.
  by move: nqc0; rewrite /C /ckpath_cycle_set inE.
have aqn : q --> next c q := dicycle_next Hcycle qc.
rewrite /outdeg_in card_gt0.
apply/set0Pn; exists (next c q).
by rewrite inE nqc aqn.
Qed.

Lemma c12_k7_low_nonlow_internal_lower5 q :
  q \in Q -> q \notin Low -> 5 <= outdeg_in C q.
Proof.
move=> qQ qNLow.
have qcap := c12_k7_low_nonlow_outside_cap2 qQ qNLow.
have split := outdeg_split_set C q.
rewrite Hreg in split.
have h := leq_add (leqnn (outdeg_in C q)) qcap.
rewrite -split in h.
move: h.
by rewrite -[7]/(5 + 2) leq_add2r.
Qed.

Lemma c12_k7_low_high_card (Hcard : #|Low| = 2) :
  #|Q :\: Low| = 3.
Proof.
have LowSub := c12_k7_low_subset_complement.
rewrite cardsD (setIidPr LowSub) c12_k7_low_complement_card Hcard.
by [].
Qed.

Lemma c12_k7_low_internal_partition :
  \sum_(q in Q) outdeg_in C q =
    \sum_(q in Low) outdeg_in C q +
    \sum_(q in Q :\: Low) outdeg_in C q.
Proof.
have LowSub := c12_k7_low_subset_complement.
rewrite (bigID (mem Low)) /=.
have firstE :
    \sum_(q in Q | q \in Low) outdeg_in C q =
    \sum_(q in Low) outdeg_in C q.
  apply: eq_bigl => q.
  case qLow: (q \in Low).
  - have qQ := subsetP LowSub q qLow.
    by rewrite qQ.
  - by rewrite andbF.
have secondE :
    \sum_(q in Q | q \notin Low) outdeg_in C q =
    \sum_(q in Q :\: Low) outdeg_in C q.
  apply: eq_bigl => q.
  rewrite !inE.
  by rewrite andbC.
by rewrite firstE secondE.
Qed.

Lemma c12_k7_low_complement_internal_eq17
    (Hcard : #|Low| = 2) :
  \sum_(q in Q) outdeg_in C q = 17.
Proof.
have lowLower : 2 <= \sum_(q in Low) outdeg_in C q.
  have h : \sum_(q in Low) 1 <= \sum_(q in Low) outdeg_in C q.
    apply: leq_sum => q qLow.
    exact: c12_k7_low_internal_lower1 qLow.
  by move: h; rewrite sum_nat_const Hcard.
have highLower : 15 <= \sum_(q in Q :\: Low) outdeg_in C q.
  have h : \sum_(q in Q :\: Low) 5 <=
      \sum_(q in Q :\: Low) outdeg_in C q.
    apply: leq_sum => q.
    rewrite inE => /andP[qNLow qQ].
    apply: c12_k7_low_nonlow_internal_lower5.
    - exact qQ.
    - exact qNLow.
  move: h.
  by rewrite sum_nat_const (c12_k7_low_high_card Hcard).
have qLower : 17 <= \sum_(q in Q) outdeg_in C q.
  rewrite c12_k7_low_internal_partition.
  exact: leq_trans (leq_add lowLower highLower) (leqnn _).
have qUpper := c12_k7_low_complement_internal_upper.
apply/eqP.
by rewrite eqn_leq qUpper qLower.
Qed.

Lemma c12_k7_low_internal_sum_eq2 (Hcard : #|Low| = 2) :
  \sum_(q in Low) outdeg_in C q = 2.
Proof.
have highLower : 15 <= \sum_(q in Q :\: Low) outdeg_in C q.
  have h : \sum_(q in Q :\: Low) 5 <=
      \sum_(q in Q :\: Low) outdeg_in C q.
    apply: leq_sum => q.
    rewrite inE => /andP[qNLow qQ].
    apply: c12_k7_low_nonlow_internal_lower5.
    - exact qQ.
    - exact qNLow.
  move: h.
  by rewrite sum_nat_const (c12_k7_low_high_card Hcard).
have lowLower : 2 <= \sum_(q in Low) outdeg_in C q.
  have h : \sum_(q in Low) 1 <= \sum_(q in Low) outdeg_in C q.
    apply: leq_sum => q qLow.
    exact: c12_k7_low_internal_lower1 qLow.
  by move: h; rewrite sum_nat_const Hcard.
have qsum := c12_k7_low_complement_internal_eq17 Hcard.
have qpart := c12_k7_low_internal_partition.
have lowUpper : \sum_(q in Low) outdeg_in C q <= 2 by nia.
apply/eqP.
by rewrite eqn_leq lowUpper lowLower.
Qed.

Lemma c12_k7_low_internal_eq1 (Hcard : #|Low| = 2) q :
  q \in Low -> outdeg_in C q = 1.
Proof.
move=> qLow.
have qLower : 1 <= outdeg_in C q :=
  c12_k7_low_internal_lower1 qLow.
have restcard : #|Low :\ q| = 1.
  have h := cardsD1 q Low.
  move: h; rewrite qLow Hcard /= add1n => h.
  have hp := congr1 predn h.
  move: hp; rewrite /= => hp.
  exact: esym hp.
have restLower : 1 <= \sum_(u in Low :\ q) outdeg_in C u.
  have h : \sum_(u in Low :\ q) 1 <=
      \sum_(u in Low :\ q) outdeg_in C u.
    apply: leq_sum => u.
    rewrite inE => /andP[_ uLow].
    exact: c12_k7_low_internal_lower1 uLow.
  by move: h; rewrite sum_nat_const restcard.
have sumsplit :
    \sum_(u in Low) outdeg_in C u =
      outdeg_in C q + \sum_(u in Low :\ q) outdeg_in C u.
  by rewrite (big_setD1 q qLow).
have lowsum := c12_k7_low_internal_sum_eq2 Hcard.
have qUpper : outdeg_in C q <= 1 by nia.
apply/eqP.
by rewrite eqn_leq qUpper qLower.
Qed.

Lemma c12_k7_low_cycle_internal_eq66 (Hcard : #|Low| = 2) :
  \sum_(q in C) outdeg_in C q = 66.
Proof.
rewrite c12_k7_low_cycle_internal_partition
        c12_k7_low_selected_internal_sum
        (c12_k7_low_complement_internal_eq17 Hcard).
by [].
Qed.

Lemma c12_k7_low_cycle_remove_card u :
  u \in C -> #|C :\ u| = 11.
Proof.
move=> uC.
have h := cardsD1 u C.
move: h; rewrite uC c12_k7_low_cycle_card /= add1n => h.
have hp := congr1 predn h.
move: hp; rewrite /= => hp.
exact: esym hp.
Qed.

(** Equality in the oriented arc bound makes the cycle projection total. *)
Lemma c12_k7_low_cycle_total (Hcard : #|Low| = 2) u w :
  u \in C -> w \in C -> u != w -> (u --> w) || (w --> u).
Proof.
move=> uC wC uDw.
case auw: (u --> w) => //.
case awu: (w --> u) => //.
exfalso.
have uCw : u \in (C :\ w).
  rewrite !inE.
  have uc : u \in c.
    by move: uC; rewrite /C /ckpath_cycle_set inE.
  by rewrite uDw uc.
have cardCwu : #|(C :\ w) :\ u| = 10.
  have h := cardsD1 u (C :\ w).
  move: h; rewrite uCw (c12_k7_low_cycle_remove_card wC) /= add1n => h.
  have hp := congr1 predn h.
  move: hp; rewrite /= => hp.
  exact: esym hp.
have rowu : \sum_(z in C) ((u --> z) + (z --> u)) <= 10.
  rewrite (big_setD1 w wC) /= auw awu.
  have h := even_pair_sum_bound (C :\ w) u.
  by rewrite cardCwu in h.
have rows_rest :
    \sum_(x in C :\ u) \sum_(z in C) ((x --> z) + (z --> x))
      <= 11 * 11.
  rewrite -{1}(c12_k7_low_cycle_remove_card uC) -sum_nat_const.
  apply: leq_sum => x.
  rewrite inE => /andP[_ xC].
  have h := even_pair_sum_bound C x.
  by rewrite (c12_k7_low_cycle_remove_card xC) in h.
have total_le :
    \sum_(x in C) \sum_(z in C) ((x --> z) + (z --> x)) <= 131.
  rewrite (big_setD1 u uC) /=.
  apply: leq_trans (leq_add rowu rows_rest) _.
  by [].
have hd := even_double_internal C.
rewrite (c12_k7_low_cycle_internal_eq66 Hcard) /= in hd.
move: total_le; rewrite -hd.
by [].
Qed.

End LowCounting.

(** The bridge consumes both the degree characterization and the Hamilton
    obstruction from this small interface. *)
Theorem c12_k7_low_hand_interface :
  [ /\ (forall q, q \in Low =
          ((q \in C) && (outdeg_in C q <= 4)))
    & forall q, q \in Low -> ~ c12_k7_hamilton_from c B q ].
Proof.
split.
- exact: c12_k7_low_endpointP.
- exact: c12_k7_low_no_hamilton.
Qed.

End C12LowHand.
