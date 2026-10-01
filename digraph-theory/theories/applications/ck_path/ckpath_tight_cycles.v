(** * Tight cycle-side eliminations for the small CK shapes *)

From HB Require Import structures.
From mathcomp Require Import all_boot.
From Digraph Require Import prelude digraph oriented dipath ckpath_cycle_tools.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section TightCycleTools.
Variable H : orientedDigraph.
Implicit Types (v z : H) (A B S : {set H}) (c : seq H).

Lemma outdeg_in_card_le A v : outdeg_in A v <= #|A|.
Proof.
apply: subset_leq_card; apply/subsetP=> z.
by rewrite !inE => /andP[].
Qed.

Lemma outdeg_in_full A v :
  outdeg_in A v = #|A| -> forall z, z \in A -> v --> z.
Proof.
move=> cardE z zA.
pose N := [set w in A | v --> w].
have sub : N \subset A.
  by apply/subsetP=> w; rewrite /N !inE => /andP[].
have cardNE : #|N| = #|A| by exact: cardE.
have eqNA : N = A.
  apply/eqP.
  rewrite eqEcard sub /=.
  by rewrite cardNE.
have : z \in N by rewrite eqNA.
by rewrite /N !inE => /andP[].
Qed.

Lemma outdeg_in_split_subset A B v :
  A \subset B ->
  outdeg_in B v = outdeg_in A v + outdeg_in (B :\: A) v.
Proof.
move=> subAB.
rewrite !outdeg_in_sumE (bigID (mem A)) /=.
congr (_ + _); apply: eq_bigl => z.
- case zA: (z \in A).
  have zB : z \in B by exact: (subsetP subAB z zA).
  by rewrite zB.
- by rewrite andbF.
- rewrite inE; exact: andbC _ _.
Qed.

(** Equality in the oriented arc bound forces a five-set to be complete
    toward the complementary cycle vertices.  The numerical equality is
    kept explicit so the same lemma covers the C8/k=5 and C9/k=6 rows. *)
Lemma tight_five_set_complete c S d n :
  dicycle c -> #|[set z in c]| = n ->
  S \subset [set z in c] -> #|S| = 5 ->
  (forall v, v \in S -> outdeg v = d) ->
  (forall v z, v \in S -> v --> z -> z \in c) ->
  5 * d = 10 + 5 * (n - 5) ->
  forall v z, v \in S -> z \in [set w in c] :\: S -> v --> z.
Proof.
move=> dc cardC Ssub cardS hreg closed tight.
set C : {set H} := [set z in c].
set Q : {set H} := C :\: S.
have cardQ : #|Q| = n - 5.
  rewrite /Q cardsD.
  have -> : C :&: S = S.
    exact: setIidPr Ssub.
  by rewrite /C cardC cardS.
have outC v : v \in S -> outdeg_in C v = d.
  move=> vS.
  rewrite -(hreg v vS).
  apply: eq_card => z; rewrite !inE /C.
  case avz: (v --> z); last by rewrite andbF.
  rewrite andbT.
  exact: closed v z vS avz.
pose I := \sum_(v in S) outdeg_in S v.
pose X := \sum_(v in S) outdeg_in Q v.
have splitCX : I + X = 5 * d.
  rewrite /I /X -big_split /=.
  under eq_bigr do rewrite -(@outdeg_in_split_subset S C _ Ssub).
  under eq_bigr do rewrite outC //.
  by rewrite sum_nat_const cardS mulnC.
have Ile10 : I <= 10.
  have hb := oriented_arcs_bound S.
  rewrite cardS /= in hb.
  rewrite -/I in hb.
  change (is_true (2 * I <= 20)) in hb.
  move: hb.
  by rewrite -[20]/(2 * 10) leq_pmul2l.
have Xle : X <= 5 * (n - 5).
  rewrite /X -cardQ -cardS -sum_nat_const.
  apply: leq_sum => v _.
  exact: outdeg_in_card_le.
have Xeq : X = 5 * (n - 5).
  apply/eqP; rewrite eqn_leq Xle andTb.
  have h : I + 5 * (n - 5) <= I + X.
    by rewrite splitCX tight leq_add2r.
  by move: h; rewrite leq_add2l.
move=> v z vS zQ.
apply: outdeg_in_full zQ.
apply/eqP; rewrite eqn_leq outdeg_in_card_le andTb.
rewrite leqNgt; apply/negP=> dvlt.
have cardSv : #|S :\ v| = 4.
  have h := cardsD1 v S.
  move: h; rewrite vS cardS /= add1n => h.
  have hp := congr1 predn h.
  move: hp; rewrite /= => hp.
  exact: esym hp.
have restle :
    \sum_(u in S :\ v) outdeg_in Q u <= 4 * #|Q|.
  rewrite -cardSv -sum_nat_const.
  apply: leq_sum => u _.
  exact: outdeg_in_card_le.
have Xsplit : X = outdeg_in Q v + \sum_(u in S :\ v) outdeg_in Q u.
  by rewrite /X (big_setD1 v vS).
have Xlt : X < 5 * #|Q|.
  rewrite Xsplit.
  apply: leq_ltn_trans (leq_add (leqnn _) restle) _.
  rewrite -[5]/4.+1 mulSn.
  by rewrite ltn_add2r.
move: Xlt.
by rewrite Xeq cardQ ltnn.
Qed.

Lemma tight_cycle_no_proper_Q c S d n :
  dicycle c -> #|[set z in c]| = n ->
  S \subset [set z in c] -> #|S| = 5 ->
  0 < n - 5 -> n - 5 < n ->
  (forall v, v \in S -> outdeg v = d) ->
  (forall v z, v \in S -> v --> z -> z \in c) ->
  5 * d = 10 + 5 * (n - 5) -> False.
Proof.
move=> dc cardC Ssub cardS qpos qproper hreg closed tight.
set C : {set H} := [set z in c].
set Q : {set H} := C :\: S.
have cardQ : #|Q| = n - 5.
  rewrite /Q cardsD.
  have -> : C :&: S = S.
    exact: setIidPr Ssub.
  by rewrite /C cardC cardS.
have complete := tight_five_set_complete dc cardC Ssub cardS hreg closed tight.
have Qn0 : Q != set0 by rewrite -card_gt0 cardQ.
have Qsub : Q \subset C.
  by apply/subsetP=> z; rewrite /Q !inE => /andP[_ zC].
have Qclosed : forall q, q \in Q -> next c q \in Q.
  move=> q qQ.
  have qC : q \in c.
    have qCinC : q \in C := subsetP Qsub q qQ.
    by move: qCinC; rewrite /C inE.
  have nqC : next c q \in c by rewrite mem_next.
  case nqS : (next c q \in S).
  - exfalso.
    have qQ' : q \in [set w in c] :\: S.
      by move: qQ; rewrite /Q /C.
    have sq : next c q --> q := complete (next c q) q nqS qQ'.
    have qs : q --> next c q := dicycle_next dc qC.
    by move: (arc_asymm _ _ qs); rewrite sq.
  - by rewrite /Q /C !inE nqS nqC.
have eqQC : Q = C.
  exact: next_closed_dicycle dc Qn0 Qsub Qclosed.
have hcardEq : #|Q| = #|C| by rewrite eqQC.
move: hcardEq; rewrite cardQ /C cardC => eqn.
by have := qproper; rewrite eqn ltnn.
Qed.

Lemma no_tight_cycle8_five_set c S :
  dicycle c -> size c = 8 ->
  S \subset [set z in c] -> #|S| = 5 ->
  (forall v, v \in S -> outdeg v = 5) ->
  (forall v z, v \in S -> v --> z -> z \in c) -> False.
Proof.
move=> dc sizeC Ssub cardS hreg closed.
have cardC : #|[set z in c]| = 8.
  by rewrite (dicycle_set_card dc) sizeC.
apply: (tight_cycle_no_proper_Q dc cardC Ssub cardS _ _ hreg closed).
- by [].
- by [].
- by [].
Qed.

Lemma no_tight_cycle9_five_set c S :
  dicycle c -> size c = 9 ->
  S \subset [set z in c] -> #|S| = 5 ->
  (forall v, v \in S -> outdeg v = 6) ->
  (forall v z, v \in S -> v --> z -> z \in c) -> False.
Proof.
move=> dc sizeC Ssub cardS hreg closed.
have cardC : #|[set z in c]| = 9.
  by rewrite (dicycle_set_card dc) sizeC.
apply: (tight_cycle_no_proper_Q dc cardC Ssub cardS _ _ hreg closed).
- by [].
- by [].
- by [].
Qed.

End TightCycleTools.
