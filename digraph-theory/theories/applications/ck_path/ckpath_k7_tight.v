(** * Tight cycle-side eliminations needed at out-degree seven *)

From HB Require Import structures.
From mathcomp Require Import all_boot zify.
From Stdlib Require Import Lia.
From Digraph Require Import prelude digraph oriented dipath
  ckpath_cycle_tools ckpath_tight_cycles.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section K7Tight.
Variable H : orientedDigraph.
Implicit Types (v z : H) (S : {set H}) (c : seq H).

(** If every selected cycle vertex dominates every complementary cycle
    vertex, the complement is successor-closed.  A nonempty proper such
    subset cannot occur on a directed cycle. *)
Lemma complete_complement_no_dicycle c S :
  dicycle c -> S \subset [set z in c] ->
  (forall v z, v \in S -> z \in [set w in c] :\: S -> v --> z) ->
  [set z in c] :\: S != set0 ->
  #|[set z in c] :\: S| < #|[set z in c]| -> False.
Proof.
move=> dc Ssub complete Qn0 Qproper.
set C : {set H} := [set z in c].
set Q : {set H} := C :\: S.
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
    have sq : next c q --> q := complete _ _ nqS qQ'.
    have qs : q --> next c q := dicycle_next dc qC.
    by move: (arc_asymm _ _ qs); rewrite sq.
  - by rewrite /Q /C !inE nqS nqC.
have QC : Q = C := next_closed_dicycle dc Qn0 Qsub Qclosed.
have qp : #|Q| < #|C|.
  by move: Qproper; rewrite /Q /C.
by move: qp; rewrite QC ltnn.
Qed.

Lemma no_tight_cycle10_five_set c S :
  dicycle c -> size c = 10 ->
  S \subset [set z in c] -> #|S| = 5 ->
  (forall v, v \in S -> outdeg v = 7) ->
  (forall v z, v \in S -> v --> z -> z \in c) -> False.
Proof.
move=> dc sizeC Ssub cardS hreg closed.
have cardC : #|[set z in c]| = 10.
  by rewrite (dicycle_set_card dc) sizeC.
have complete :
    forall v z, v \in S -> z \in [set w in c] :\: S -> v --> z.
  apply: (tight_five_set_complete dc cardC Ssub cardS hreg closed).
  by [].
apply: (complete_complement_no_dicycle dc Ssub complete).
- rewrite -card_gt0 cardsD (setIidPr Ssub) cardC cardS.
  by [].
- rewrite cardsD (setIidPr Ssub) cardC cardS.
  by [].
Qed.

(** Equality in the oriented arc bound for seven selected vertices on an
    eleven-cycle forces all 7*4 selected-to-complement arcs. *)
Lemma tight_seven_set_complete c S :
  dicycle c -> #|[set z in c]| = 11 ->
  S \subset [set z in c] -> #|S| = 7 ->
  (forall v, v \in S -> outdeg v = 7) ->
  (forall v z, v \in S -> v --> z -> z \in c) ->
  forall v z, v \in S -> z \in [set w in c] :\: S -> v --> z.
Proof.
move=> dc cardC Ssub cardS hreg closed.
set C : {set H} := [set z in c].
set Q : {set H} := C :\: S.
have cardQ : #|Q| = 4.
  rewrite /Q cardsD.
  have -> : C :&: S = S := setIidPr Ssub.
  by rewrite /C cardC cardS.
have outC v : v \in S -> outdeg_in C v = 7.
  move=> vS.
  rewrite -(hreg v vS).
  apply: eq_card => z; rewrite !inE /C.
  case avz: (v --> z); last by rewrite andbF.
  rewrite andbT.
  exact: closed v z vS avz.
pose I := \sum_(v in S) outdeg_in S v.
pose X := \sum_(v in S) outdeg_in Q v.
have splitCX : I + X = 49.
  rewrite /I /X -big_split /=.
  under eq_bigr do rewrite -(@outdeg_in_split_subset H S C _ Ssub).
  under eq_bigr do rewrite outC //.
  by rewrite sum_nat_const cardS.
have Ile21 : I <= 21.
  have hb := oriented_arcs_bound S.
  rewrite cardS /= in hb.
  rewrite -/I in hb.
  change (is_true (2 * I <= 42)) in hb.
  move: hb.
  by rewrite -[42]/(2 * 21) leq_pmul2l.
have Xle : X <= #|S| * #|Q|.
  rewrite /X -sum_nat_const.
  apply: leq_sum => v _.
  exact: (@outdeg_in_card_le H Q v).
have Xle28 : X <= 28 by move: Xle; rewrite cardS cardQ.
have Xeq28 : X = 28 by lia.
move=> v z vS zQ.
apply: outdeg_in_full zQ.
apply/eqP; rewrite eqn_leq outdeg_in_card_le andTb.
rewrite cardQ leqNgt; apply/negP=> dvlt.
have cardSv : #|S :\ v| = 6.
  have h := cardsD1 v S.
  move: h; rewrite vS cardS /= add1n => h.
  have hp := congr1 predn h.
  move: hp; rewrite /= => hp.
  exact: esym hp.
have restle :
    \sum_(u in S :\ v) outdeg_in Q u <= 6 * #|Q|.
  rewrite -cardSv -sum_nat_const.
  apply: leq_sum => u _.
  exact: (@outdeg_in_card_le H Q u).
have Xsplit : X = outdeg_in Q v + \sum_(u in S :\ v) outdeg_in Q u.
  by rewrite /X (big_setD1 v vS).
have Xlt : X < 28.
  rewrite Xsplit.
  have qvlt : outdeg_in Q v < 4 by exact: dvlt.
  rewrite cardQ in restle.
  lia.
by move: Xlt; rewrite Xeq28 ltnn.
Qed.

Lemma no_tight_cycle11_seven_set c S :
  dicycle c -> size c = 11 ->
  S \subset [set z in c] -> #|S| = 7 ->
  (forall v, v \in S -> outdeg v = 7) ->
  (forall v z, v \in S -> v --> z -> z \in c) -> False.
Proof.
move=> dc sizeC Ssub cardS hreg closed.
have cardC : #|[set z in c]| = 11.
  by rewrite (dicycle_set_card dc) sizeC.
have complete :
    forall v z, v \in S -> z \in [set w in c] :\: S -> v --> z.
  exact: (tight_seven_set_complete dc cardC Ssub cardS hreg closed).
apply: (complete_complement_no_dicycle dc Ssub complete).
- rewrite -card_gt0 cardsD (setIidPr Ssub) cardC cardS.
  by [].
- rewrite cardsD (setIidPr Ssub) cardC cardS.
  by [].
Qed.

End K7Tight.
