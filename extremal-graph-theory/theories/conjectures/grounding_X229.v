(** * Extremal.conjectures.grounding_X229 -- grounding lemmas for wave X229.

    For [expander_proper_colouring_two_connected_palettes_statement] this file
    records, for each of the three guards of the statement,
    (i)  a NON-VACUITY witness and
    (ii) a GUARD-HAS-TEETH lemma,
    plus the source's own observation that no one-vertex graph is a robust
    sublinear expander (arXiv:2309.04460, remark after Definition 3.1).

    Everything is closed by [Qed]; see the [Print Assumptions] audit at the end. *)

From GTBase Require Import base.
From Extremal.foundations Require Import edge_colourings.
From Extremal.conjectures Require Import X229.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** The expander guard *)

(** The source's own remark: for eps = 1 and U = V(G) the condition fails on a
    one-vertex graph, since the external neighbourhood of the whole vertex set is
    empty.  So the guard has teeth. *)
Lemma not_rse_K1 : ~ x229_robust_sublinear_expander 'K_1.
Proof.
move=> /(_ 1 1 [set: 'K_1] set0 isT (leqnn 1)).
rewrite cardsT card_ord subnn expn1 expn0 cards0 muln0 muln1 sub0set.
move=> /(_ isT (leqnn 1) isT (leq0n _)).
by rewrite /x229_ext_neigh setDT cards0 muln0.
Qed.

(** NON-VACUITY: the single edge IS a robust sublinear expander.  Either eps = 0
    (nothing to prove), or |U| = 1 and no edge may be deleted, and the other
    vertex is then an external neighbour. *)
Lemma rse_K2 : x229_robust_sublinear_expander 'K_2.
Proof.
move=> a b U F b0 ab U0 Hsize _ Hedges.
case: (posnP a) => [->|a0]; first by rewrite mul0n.
have cK2 : #|'K_2| = 2 by rewrite card_ord.
have cEK2 : #|E('K_2)| = 1 by rewrite card_edge_Kn binn.
have HU : #|U| <= 2 by have := max_card (mem U); rewrite card_ord.
have cardU : #|U| = 1.
  case: (ltngtP #|U| 1) => // [|cU2]; first by rewrite ltnNge U0.
  have {}cU2 : #|U| = 2 by apply/eqP; rewrite eqn_leq HU cU2.
  move: Hsize; rewrite cU2 cK2 leq_exp2l // => Hba.
  have Hb1 : b - a <= b.-1 by rewrite -subn1; apply: leq_sub2l.
  by move: (leq_trans Hba Hb1); rewrite -ltnS (ltn_predK b0) ltnn.
have cardF : #|F| = 0.
  apply/eqP; apply: contraTT Hedges; rewrite -lt0n => F0.
  rewrite -ltnNge cK2 cEK2 cardU mul1n muln1.
  apply: leq_trans (_ : 3 * b * 2 <= _);
    last by rewrite leq_mul2l leq_pmulr // orbT.
  rewrite mulnAC /=.
  apply: leq_ltn_trans (_ : 2 * b < _); first by rewrite leq_mul2l ab orbT.
  by rewrite ltn_mul2r b0 andbT.
have {}cardF : F = set0 by apply/eqP; rewrite -cards_eq0 cardF.
have /card_gt0P[x xU] : 0 < #|U| by rewrite cardU.
have /card_gt0P[y yU] : 0 < #|~: U|.
  by have := cardsC U; rewrite cardU card_ord; case: #|~: U|.
rewrite inE in yU.
have xy : x != y by apply: contraNneq yU => <-.
have Hext : 0 < #|@x229_ext_neigh (del_edge_set 'K_2 F) U|.
  apply/card_gt0P; exists y; rewrite inE yU /=.
  apply: (@mem_opns (del_edge_set 'K_2 F) _ x) => //.
  rewrite /edge_rel /=.
  by rewrite /del_es_rel /= cardF inE andbT.
rewrite cardU muln1; apply: leq_trans ab _.
apply: leq_trans (_ : 3 * b * 1 <= _); first by rewrite muln1 leq_pmull.
by rewrite leq_mul2l Hext orbT.
Qed.

(** ** The proper-colouring guard *)

(** NON-VACUITY: colouring every edge by itself is a proper edge colouring. *)
Lemma proper_ecolouring_id (G : sgraph) : proper_ecolouring (G := G) id.
Proof.
move=> x y z xy xz yz; apply: contraNneq yz => /= E.
have : y \in [set x; z] by rewrite -E !inE eqxx orbT.
rewrite !inE => /orP[/eqP yx|/eqP //].
by move: xy; rewrite yx sg_irrefl.
Qed.

(** GUARD HAS TEETH: a constant colouring is not proper as soon as two edges
    share a vertex. *)
Lemma not_proper_ecolouring_const_K3 :
  ~ proper_ecolouring (G := 'K_3) (fun _ => tt).
Proof.
move=> /(_ ord0 (Ordinal (isT : 1 < 3)) (Ordinal (isT : 2 < 3)) isT isT isT).
by rewrite eqxx.
Qed.

(** ** The average-degree guard *)

(** NON-VACUITY: ['K_2] meets the average-degree guard for C = 1. *)
Lemma avgdeg_guard_K2_1 :
  forall L : nat, 2 ^ L <= #|'K_2| -> 1 * (#|'K_2| * L) <= 2 * #|E('K_2)|.
Proof.
move=> L; rewrite card_ord card_edge_Kn binn mul1n => HL.
have : L <= 1 by rewrite -(@leq_exp2l 2) //.
by case: L HL => [|[|L]].
Qed.

(** GUARD HAS TEETH: ['K_2] does NOT meet the average-degree guard for C = 3,
    so the guard genuinely restricts the graphs the statement speaks about. *)
Lemma not_avgdeg_guard_K2_3 :
  ~ (forall L : nat, 2 ^ L <= #|'K_2| -> 3 * (#|'K_2| * L) <= 2 * #|E('K_2)|).
Proof.
move=> /(_ 1); rewrite card_ord card_edge_Kn binn expn1.
by move=> /(_ (leqnn 2)).
Qed.

(** ** Print Assumptions audit *)

Print Assumptions not_rse_K1.
Print Assumptions rse_K2.
Print Assumptions proper_ecolouring_id.
Print Assumptions not_proper_ecolouring_const_K3.
Print Assumptions avgdeg_guard_K2_1.
Print Assumptions not_avgdeg_guard_K2_3.
