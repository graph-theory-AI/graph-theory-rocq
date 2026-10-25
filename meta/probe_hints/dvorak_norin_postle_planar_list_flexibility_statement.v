(** Witness hint (A2 source repair, 2026-10-25): an axiom-free REFUTATION of
    [Chromatic.conjectures.X132.dvorak_norin_postle_planar_list_flexibility_statement] as encoded before
    its repair (corpus row studies:std_dvo_k_norin_postle_flexibility_conjecture_planar).

    The body asks for lists of size AT LEAST 5 ([weighted_epsilon_flexible G 5 p q]) while the total
    request weight sums over every colour of each list.  The one-vertex graph is planar; with a list of
    q+5 colours, each requested with weight 1, the total request is q+5 and any colouring satisfies
    weight 1, so p * (q+5) <= q * 1 fails for every p > 0.  Marcol found the defect in the X183 review
    (r3_x132_false, evidence math-2026-10-25/x183-review-by-marcol); the planarity proof of the
    one-vertex graph is his.  The source's lists have size exactly 5, 4 and 3; with that reading this
    file no longer compiles (hint-stale-FIX-OK). *)
From GTBase Require Import base.
From Chromatic.conjectures Require Import X132.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition G1 : sgraph := 'K_1.

(** The one-vertex graph is planar: it has too few vertices for a K_5 or K_{3,3} minor. *)
Lemma g1_planar : wagner_planar G1.
Proof.
split=> /minor_card; rewrite card_ord /=.
  by rewrite card_ord.
by rewrite card_sum !card_ord.
Qed.

Lemma refuted : ~ dvorak_norin_postle_planar_list_flexibility_statement.
Proof.
move=> [p [q [hp hpq /(_ G1 g1_planar) [[_ [_ hfl]] _]]]].
have hsz : forall v : G1, (5 <= #|[set: 'I_(q + 5)]|)%N.
  by move=> v; rewrite cardsT card_ord leq_addl.
have [f [_ hf]] := hfl 'I_(q + 5) (fun _ => setT) (fun _ _ => 1%N) hsz.
move: hf; rewrite /weighted_request_total /weighted_request_satisfied.
have -> : \sum_(v : G1) \sum_(c in [set: 'I_(q + 5)]) 1 = q + 5.
  by rewrite big_ord1 sum1_card cardsT card_ord.
have -> : \sum_(v : G1) 1 = 1 by rewrite big_ord1.
rewrite muln1 => h.
have : (q + 5 <= q)%N by apply: leq_trans h; rewrite leq_pmull.
by rewrite -{2}(addn0 q) leq_add2l.
Qed.

Print Assumptions refuted.
