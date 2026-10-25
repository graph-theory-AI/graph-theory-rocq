(** Witness hint (Any-lane re-encoding, 2026-10-25): an axiom-free REFUTATION of
    [Chromatic.conjectures.X183.degenerate_list_flexibility_d_plus_one_statement] as encoded before
    its re-encoding (corpus row arxiv:1612.08698#00, Problem 1).

    The body asks for lists of size AT LEAST d+1 ([weighted_epsilon_flexible]) while the total
    request weight sums over every colour of each list.  At d = 0 the one-vertex graph (0-degenerate)
    with a list of q+1 colours, each requested with weight 1, has total request q+1, and any
    colouring satisfies weight 1, so p * (q+1) <= q * 1 fails for every p > 0.  The source's lists
    have size exactly d+1; with that reading this file no longer compiles (hint-stale-FIX-OK). *)
From GTBase Require Import base.
From Chromatic.conjectures Require Import X183.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition G1 : sgraph := 'K_1.

(** The one-vertex graph is 0-degenerate. *)
Lemma k1_degenerate0 : k_degenerate G1 0.
Proof.
move=> S _ /set0Pn [x xS]; exists x; split => //.
rewrite leqn0 cards_eq0; apply/eqP/setP => y; rewrite !inE.
by apply/negbTE; rewrite /edge_rel /= (fintype.ord1 x) (fintype.ord1 y) eqxx.
Qed.

Lemma refuted : ~ degenerate_list_flexibility_d_plus_one_statement.
Proof.
move=> /(_ 0) [p [q [hp hpq /(_ G1 k1_degenerate0) [_ [_ hfl]]]]].
have hsz : forall v : G1, (1 <= #|[set: 'I_q.+1]|)%N by move=> v; rewrite cardsT card_ord.
have [f [_ hf]] := hfl 'I_q.+1 (fun _ => setT) (fun _ _ => 1%N) hsz.
move: hf; rewrite /weighted_request_total /weighted_request_satisfied.
have -> : \sum_(v : G1) \sum_(c in [set: 'I_q.+1]) 1 = q.+1.
  by rewrite big_ord1 sum1_card cardsT card_ord.
have -> : \sum_(v : G1) 1 = 1 by rewrite big_ord1.
rewrite muln1 => h.
have : (q.+1 <= q)%N by apply: leq_trans h; rewrite leq_pmull.
by rewrite ltnn.
Qed.

Print Assumptions refuted.
