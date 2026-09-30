(** * Minor.conjectures.implications_X214 — corpus-relation edges out of Hadwiger's conjecture

    The wave X214 row bm:bm-041 (Hadwiger) is the source of three confirmed
    [implies] edges of meta/corpus_relations.json: e223, e224 and e240.

    - e223 targets [fractional_hadwiger_statement], which lives in
      extremal-graph-theory; minor-theory cannot import it, so its [@EDGE] record
      and proof live in atlas/theories/conjectures/implications_A1.v, where it is
      VERIFIED (wave A1, 2026-09-24).
    - e224 and e240 target [seagull_statement] (Minor.conjectures.U7) and
      [hadwiger_independence_minor_statement] (Minor.conjectures.X5); both are
      PROVED below, so both edges are recorded as status=verified.

    Both proofs go through the same textbook bound [#|A| <= χ(A) * α(A)]: an
    optimal colouring has χ(A) classes, each stable and hence of size at most
    α(A).  Axiom-free: only [Qed]-closed results live here. *)

From GTBase Require Import base.
From GraphTheory Require Import minor coloring.
From Minor.conjectures Require Import U7 X5 X214.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** The shared bridge lemma *********************************************)

(** Every vertex set is covered by χ(A) stable sets, each of size at most α(A). *)
Lemma card_leq_chi_alpha (G : sgraph) (A : {set G}) : #|A| <= χ(A) * α(A).
Proof.
case: chiP => P /coloring_stabsetP [part stabP] _.
rewrite (card_partition part) -sum_nat_const.
by apply: leq_sum => S SP; exact: stabset_bound (stabP S SP).
Qed.

(** ['K_n] has every smaller complete graph as a minor. *)
Lemma X214_Kn_minor_Km (n m : nat) : m <= n -> minor 'K_n 'K_m.
Proof.
move=> le; apply: (@minor_of_clique _ [set: 'K_n]); last exact: Kn_clique.
by rewrite cardsT card_ord.
Qed.

(** ** e224 : Hadwiger implies the Seagull problem ************************)

(*@EDGE from=hadwiger_chromatic_clique_minor_statement to=seagull_statement kind=implies status=verified proved=true proof=hadwiger_chromatic_clique_minor_statement_implies_seagull_statement cite="gc:e224" note="A graph with independence number at most 2 has every colour class of size at most 2, so its chromatic number is at least ceil(n/2); Hadwiger then yields a K_chi minor, and a K_ceil(n/2) minor by minor-monotonicity of complete graphs." *)
Theorem hadwiger_chromatic_clique_minor_statement_implies_seagull_statement :
  hadwiger_chromatic_clique_minor_statement -> seagull_statement.
Proof.
move=> HAD G _ a2.
have key : #|G| <= χ([set: G]) * 2.
  rewrite -cardsT; apply: (leq_trans (card_leq_chi_alpha [set: G])).
  by rewrite leq_mul2l alphaT a2 orbT.
have ceil_le : ceil_div #|G| 2 <= χ([set: G]).
  rewrite /ceil_div; have -> : #|G| + 2 - 1 = #|G|.+1 by rewrite addn2 subn1.
  apply: (leq_trans (leq_div2r 2 (_ : #|G|.+1 <= χ([set: G]) * 2 + 1))).
    by rewrite addn1 ltnS; exact: key.
  by rewrite divnMDl // divn_small // addn0.
by apply: minor_trans (HAD _ _ (erefl _)) (X214_Kn_minor_Km ceil_le).
Qed.

(** ** e240 : Hadwiger implies the independence-number form ***************)

(*@EDGE from=hadwiger_chromatic_clique_minor_statement to=hadwiger_independence_minor_statement kind=implies status=verified proved=true proof=hadwiger_chromatic_clique_minor_statement_implies_hadwiger_independence_minor_statement cite="gc:e240" note="Hadwiger gives a K_chi minor; a graph with no K_{t+1} minor therefore has chromatic number at most t, and n <= chi * alpha <= t * alpha." *)
Theorem hadwiger_chromatic_clique_minor_statement_implies_hadwiger_independence_minor_statement :
  hadwiger_chromatic_clique_minor_statement -> hadwiger_independence_minor_statement.
Proof.
move=> HAD t n G _ cardn noK.
have hchi : minor G 'K_(χ([set: G])) by exact: HAD.
have chile : χ([set: G]) <= t.
  rewrite leqNgt; apply/negP => tlt; apply: noK.
  by apply: minor_trans hchi (X214_Kn_minor_Km tlt).
rewrite -cardn -cardsT; apply: (leq_trans (card_leq_chi_alpha [set: G])).
by rewrite alphaT leq_mul2r chile orbT.
Qed.
