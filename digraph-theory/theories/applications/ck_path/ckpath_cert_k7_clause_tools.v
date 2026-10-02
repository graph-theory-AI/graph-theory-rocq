(** * Semantic plumbing specific to the k=7 finite formulas *)

From Stdlib Require Import List Bool Arith Lia.
From mathcomp Require Import all_boot.
From Digraph Require Import ckpath_cnf ckpath_cardinality
  ckpath_cert_base ckpath_cert_k7_base ckpath_cert_valuation
  ckpath_cert_clause_tools.
Import ListNotations.

Lemma positive_guard_at_most_complete rho x k xs :
  (rho x = true \/ (count_true rho xs <= k)%coq_nat) ->
  satisfies_cnf rho (at_most_comb [positive_literal x] k xs).
Proof.
move=> hcase; apply: at_most_comb_complete.
case: hcase => [hx | hc].
- left; unfold eval_clause; simpl.
  by rewrite eval_positive_literal hx.
- right; exact hc.
Qed.

Lemma negative_guard_at_most_complete rho x k xs :
  (rho x = false \/ (count_true rho xs <= k)%coq_nat) ->
  satisfies_cnf rho (at_most_comb [negative_literal x] k xs).
Proof.
move=> hcase; apply: at_most_comb_complete.
case: hcase => [hx | hc].
- left; unfold eval_clause; simpl.
  by rewrite eval_negative_literal hx.
- right; exact hc.
Qed.

Lemma two_positive_guard_at_least_complete rho x y k xs :
  (k <= length xs)%coq_nat ->
  (rho x = true \/ rho y = true \/
   (k <= count_true rho xs)%coq_nat) ->
  satisfies_cnf rho
    (at_least_comb [positive_literal x; positive_literal y] k xs).
Proof.
move=> hlen hcase; apply: at_least_comb_complete => //.
case: hcase => [hx | [hy | hc]].
- left; unfold eval_clause; simpl.
  by rewrite eval_positive_literal hx.
- left; unfold eval_clause; simpl.
  by rewrite !eval_positive_literal hy orbT.
- right; exact hc.
Qed.

Lemma c11_k7_bad_rotation_clause_complete rho endpoint path :
  (rho (mark_var 11 endpoint) = true ->
   rho (set_var 11 (cycle_predecessor 11 (hd 0 path))) = true ->
   (forall x, In x (path_chord_vars 11 path) -> rho x = true) -> False) ->
  satisfies_clause rho (c11_k7_bad_rotation_clause endpoint path).
Proof.
move=> hbad.
remember (cycle_predecessor 11 (hd 0 path)) as pred_start eqn:hpred.
unfold satisfies_clause, c11_k7_bad_rotation_clause.
rewrite <- hpred.
change ((eval_literal rho (negative_literal (mark_var 11 endpoint)) ||
         (eval_literal rho (negative_literal (set_var 11 pred_start)) ||
          eval_clause rho
            (map negative_literal (path_chord_vars 11 path)))) = true).
rewrite !eval_negative_literal.
rewrite eval_negative_clause.
case hmark: (rho (mark_var 11 endpoint)); simpl; last by [].
case hset: (rho (set_var 11 pred_start)); simpl; last by [].
case hall: (forallb rho (path_chord_vars 11 path)); simpl; last by [].
exfalso.
apply (hbad hmark hset).
move=> x hx.
exact: (proj1 (forallb_forall rho _) hall x hx).
Qed.

Lemma c12_k7_low_rotation_clause_complete rho endpoint path :
  (rho (set_var 12 endpoint) = false ->
   rho (mark_var 12 endpoint) = true ->
   rho (set_var 12 (cycle_predecessor 12 (hd 0 path))) = true ->
   (forall x, In x (path_chord_vars 12 path) -> rho x = true) -> False) ->
  satisfies_clause rho (c12_k7_low_rotation_clause endpoint path).
Proof.
move=> hbad.
remember (cycle_predecessor 12 (hd 0 path)) as pred_start eqn:hpred.
unfold satisfies_clause, c12_k7_low_rotation_clause.
rewrite <- hpred.
change ((eval_literal rho (positive_literal (set_var 12 endpoint)) ||
         (eval_literal rho (negative_literal (mark_var 12 endpoint)) ||
          (eval_literal rho (negative_literal (set_var 12 pred_start)) ||
           eval_clause rho
             (map negative_literal (path_chord_vars 12 path))))) = true).
rewrite eval_positive_literal.
rewrite !eval_negative_literal.
rewrite eval_negative_clause.
case hsetq: (rho (set_var 12 endpoint)); simpl; first by [].
case hmark: (rho (mark_var 12 endpoint)); simpl; last by [].
case hset: (rho (set_var 12 pred_start)); simpl; last by [].
case hall: (forallb rho (path_chord_vars 12 path)); simpl; last by [].
exfalso.
apply (hbad hsetq hmark hset).
move=> x hx.
exact: (proj1 (forallb_forall rho _) hall x hx).
Qed.
