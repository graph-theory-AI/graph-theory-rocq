(** * C9/C10 semantic interfaces for the finite CK-path certificates

    This small projection layer deliberately imports no C11 certificate.
    It assembles independently checked semantic fragments into the exact C9
    and C10 CNFs replayed by their generated DRUP certificates. *)

From Stdlib Require Import List Bool Arith Lia.
From Digraph Require Import ckpath_cnf ckpath_cardinality ckpath_cert_base
  ckpath_cert_c9 ckpath_cert_c10.
Import ListNotations.

Local Lemma positive_unit_satisfied_small (rho : valuation) (x : nat) :
  rho x = true -> satisfies_cnf rho [[positive_literal x]].
Proof.
intro Hx.
unfold satisfies_cnf, eval_cnf, eval_clause, eval_literal,
  positive_literal.
simpl. now rewrite Hx.
Qed.

Local Lemma exactly_comb_satisfied_small
    (rho : valuation) (k : nat) (xs : list nat) :
  k <= length xs -> count_true rho xs = k ->
  satisfies_cnf rho (exactly_comb [] k xs).
Proof.
intros Hlen Hcount.
apply exactly_comb_complete; [exact Hlen |].
right. exact Hcount.
Qed.

Local Lemma at_most_comb_satisfied_small
    (rho : valuation) (k : nat) (xs : list nat) :
  count_true rho xs <= k -> satisfies_cnf rho (at_most_comb [] k xs).
Proof.
intro Hcount.
apply at_most_comb_complete.
right. exact Hcount.
Qed.

Local Lemma at_least_comb_satisfied_small
    (rho : valuation) (k : nat) (xs : list nat) :
  k <= length xs -> k <= count_true rho xs ->
  satisfies_cnf rho (at_least_comb [] k xs).
Proof.
intros Hlen Hcount.
apply at_least_comb_complete; [exact Hlen |].
right. exact Hcount.
Qed.

Theorem c9_projection_impossible (rho : valuation) :
  satisfies_cnf rho (cycle_base_clauses 9) ->
  count_true rho (map (set_var 9) (vertex_list 9)) = 3 ->
  count_true rho (map (mark_var 9) (vertex_list 9)) <= 5 ->
  rho (set_var 9 0) = true ->
  satisfies_cnf rho
    (flat_map c9_endpoint_clauses (vertex_list 9)) -> False.
Proof.
intros Hcycle Hset Hmark Hzero Hendpoints.
apply (c9_base_unsatisfiable rho).
assert (Hlen : 3 <= length (map (set_var 9) (vertex_list 9))).
{
  unfold vertex_list.
  rewrite length_map, length_seq.
  lia.
}
pose proof
  (exactly_comb_satisfied_small rho 3 _ Hlen Hset) as Hset'.
pose proof
  (at_most_comb_satisfied_small rho 5 _ Hmark) as Hmark'.
pose proof
  (positive_unit_satisfied_small rho (set_var 9 0) Hzero) as Hzero'.
unfold c9_base, satisfies_cnf, eval_cnf in *.
repeat rewrite forallb_app.
apply Bool.andb_true_iff.
split.
- exact Hcycle.
- apply Bool.andb_true_iff.
  split.
  + exact Hset'.
  + apply Bool.andb_true_iff.
    split.
    * exact Hmark'.
    * apply Bool.andb_true_iff.
      split; assumption.
Qed.

Theorem c10_projection_impossible (rho : valuation) :
  satisfies_cnf rho (cycle_base_clauses 10) ->
  count_true rho (map (set_var 10) (vertex_list 10)) = 6 ->
  rho (mark_var 10 0) = true ->
  satisfies_cnf rho
    (flat_map c10_endpoint_clauses (vertex_list 10)) ->
  2 <= count_true rho (map (mark_var 10) (vertex_list 10)) -> False.
Proof.
intros Hcycle Hset Hzero Hendpoints Hmark.
apply (c10_base_unsatisfiable rho).
assert (HlenSet : 6 <= length (map (set_var 10) (vertex_list 10))).
{
  unfold vertex_list.
  rewrite length_map, length_seq.
  lia.
}
assert (HlenMark : 2 <= length (map (mark_var 10) (vertex_list 10))).
{
  unfold vertex_list.
  rewrite length_map, length_seq.
  lia.
}
pose proof
  (exactly_comb_satisfied_small rho 6 _ HlenSet Hset) as Hset'.
pose proof
  (positive_unit_satisfied_small rho (mark_var 10 0) Hzero) as Hzero'.
pose proof
  (at_least_comb_satisfied_small rho 2 _ HlenMark Hmark) as Hmark'.
unfold c10_base, satisfies_cnf, eval_cnf in *.
repeat rewrite forallb_app.
apply Bool.andb_true_iff.
split.
- exact Hcycle.
- apply Bool.andb_true_iff.
  split.
  + exact Hset'.
  + apply Bool.andb_true_iff.
    split.
    * exact Hzero'.
    * apply Bool.andb_true_iff.
      split; [exact Hendpoints | exact Hmark'].
Qed.
