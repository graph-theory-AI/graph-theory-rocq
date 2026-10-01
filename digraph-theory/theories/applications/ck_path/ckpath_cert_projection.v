(** * Semantic interfaces for the finite CK-path certificates

    The generated proof objects establish unsatisfiability of concrete CNFs.
    This module exposes the small, compositional interface needed by the graph
    bridge: the cycle clauses, cardinalities, normalization unit, and endpoint
    clauses may be verified independently and then assembled into the exact
    certified base formula. *)

From Stdlib Require Import List Bool Arith Lia.
From Digraph Require Import ckpath_cnf ckpath_cardinality ckpath_cert_base
  ckpath_cert_c9 ckpath_cert_c10 ckpath_cert_c11_m3 ckpath_cert_c11_m4.
Import ListNotations.

Lemma eval_cnf_app_true (rho : valuation) (left right : cnf) :
  eval_cnf rho left = true -> eval_cnf rho right = true ->
  eval_cnf rho (left ++ right) = true.
Proof.
intros Hleft Hright.
unfold eval_cnf in *. rewrite forallb_app.
now rewrite Hleft, Hright.
Qed.

Lemma positive_unit_satisfied (rho : valuation) (x : nat) :
  rho x = true -> satisfies_cnf rho [[positive_literal x]].
Proof.
intro Hx.
unfold satisfies_cnf, eval_cnf, eval_clause, eval_literal,
  positive_literal.
simpl. now rewrite Hx.
Qed.

Lemma exactly_comb_satisfied
    (rho : valuation) (k : nat) (xs : list nat) :
  k <= length xs -> count_true rho xs = k ->
  satisfies_cnf rho (exactly_comb [] k xs).
Proof.
intros Hlen Hcount.
apply exactly_comb_complete; [exact Hlen |].
right. exact Hcount.
Qed.

Lemma at_most_comb_satisfied
    (rho : valuation) (k : nat) (xs : list nat) :
  count_true rho xs <= k -> satisfies_cnf rho (at_most_comb [] k xs).
Proof.
intro Hcount.
apply at_most_comb_complete.
right. exact Hcount.
Qed.

Lemma at_least_comb_satisfied
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
assert (Hset' :
    eval_cnf rho
      (exactly_comb [] 3 (map (set_var 9) (vertex_list 9))) = true).
  apply exactly_comb_satisfied; [vm_compute; lia | exact Hset].
assert (Hmark' :
    eval_cnf rho
      (at_most_comb [] 5 (map (mark_var 9) (vertex_list 9))) = true).
  exact (at_most_comb_satisfied rho 5 _ Hmark).
assert (Hzero' : eval_cnf rho [[positive_literal (set_var 9 0)]] = true).
  exact (positive_unit_satisfied rho (set_var 9 0) Hzero).
apply (c9_base_unsatisfiable rho).
unfold satisfies_cnf in *.
unfold c9_base.
apply eval_cnf_app_true; [exact Hcycle |].
apply eval_cnf_app_true; [exact Hset' |].
apply eval_cnf_app_true; [exact Hmark' |].
apply eval_cnf_app_true; [exact Hzero' | exact Hendpoints].
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
assert (Hset' :
    eval_cnf rho
      (exactly_comb [] 6 (map (set_var 10) (vertex_list 10))) = true).
  apply exactly_comb_satisfied; [vm_compute; lia | exact Hset].
assert (Hzero' : eval_cnf rho [[positive_literal (mark_var 10 0)]] = true).
  exact (positive_unit_satisfied rho (mark_var 10 0) Hzero).
assert (Hmark' :
    eval_cnf rho
      (at_least_comb [] 2 (map (mark_var 10) (vertex_list 10))) = true).
  apply at_least_comb_satisfied; [vm_compute; lia | exact Hmark].
apply (c10_base_unsatisfiable rho).
unfold satisfies_cnf in *.
unfold c10_base.
apply eval_cnf_app_true; [exact Hcycle |].
apply eval_cnf_app_true; [exact Hset' |].
apply eval_cnf_app_true; [exact Hzero' |].
apply eval_cnf_app_true; [exact Hendpoints | exact Hmark'].
Qed.

Theorem c11_m3_projection_impossible (rho : valuation) :
  satisfies_cnf rho (cycle_base_clauses 11) ->
  count_true rho (map (set_var 11) (vertex_list 11)) = 3 ->
  count_true rho (map (mark_var 11) (vertex_list 11)) <= 5 ->
  rho (set_var 11 0) = true ->
  satisfies_cnf rho
    (flat_map (c11_endpoint_clauses 3) (vertex_list 11)) -> False.
Proof.
intros Hcycle Hset Hmark Hzero Hendpoints.
assert (Hset' :
    eval_cnf rho
      (exactly_comb [] 3 (map (set_var 11) (vertex_list 11))) = true).
  apply exactly_comb_satisfied; [vm_compute; lia | exact Hset].
assert (Hmark' :
    eval_cnf rho
      (at_most_comb [] 5 (map (mark_var 11) (vertex_list 11))) = true).
  exact (at_most_comb_satisfied rho 5 _ Hmark).
assert (Hzero' : eval_cnf rho [[positive_literal (set_var 11 0)]] = true).
  exact (positive_unit_satisfied rho (set_var 11 0) Hzero).
apply (c11_m3_base_unsatisfiable rho).
unfold satisfies_cnf in *.
unfold c11_base.
apply eval_cnf_app_true; [exact Hcycle |].
apply eval_cnf_app_true; [exact Hset' |].
apply eval_cnf_app_true; [exact Hmark' |].
apply eval_cnf_app_true; [exact Hzero' | exact Hendpoints].
Qed.

Theorem c11_m4_projection_impossible (rho : valuation) :
  satisfies_cnf rho (cycle_base_clauses 11) ->
  count_true rho (map (set_var 11) (vertex_list 11)) = 4 ->
  count_true rho (map (mark_var 11) (vertex_list 11)) <= 5 ->
  rho (set_var 11 0) = true ->
  satisfies_cnf rho
    (flat_map (c11_endpoint_clauses 4) (vertex_list 11)) -> False.
Proof.
intros Hcycle Hset Hmark Hzero Hendpoints.
assert (Hset' :
    eval_cnf rho
      (exactly_comb [] 4 (map (set_var 11) (vertex_list 11))) = true).
  apply exactly_comb_satisfied; [vm_compute; lia | exact Hset].
assert (Hmark' :
    eval_cnf rho
      (at_most_comb [] 5 (map (mark_var 11) (vertex_list 11))) = true).
  exact (at_most_comb_satisfied rho 5 _ Hmark).
assert (Hzero' : eval_cnf rho [[positive_literal (set_var 11 0)]] = true).
  exact (positive_unit_satisfied rho (set_var 11 0) Hzero).
apply (c11_m4_base_unsatisfiable rho).
unfold satisfies_cnf in *.
unfold c11_base.
apply eval_cnf_app_true; [exact Hcycle |].
apply eval_cnf_app_true; [exact Hset' |].
apply eval_cnf_app_true; [exact Hmark' |].
apply eval_cnf_app_true; [exact Hzero' | exact Hendpoints].
Qed.
