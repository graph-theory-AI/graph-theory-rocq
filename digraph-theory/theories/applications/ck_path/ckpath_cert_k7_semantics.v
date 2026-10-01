(** * Compositional semantic interfaces for the k=7 finite bases *)

From Stdlib Require Import List Bool Arith Lia.
From Digraph Require Import ckpath_cnf ckpath_cardinality
  ckpath_cert_base ckpath_cert_k7_base ckpath_cert_clause_tools
  ckpath_cert_k7_clause_tools.
Import ListNotations.

Local Lemma k7_positive_unit_satisfied (rho : valuation) (x : nat) :
  rho x = true -> satisfies_cnf rho [[positive_literal x]].
Proof.
intro hx.
unfold satisfies_cnf, eval_cnf, eval_clause, eval_literal,
  positive_literal.
simpl; now rewrite hx.
Qed.

Local Lemma k7_exactly_satisfied
    (rho : valuation) (k : nat) (xs : list nat) :
  k <= length xs -> count_true rho xs = k ->
  satisfies_cnf rho (exactly_comb [] k xs).
Proof.
intros hlen hcount.
apply exactly_comb_complete; [exact hlen |].
right; exact hcount.
Qed.

Local Lemma k7_at_most_satisfied
    (rho : valuation) (k : nat) (xs : list nat) :
  count_true rho xs <= k ->
  satisfies_cnf rho (at_most_comb [] k xs).
Proof.
intro hcount; apply at_most_comb_complete.
right; exact hcount.
Qed.

Local Lemma k7_at_least_satisfied
    (rho : valuation) (k : nat) (xs : list nat) :
  k <= length xs -> k <= count_true rho xs ->
  satisfies_cnf rho (at_least_comb [] k xs).
Proof.
intros hlen hcount; apply at_least_comb_complete; [exact hlen |].
right; exact hcount.
Qed.

Theorem c11_k7_bad_base_satisfied (rho : valuation) :
  satisfies_cnf rho (cycle_base_clauses 11) ->
  count_true rho (map (set_var 11) (vertex_list 11)) = 6 ->
  rho (mark_var 11 0) = true ->
  satisfies_cnf rho
    (flat_map c11_k7_bad_endpoint_clauses (vertex_list 11)) ->
  2 <= count_true rho (map (mark_var 11) (vertex_list 11)) ->
  satisfies_cnf rho c11_k7_bad_base.
Proof.
intros hcycle hset hzero hendpoints hbad.
unfold c11_k7_bad_base.
repeat rewrite satisfies_cnf_app.
repeat split.
- exact hcycle.
- apply k7_exactly_satisfied; [vm_compute; lia | exact hset].
- exact (k7_positive_unit_satisfied rho _ hzero).
- exact hendpoints.
- apply k7_at_least_satisfied; [vm_compute; lia | exact hbad].
Qed.

Theorem c12_k7_cover_base_satisfied (rho : valuation) m :
  m <= 12 ->
  satisfies_cnf rho (cycle_base_clauses 12) ->
  count_true rho (map (set_var 12) (vertex_list 12)) = m ->
  count_true rho (map (mark_var 12) (vertex_list 12)) <= 5 ->
  rho (set_var 12 0) = true ->
  satisfies_cnf rho
    (flat_map c12_k7_cover_endpoint_clauses (vertex_list 12)) ->
  satisfies_cnf rho (c12_k7_cover_base m).
Proof.
intros hm hcycle hset hmark hzero hendpoints.
unfold c12_k7_cover_base.
repeat rewrite satisfies_cnf_app.
repeat split.
- exact hcycle.
- apply k7_exactly_satisfied; [vm_compute; lia | exact hset].
- exact (k7_at_most_satisfied rho _ _ hmark).
- exact (k7_positive_unit_satisfied rho _ hzero).
- exact hendpoints.
Qed.

Theorem c12_k7_low_base_satisfied (rho : valuation) :
  satisfies_cnf rho (cycle_base_clauses 12) ->
  count_true rho (map (set_var 12) (vertex_list 12)) = 7 ->
  rho (set_var 12 0) = true ->
  satisfies_cnf rho
    (flat_map c12_k7_low_endpoint_clauses (vertex_list 12)) ->
  satisfies_cnf rho c12_k7_low_base.
Proof.
intros hcycle hset hzero hendpoints.
unfold c12_k7_low_base.
repeat rewrite satisfies_cnf_app.
repeat split.
- exact hcycle.
- apply k7_exactly_satisfied; [vm_compute; lia | exact hset].
- exact (k7_positive_unit_satisfied rho _ hzero).
- exact hendpoints.
Qed.

Theorem c13_k7_cover_base_satisfied (rho : valuation) m :
  m <= 13 ->
  satisfies_cnf rho (cycle_base_clauses 13) ->
  count_true rho (map (set_var 13) (vertex_list 13)) = m ->
  count_true rho (map (mark_var 13) (vertex_list 13)) <= 6 ->
  rho (set_var 13 0) = true ->
  satisfies_cnf rho
    (flat_map c13_k7_cover_endpoint_clauses (vertex_list 13)) ->
  satisfies_cnf rho (c13_k7_cover_base m).
Proof.
intros hm hcycle hset hmark hzero hendpoints.
unfold c13_k7_cover_base.
repeat rewrite satisfies_cnf_app.
repeat split.
- exact hcycle.
- apply k7_exactly_satisfied; [vm_compute; lia | exact hset].
- exact (k7_at_most_satisfied rho _ _ hmark).
- exact (k7_positive_unit_satisfied rho _ hzero).
- exact hendpoints.
Qed.
