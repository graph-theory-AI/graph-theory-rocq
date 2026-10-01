(** * Semantic interface for the k=7 C12 low-three finite base *)

From Stdlib Require Import List Bool Arith Lia.
From Digraph Require Import ckpath_cnf ckpath_cardinality
  ckpath_cert_base ckpath_cert_k7_base ckpath_cert_k7_c12_low3_base
  ckpath_cert_clause_tools ckpath_cert_k7_clause_tools.
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

Local Lemma k7_at_least_satisfied
    (rho : valuation) (k : nat) (xs : list nat) :
  k <= length xs -> k <= count_true rho xs ->
  satisfies_cnf rho (at_least_comb [] k xs).
Proof.
intros hlen hcount; apply at_least_comb_complete; [exact hlen |].
right; exact hcount.
Qed.

Theorem c12_k7_low_raw_base_satisfied (rho : valuation) :
  satisfies_cnf rho (cycle_base_clauses 12) ->
  count_true rho (map (set_var 12) (vertex_list 12)) = 7 ->
  satisfies_cnf rho
    (flat_map c12_k7_low_endpoint_clauses (vertex_list 12)) ->
  satisfies_cnf rho c12_k7_low_raw_base.
Proof.
intros hcycle hset hendpoints.
unfold c12_k7_low_raw_base.
repeat rewrite satisfies_cnf_app.
repeat split.
- exact hcycle.
- apply k7_exactly_satisfied; [vm_compute; lia | exact hset].
- exact hendpoints.
Qed.

Theorem c12_k7_low3_base_satisfied (rho : valuation) :
  satisfies_cnf rho c12_k7_low_raw_base ->
  rho (mark_var 12 0) = true ->
  (forall i,
      In i (vertex_list 12) ->
      rho (mark_var 12 i) = true ->
      rho (set_var 12 i) = false) ->
  3 <= count_true rho (map (mark_var 12) (vertex_list 12)) ->
  (forall i,
      In i (vertex_list 12) ->
      rho (mark_var 12 i) = false \/
      count_true rho (internal_row 12 i) <= 3) ->
  satisfies_cnf rho c12_k7_low3_base.
Proof.
intros hraw hroot hdisjoint hcard hdegree.
unfold c12_k7_low3_base.
repeat rewrite satisfies_cnf_app.
repeat split.
- exact hraw.
- exact (k7_positive_unit_satisfied rho _ hroot).
- apply satisfies_cnf_map.
  intros i hi.
  unfold satisfies_clause, eval_clause; simpl.
  rewrite !eval_negative_literal.
  destruct (rho (mark_var 12 i)) eqn:hmark; simpl.
  + rewrite (hdisjoint i hi hmark). reflexivity.
  + reflexivity.
- apply k7_at_least_satisfied; [vm_compute; lia | exact hcard].
- apply satisfies_cnf_flat_map.
  intros i hi.
  apply negative_guard_at_most_complete.
  exact (hdegree i hi).
Qed.
