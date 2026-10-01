(** * Certified projection interfaces for the k=7 finite endgames *)

From Stdlib Require Import List Bool Arith Lia.
From Digraph Require Import ckpath_cnf ckpath_cardinality
  ckpath_cert_base ckpath_cert_k7_base ckpath_cert_k7_semantics
  ckpath_cert_k7_c11_bad.
Import ListNotations.

Theorem c11_k7_bad_projection_impossible (rho : valuation) :
  satisfies_cnf rho (cycle_base_clauses 11) ->
  count_true rho (map (set_var 11) (vertex_list 11)) = 6 ->
  rho (mark_var 11 0) = true ->
  satisfies_cnf rho
    (flat_map c11_k7_bad_endpoint_clauses (vertex_list 11)) ->
  2 <= count_true rho (map (mark_var 11) (vertex_list 11)) -> False.
Proof.
intros hcycle hset hzero hendpoints hbad.
apply (c11_k7_bad_base_unsatisfiable rho).
exact (c11_k7_bad_base_satisfied rho
         hcycle hset hzero hendpoints hbad).
Qed.
