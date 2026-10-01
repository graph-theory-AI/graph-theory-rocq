(** * Certified projection interface for the k=7 C12 cover endgame *)

From Stdlib Require Import List Bool Arith Lia.
From Digraph Require Import ckpath_cnf ckpath_cardinality
  ckpath_cert_base ckpath_cert_k7_base ckpath_cert_k7_semantics
  ckpath_cert_k7_c12_cover4_micro_final.
Import ListNotations.

Theorem c12_k7_cover4_projection_impossible (rho : valuation) :
  satisfies_cnf rho (cycle_base_clauses 12) ->
  count_true rho (map (set_var 12) (vertex_list 12)) = 4 ->
  count_true rho (map (mark_var 12) (vertex_list 12)) <= 5 ->
  rho (set_var 12 0) = true ->
  satisfies_cnf rho
    (flat_map c12_k7_cover_endpoint_clauses (vertex_list 12)) -> False.
Proof.
intros hcycle hset hmark hzero hendpoints.
apply (c12_k7_cover4_micro_base_unsatisfiable rho).
apply (c12_k7_cover_base_satisfied rho 4).
- lia.
- exact hcycle.
- exact hset.
- exact hmark.
- exact hzero.
- exact hendpoints.
Qed.
