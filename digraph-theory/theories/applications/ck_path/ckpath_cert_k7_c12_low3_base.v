(** * Rotation-normalized C12 low-three finite base for k=7 *)

From Stdlib Require Import List Bool Arith Lia.
From Digraph Require Import ckpath_cnf ckpath_cardinality
  ckpath_cert_base ckpath_cert_k7_base.
Import ListNotations.

(** The same endpoint constraints before choosing a root in the seven-set.
    Keep [c12_k7_low_base] in [ckpath_cert_k7_base] in its historical order:
    existing generated objects depend on the unit clause occurring before the
    endpoint blocks. *)
Definition c12_k7_low_raw_base : cnf :=
  cycle_base_clauses 12 ++
  exactly_comb [] 7 (map (set_var 12) (vertex_list 12)) ++
  flat_map c12_k7_low_endpoint_clauses (vertex_list 12).

(** A rotation-normalized low root, at least three low endpoints, disjointness
    from the seven-set, and the internal-degree consequence of being low. *)
Definition c12_k7_low3_base : cnf :=
  c12_k7_low_raw_base ++
  [[positive_literal (mark_var 12 0)]] ++
  map
    (fun i =>
       [negative_literal (mark_var 12 i);
        negative_literal (set_var 12 i)])
    (vertex_list 12) ++
  at_least_comb [] 3 (map (mark_var 12) (vertex_list 12)) ++
  flat_map
    (fun i =>
       at_most_comb [negative_literal (mark_var 12 i)] 3
                    (internal_row 12 i))
    (vertex_list 12).

Lemma c12_k7_low_raw_base_clause_count :
  length c12_k7_low_raw_base = 5541.
Proof. vm_compute. reflexivity. Qed.

Lemma c12_k7_low3_base_clause_count : length c12_k7_low3_base = 7132.
Proof. vm_compute. reflexivity. Qed.
