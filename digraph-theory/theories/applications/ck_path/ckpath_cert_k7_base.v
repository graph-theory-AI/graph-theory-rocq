(** * Concrete finite CNFs for the out-degree-seven endgames *)

From Stdlib Require Import List Bool Arith Lia.
From Digraph Require Import ckpath_cnf ckpath_cardinality ckpath_drup
  ckpath_cert_base.
Import ListNotations.

(** Cut the ordinary cycle path into four nonempty consecutive blocks
    [A|B|C|D] and read them in the order [C|B|A|D]. *)
Definition reverse_three_block_rotation
    (n endpoint a b c : nat) : list nat :=
  let word := cyclic_order n endpoint in
  firstn (c - b) (skipn b word) ++
  firstn (b - a) (skipn a word) ++
  firstn a word ++ skipn c word.

Definition reverse_three_block_paths
    (n endpoint : nat) : list (list nat) :=
  flat_map
    (fun a =>
       flat_map
         (fun b =>
            map (fun c => reverse_three_block_rotation n endpoint a b c)
                (seq (S b) (n - 1 - b)))
         (seq (S a) (n - 2 - a)))
    (seq 1 (n - 3)).

(** ** C11: two bad endpoints outside a six-set *)

Definition c11_k7_bad_rotation_clause
    (endpoint : nat) (path : list nat) : clause :=
  let start := hd 0 path in
  negative_literal (mark_var 11 endpoint) ::
  negative_literal (set_var 11 (cycle_predecessor 11 start)) ::
  map negative_literal (path_chord_vars 11 path).

Definition c11_k7_bad_endpoint_clauses (endpoint : nat) : cnf :=
  exactly_comb [negative_literal (set_var 11 endpoint)] 6
               (internal_row 11 endpoint) ++
  [[negative_literal (mark_var 11 endpoint);
    negative_literal (set_var 11 endpoint)]] ++
  map (c11_k7_bad_rotation_clause endpoint)
      (two_chord_paths 11 endpoint).

Definition c11_k7_bad_base : cnf :=
  cycle_base_clauses 11 ++
  exactly_comb [] 6 (map (set_var 11) (vertex_list 11)) ++
  [[positive_literal (mark_var 11 0)]] ++
  flat_map c11_k7_bad_endpoint_clauses (vertex_list 11) ++
  at_least_comb [] 2 (map (mark_var 11) (vertex_list 11)).

(** ** C12: active gateways whose Hamilton starts have a five-cover *)

Definition c12_k7_cover_endpoint_clauses (endpoint : nat) : cnf :=
  [[negative_literal (set_var 12 endpoint);
    positive_literal (mark_var 12 (cycle_successor 12 endpoint))]] ++
  exactly_comb [positive_literal (set_var 12 endpoint)] 6
               (internal_row 12 endpoint) ++
  at_most_comb [negative_literal (set_var 12 endpoint)] 5
               (internal_row 12 endpoint) ++
  map (cover_rotation_clause 12 endpoint) (two_chord_paths 12 endpoint).

Definition c12_k7_cover_base (active_size : nat) : cnf :=
  cycle_base_clauses 12 ++
  exactly_comb [] active_size (map (set_var 12) (vertex_list 12)) ++
  at_most_comb [] 5 (map (mark_var 12) (vertex_list 12)) ++
  [[positive_literal (set_var 12 0)]] ++
  flat_map c12_k7_cover_endpoint_clauses (vertex_list 12).

(** ** C12: every low-degree complementary endpoint is bad *)

Definition c12_k7_low_rotation_clause
    (endpoint : nat) (path : list nat) : clause :=
  let start := hd 0 path in
  positive_literal (set_var 12 endpoint) ::
  negative_literal (mark_var 12 endpoint) ::
  negative_literal (set_var 12 (cycle_predecessor 12 start)) ::
  map negative_literal (path_chord_vars 12 path).

Definition c12_k7_low_endpoint_clauses (endpoint : nat) : cnf :=
  exactly_comb [negative_literal (set_var 12 endpoint)] 6
               (internal_row 12 endpoint) ++
  at_most_comb [positive_literal (set_var 12 endpoint)] 6
               (internal_row 12 endpoint) ++
  at_least_comb
    [positive_literal (set_var 12 endpoint);
     positive_literal (mark_var 12 endpoint)] 4
    (internal_row 12 endpoint) ++
  map (c12_k7_low_rotation_clause endpoint)
      (two_chord_paths 12 endpoint).

Definition c12_k7_low_base : cnf :=
  cycle_base_clauses 12 ++
  exactly_comb [] 7 (map (set_var 12) (vertex_list 12)) ++
  [[positive_literal (set_var 12 0)]] ++
  flat_map c12_k7_low_endpoint_clauses (vertex_list 12).

(** ** C13: active gateways whose Hamilton starts have a six-cover *)

Definition c13_k7_cover_endpoint_clauses (endpoint : nat) : cnf :=
  [[negative_literal (set_var 13 endpoint);
    positive_literal (mark_var 13 (cycle_successor 13 endpoint))]] ++
  exactly_comb [positive_literal (set_var 13 endpoint)] 6
               (internal_row 13 endpoint) ++
  at_most_comb [negative_literal (set_var 13 endpoint)] 5
               (internal_row 13 endpoint) ++
  map (cover_rotation_clause 13 endpoint)
      (two_chord_paths 13 endpoint ++
       reverse_three_block_paths 13 endpoint).

Definition c13_k7_cover_base (active_size : nat) : cnf :=
  cycle_base_clauses 13 ++
  exactly_comb [] active_size (map (set_var 13) (vertex_list 13)) ++
  at_most_comb [] 6 (map (mark_var 13) (vertex_list 13)) ++
  [[positive_literal (set_var 13 0)]] ++
  flat_map c13_k7_cover_endpoint_clauses (vertex_list 13).

(** Executable guards on the exact clause ordering expected by generated
    proof objects.  Counts are filled only after cross-checking the Python
    emitter against these definitions. *)
Lemma reverse_three_block_paths13_count endpoint :
  length (reverse_three_block_paths 13 endpoint) = 220.
Proof. vm_compute. reflexivity. Qed.

Lemma c11_k7_bad_base_clause_count : length c11_k7_bad_base = 2080.
Proof. vm_compute. reflexivity. Qed.

Lemma c12_k7_cover3_base_clause_count :
  length (c12_k7_cover_base 3) = 5188.
Proof. vm_compute. reflexivity. Qed.

Lemma c12_k7_cover4_base_clause_count :
  length (c12_k7_cover_base 4) = 5639.
Proof. vm_compute. reflexivity. Qed.

Lemma c12_k7_low_base_clause_count : length c12_k7_low_base = 5542.
Proof. vm_compute. reflexivity. Qed.

Lemma c13_k7_cover3_base_clause_count :
  length (c13_k7_cover_base 3) = 13898.
Proof. vm_compute. reflexivity. Qed.

Lemma c13_k7_cover4_base_clause_count :
  length (c13_k7_cover_base 4) = 14678.
Proof. vm_compute. reflexivity. Qed.

Lemma c13_k7_cover5_base_clause_count :
  length (c13_k7_cover_base 5) = 15536.
Proof. vm_compute. reflexivity. Qed.
