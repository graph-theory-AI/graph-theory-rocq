(** * Chromatic.conjectures.X100 -- v2 modular edge-colouring row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X100 vocabulary ***********************************************)

Definition x100_edge_set (G : sgraph) : {set {set G}} :=
  simple_edge_set G.

Definition x100_col_deg
    (G : sgraph) (q : nat) (col : {set G} -> 'I_q) (v : G) (c : 'I_q) : nat :=
  \sum_(e in x100_edge_set G | (v \in e) && (col e == c)) 1.

Definition x100_modular_edge_colouring
    (G : sgraph) (k q : nat) (col : {set G} -> 'I_q) : Prop :=
  forall (v : G) (c : 'I_q),
    x100_col_deg col v c = 0 \/ x100_col_deg col v c %% k = 1.

Definition x100_modular_edge_colourable
    (G : sgraph) (k q : nat) : Prop :=
  exists col : {set G} -> 'I_q, @x100_modular_edge_colouring G k q col.

(** ** X100 statements *****************************************************)

(** Studies slice: Botler-Colucci-Kohayakawa modular edge-colouring conjecture:
    for every modulus k >= 2, k plus a constant number of edge colours suffice
    for every finite graph. *)
Definition modular_edge_colouring_k_plus_constant_statement : Prop :=
  forall k : nat,
    2 <= k ->
    exists C : nat,
      forall G : sgraph,
        x100_modular_edge_colourable G k (k + C).
