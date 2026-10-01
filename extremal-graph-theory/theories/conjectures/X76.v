(** * Extremal.conjectures.X76 -- v2 C_k-free max-cut row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X76 vocabulary ************************************************)

Definition x76_edge_set (G : sgraph) : {set {set G}} :=
  simple_edge_set G.

Definition x76_edge_count (G : sgraph) : nat := #|x76_edge_set G|.

Definition x76_cut_size (G : sgraph) (A : {set G}) : nat :=
  #|[set e in x76_edge_set G | ~~ [disjoint e & A] && ~~ (e \subset A)]|.

Definition x76_has_cycle_length (G : sgraph) (k : nat) : Prop :=
  exists c : seq G, ucycle (--) c /\ size c = k.

Definition x76_power_surplus
    (k cnum cden m s : nat) : Prop :=
  (cnum ^ (k + 2)) * (m ^ (k + 1)) <=
    (cden ^ (k + 2)) * (s ^ (k + 2)).

(** ** X76 statements ******************************************************)

(** Studies slice: Alon et al. conjecture that C_k-free graphs have max-cut
    surplus Omega_k(m^((k+1)/(k+2))).  The fractional power lower bound is
    cross-multiplied over natural constants cnum/cden. *)
Definition ck_free_max_cut_polynomial_surplus_statement : Prop :=
  forall k : nat,
    3 <= k ->
    exists cnum cden N : nat,
      [/\ 0 < cnum, 0 < cden
        & forall (G : sgraph) (m : nat),
            N <= m ->
            x76_edge_count G = m ->
            ~ x76_has_cycle_length G k ->
            exists (A : {set G}) (s : nat),
              x76_power_surplus k cnum cden m s /\
              m + 2 * s <= 2 * x76_cut_size A].
