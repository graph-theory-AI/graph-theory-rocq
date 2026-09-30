(** * Extremal.conjectures.X76 -- v2 C_k-free max-cut row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X76 vocabulary ************************************************)

Definition x76_edge_set (G : sgraph) : {set {set G}} :=
  [set e : {set G} |
      [exists x : G, [exists y : G, (x -- y) && (e == [set x; y])]]].

Definition x76_edge_count (G : sgraph) : nat := #|x76_edge_set G|.

Definition x76_cut_size (G : sgraph) (A : {set G}) : nat :=
  #|[set e in x76_edge_set G | ~~ [disjoint e & A] && ~~ (e \subset A)]|.

Definition x76_has_cycle_length (G : sgraph) (k : nat) : Prop :=
  exists c : seq G, ucycle (--) c /\ size c = k.

Definition x76_power_surplus
    (k cnum cden m s : nat) : Prop :=
  (cnum ^ (k + 2)) * (m ^ (k + 1)) <=
    (cden ^ (k + 2)) * (s ^ (k + 2)).

(** Corpus row: studies:std_alon_et_al_c_k_free_max_cut_conjecture
    Site: none
    Review: none
    English statement: (Alon et al., "Alon et al. C_k-Free Max-Cut Conjecture")
      For every k >= 3 there are positive naturals cnum, cden and a threshold N such that every
      graph G with m >= N edges and no cycle of length k has a vertex set A whose cut has size
      at least m/2 + s for some s with (cnum/cden) * m^((k+1)/(k+2)) <= s; that is, the max-cut
      surplus is Omega_k(m^((k+1)/(k+2))).
    Definitions: [x76_edge_set G], [x76_edge_count G] - the edges as 2-element vertex sets and their
      number (X76.v); [x76_cut_size G A] - the number of edges with exactly one end in A
      (X76.v); [x76_has_cycle_length G k] - some uniform cycle of G has exactly k vertices, so
      its negation is C_k-freeness (X76.v); [x76_power_surplus k cnum cden m s] - the
      cross-multiplied form cnum^(k+2) * m^(k+1) <= cden^(k+2) * s^(k+2) of
      s >= (cnum/cden) * m^((k+1)/(k+2)) (X76.v).
    Notes: this row comes from the studies slice of the corpus, which has no site or review page.
      The surplus is introduced as an existential s together with the cut bound
      m + 2*s <= 2 * cut(A), i.e. cut(A) >= m/2 + s, so no nat subtraction or division is
      needed. The implicit constant depending on k is the ratio cnum/cden, chosen after k and
      before G. *)
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
