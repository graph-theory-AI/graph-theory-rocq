(** * Extremal.conjectures.X85 -- v2 average-degree cycle-count row *)

From GTBase Require Export base.
From Extremal.conjectures Require Import X84.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X85 vocabulary ************************************************)

Definition x85_average_degree_at_most (G : sgraph) (d : nat) : Prop :=
  \sum_(v : G) #|N(v)| <= d * #|G|.

Definition x85_average_degree_exact (G : sgraph) (d : nat) : Prop :=
  average_degree_geq G d 1 /\ x85_average_degree_at_most G d.

Definition x85_log_corrected_exponential_bound
    (c den n d cycles : nat) : Prop :=
  (den ^ n) * cycles <= (d + c * trunc_log 2 d) ^ n.

(** Corpus row: studies:std_arman_tsaturian_conjecture_on_the_number_of_cycl
    Site: none
    Review: none
    English statement: (Arman and Tsaturian, "Arman-Tsaturian Conjecture on the Number of Cycles")
      There are c > 0, den > 1 and a threshold N such that every graph G on n vertices whose
      average degree is exactly d >= N satisfies den^n * (number of cycles of G) <=
      (d + c * floor(log_2 d))^n, i.e. the number of cycles is at most
      ((d + c log d)/den)^n.
    Definitions: [x85_average_degree_at_most G d] - the degree sum is at most d * |V(G)| (X85.v);
      [x85_average_degree_exact G d] - the average degree is both at least and at most d
      (X85.v); [x85_log_corrected_exponential_bound c den n d cycles] - the inequality above
      (X85.v); [x84_cycle_count G] - the number of cycle edge sets (X84.v);
      [average_degree_geq] - GTBase; [trunc_log 2] - MathComp floor-log2.
    Notes: this row comes from the studies slice of the corpus, which has no site or review page.
      The source bound is (1 + O(log d / d))^n * (d/e)^n; the multiplicative error is absorbed
      as the additive correction c * floor(log_2 d) inside the n-th power. PROXY: the base e is
      irrational and is replaced by an EXISTENTIALLY quantified natural den > 1, so a prover may
      take den = 2, which gives a strictly weaker bound than d/e (ledger). *)
Definition arman_tsaturian_average_degree_cycle_count_statement : Prop :=
  exists c den N : nat,
    [/\ 0 < c, 1 < den
      & forall (n d : nat) (G : sgraph),
          N <= d ->
          #|G| = n ->
          x85_average_degree_exact G d ->
          x85_log_corrected_exponential_bound
            c den n d (x84_cycle_count G)].
