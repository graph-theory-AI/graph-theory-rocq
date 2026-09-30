(** * Extremal.conjectures.X106 -- v2 universal tree-limit row *)

From GTBase Require Export base.
From Extremal.conjectures Require Import X105.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X106 vocabulary ***********************************************)

Definition x106_density_close_to
    (H G : sgraph) (C : {set {set G}}) (num den q : nat) : Prop :=
  let total := 'C(#|G|, #|H|) in
  (q * den * #|C| <= (q * num + den) * total) /\
  ((q * num - den) * total <= q * den * #|C|).

Definition x106_density_converges_to
    (H : sgraph) (Tseq : nat -> sgraph) (num den : nat) : Prop :=
  0 < den /\
  forall q : nat,
    0 < q ->
    exists N : nat,
      forall (n : nat) (C : {set {set Tseq n}}),
        N <= n ->
        @x105_induced_copy_family H (Tseq n) C ->
        @x106_density_close_to H (Tseq n) C num den q.

(** Corpus row: studies:std_bubeck_linial_problem_5_universal_convergent_seq
    Site: none
    Review: none
    English statement: (Bubeck and Linial, "Bubeck-Linial problem 5 (universal convergent sequence of trees)")
      There is a sequence of trees T_0, T_1, ... such that every tree S has a POSITIVE rational
      limit density in the sequence: there are num > 0 and den > 0 such that for every q > 0
      there is N with, for all n >= N, the induced density of S in T_n within 1/q of num/den.
    Definitions: [x105_induced_copy_family S G C] - C is exactly the set of vertex sets of G inducing a
      copy of S (X105.v); [x106_density_close_to S G C num den q] - the two cross-multiplied
      inequalities saying that |C| / binomial(|V(G)|,|V(S)|) lies within 1/q of num/den
      (X106.v); [x106_density_converges_to S Tseq num den] - the epsilon-N convergence above
      (X106.v); [is_tree] - coq-graph-theory.
    Notes: this row comes from the studies slice of the corpus, which has no site or review page.
      "Convergent sequence" is rendered only where it is used: the density of every TREE
      converges, which is what the source's limit d(S, T_n) requires; convergence of the
      densities of non-tree graphs is not asserted. The limit is required to be rational (it is
      the pair num/den) and positive (num > 0). The tolerance is 1/q with q ranging over the
      positive naturals, and the nat subtraction in the lower bound truncates harmlessly. *)
Definition universal_convergent_tree_sequence_positive_density_statement : Prop :=
  exists Tseq : nat -> sgraph,
    (forall n : nat, is_tree [set: Tseq n]) /\
    forall S : sgraph,
      is_tree [set: S] ->
      exists num den : nat,
        0 < num /\ x106_density_converges_to S Tseq num den.
