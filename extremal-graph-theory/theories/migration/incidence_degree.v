(** A10 incidence degree: the frozen X36/X84 counts of the members of a supplied family containing
    a vertex, their chains and the three extremal rows (X85 reaches X84's cycle count across files).
    Baseline, hashes and exact substitutions are recorded in
    meta/migration_reports/incidence_degree.spec.json.
    - [Legacy]: the two counts at the baseline, over an ARBITRARY family [F : {set {set G}}];
      their certificates are conversions to [GTBase.incidence.incidence_degree].
    - [X36Legacy], [X84Legacy], [X85Legacy]: the chains and rows over these frozen counts.  The
      M1 edge-set aliases and every other helper stay live (no pre-M1 claim). *)
From GTBase Require Import base.
From Extremal.conjectures Require Import X36 X84 X85.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Legacy.

Definition x36_degree_in_edge_set
    (G : sgraph) (F : {set {set G}}) (v : G) : nat :=
  #|[set e in F | v \in e]|.

Definition x84_degree_in (G : sgraph) (F : {set {set G}}) (v : G) : nat :=
  #|[set e in F | v \in e]|.

End Legacy.

Module X36Legacy.

Definition nonempty_k_divisible_subgraph (G : sgraph) (k : nat) : Prop :=
  exists F : {set {set G}},
    F != set0 /\
    F \subset x36_edge_set G /\
    forall v : G, Legacy.x36_degree_in_edge_set F v %% k == 0.

Definition alon_friedland_kalai_divisible_subgraph_statement : Prop :=
  forall (k : nat) (G : sgraph),
    0 < k ->
    ~ nonempty_k_divisible_subgraph G k ->
    #|x36_edge_set G| <= (k - 1) * #|G|.

End X36Legacy.

Module X84Legacy.

Definition cycle_edge_set (G : sgraph) (F : {set {set G}}) : bool :=
  [&& F \subset x84_edge_set G,
      2 < #|x84_support F|,
      #|F| == #|x84_support F|,
      [forall v in x84_support F, Legacy.x84_degree_in F v == 2]
    & x84_connected_support F].

Definition cycle_count (G : sgraph) : nat :=
  #|[set F : {set {set G}} | @cycle_edge_set G F]|.

Definition has_cycle_length (G : sgraph) (l : nat) : Prop :=
  exists F : {set {set G}},
    @cycle_edge_set G F /\ #|x84_support F| = l.

Definition odd_cycle_free_turan2_unique_cycle_extremal_statement : Prop :=
  forall k : nat,
    1 < k ->
    exists N : nat,
      forall n : nat,
        N <= n ->
        ~ has_cycle_length (x84_turan2 n) (2 * k + 1) /\
        forall G : sgraph,
          #|G| = n ->
          ~ has_cycle_length G (2 * k + 1) ->
          cycle_count G <= cycle_count (x84_turan2 n) /\
          (cycle_count G = cycle_count (x84_turan2 n) ->
             inhabited (G ≃ x84_turan2 n)).

End X84Legacy.

Module X85Legacy.

Definition arman_tsaturian_average_degree_cycle_count_statement : Prop :=
  exists c den N : nat,
    [/\ 0 < c, 1 < den
      & forall (n d : nat) (G : sgraph),
          N <= d ->
          #|G| = n ->
          x85_average_degree_exact G d ->
          x85_log_corrected_exponential_bound
            c den n d (X84Legacy.cycle_count G)].

End X85Legacy.

(** The two counts convert to [incidence_degree]; so does every chain and row below. *)
Lemma x36_degree_in_edge_set_compat (G : sgraph) (F : {set {set G}}) (v : G) :
  Legacy.x36_degree_in_edge_set F v = x36_degree_in_edge_set F v.
Proof. by []. Qed.

Lemma x84_degree_in_compat (G : sgraph) (F : {set {set G}}) (v : G) :
  Legacy.x84_degree_in F v = x84_degree_in F v.
Proof. by []. Qed.

Lemma x36_nonempty_k_divisible_subgraph_compat (G : sgraph) (k : nat) :
  X36Legacy.nonempty_k_divisible_subgraph G k <-> x36_nonempty_k_divisible_subgraph G k.
Proof. exact: iff_refl. Qed.

Lemma alon_friedland_kalai_divisible_subgraph_statement_compat :
  X36Legacy.alon_friedland_kalai_divisible_subgraph_statement <->
  alon_friedland_kalai_divisible_subgraph_statement.
Proof. exact: iff_refl. Qed.

Lemma x84_cycle_edge_set_compat (G : sgraph) (F : {set {set G}}) :
  X84Legacy.cycle_edge_set F = x84_cycle_edge_set F.
Proof. by []. Qed.

Lemma x84_cycle_count_compat (G : sgraph) : X84Legacy.cycle_count G = x84_cycle_count G.
Proof. by []. Qed.

Lemma x84_has_cycle_length_compat (G : sgraph) (l : nat) :
  X84Legacy.has_cycle_length G l <-> x84_has_cycle_length G l.
Proof. exact: iff_refl. Qed.

Lemma odd_cycle_free_turan2_unique_cycle_extremal_statement_compat :
  X84Legacy.odd_cycle_free_turan2_unique_cycle_extremal_statement <->
  odd_cycle_free_turan2_unique_cycle_extremal_statement.
Proof. exact: iff_refl. Qed.

Lemma arman_tsaturian_average_degree_cycle_count_statement_compat :
  X85Legacy.arman_tsaturian_average_degree_cycle_count_statement <->
  arman_tsaturian_average_degree_cycle_count_statement.
Proof. exact: iff_refl. Qed.
