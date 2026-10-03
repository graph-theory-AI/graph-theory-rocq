(** A11 minimum-degree lower bounds (misc): the frozen X38/X74 bounds, the two rows and the
    complete X38 row.
    - [Legacy]: the bounds convert to [GTBase.base.min_degree_at_least].
    - [X38Legacy], [X74Legacy]: the rows over these frozen bounds; every other helper stays live.
    - [X38Original]: A10's frozen raw incidence count and degree classes with the frozen bound.  The M1
      edge-set alias stays live, as in A10 (no pre-M1 claim).
    Baseline, hashes and exact substitutions are recorded in meta/migration_reports/min_degree_at_least.spec.json. *)
From GTBase Require Import base.
From GTMisc.conjectures Require Import X38 X74.
From GTMisc.migration Require incidence_degree.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Earlier families' certificate modules, aliased without Import: their module names coincide
    with this file's. *)
Module A10 := GTMisc.migration.incidence_degree.

Module Legacy.

Definition x38_min_degree_at_least (G : sgraph) (delta : nat) : Prop :=
  forall v : G, delta <= #|N(v)|.

Definition x74_min_degree_at_least (G : sgraph) (d : nat) : Prop :=
  forall v : G, d <= #|N(v)|.

End Legacy.

Module X38Legacy.

Definition min_degree_spanning_subgraph_small_degree_multiplicity_statement : Prop :=
  forall (delta : nat) (G : sgraph),
    Legacy.x38_min_degree_at_least G delta ->
    exists F : {set {set G}},
      F \subset x38_edge_set G /\
      forall k : nat,
        (delta.+1 * @x38_degree_class_size G F k <= #|G| + 2 * delta.+1)%N.

End X38Legacy.

Module X74Legacy.

Definition induced_linear_forest_caro_wei_bound_statement : Prop :=
  forall G : sgraph,
    Legacy.x74_min_degree_at_least G 2 ->
    exists S : {set G},
      x74_induced_linear_forest S /\
      x74_scaled_degree_sum G <= x74_degree_sum_den G * #|S|.

End X74Legacy.

Module X38Original.

Definition min_degree_spanning_subgraph_small_degree_multiplicity_statement : Prop :=
  forall (delta : nat) (G : sgraph),
    Legacy.x38_min_degree_at_least G delta ->
    exists F : {set {set G}},
      F \subset x38_edge_set G /\
      forall k : nat,
        (delta.+1 * @A10.X38Legacy.degree_class_size G F k <= #|G| + 2 * delta.+1)%N.

End X38Original.

Lemma x38_min_degree_at_least_compat (G : sgraph) (delta : nat) :
  Legacy.x38_min_degree_at_least G delta <->
  x38_min_degree_at_least G delta.
Proof. exact: iff_refl. Qed.

Lemma x74_min_degree_at_least_compat (G : sgraph) (d : nat) :
  Legacy.x74_min_degree_at_least G d <->
  x74_min_degree_at_least G d.
Proof. exact: iff_refl. Qed.

Lemma min_degree_spanning_subgraph_small_degree_multiplicity_statement_compat :
  X38Legacy.min_degree_spanning_subgraph_small_degree_multiplicity_statement <->
  min_degree_spanning_subgraph_small_degree_multiplicity_statement.
Proof. exact: iff_refl. Qed.

Lemma induced_linear_forest_caro_wei_bound_statement_compat :
  X74Legacy.induced_linear_forest_caro_wei_bound_statement <->
  induced_linear_forest_caro_wei_bound_statement.
Proof. exact: iff_refl. Qed.

Lemma min_degree_spanning_subgraph_small_degree_multiplicity_statement_original_compat :
  X38Original.min_degree_spanning_subgraph_small_degree_multiplicity_statement <->
  min_degree_spanning_subgraph_small_degree_multiplicity_statement.
Proof. exact: A10.min_degree_spanning_subgraph_small_degree_multiplicity_statement_compat. Qed.
