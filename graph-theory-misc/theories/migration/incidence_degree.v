(** A10 incidence degree: the frozen X37/X38 counts of the members of a supplied family containing
    a vertex, their degree-class chains and the two rows.  Baseline, hashes and exact substitutions
    are recorded in meta/migration_reports/incidence_degree.spec.json.
    - [Legacy]: the two counts at the baseline, over an ARBITRARY family [F : {set {set G}}]; their
      certificates are conversions to [GTBase.incidence.incidence_degree].
    - [X37Legacy], [X38Legacy]: the chains and rows over these frozen counts.  The M1 edge-set
      aliases and every other helper stay live (no pre-M1 claim). *)
From GTBase Require Import base.
From GTMisc.conjectures Require Import X37 X38.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Legacy.

Definition x37_subgraph_degree
    (G : sgraph) (F : {set {set G}}) (v : G) : nat :=
  #|[set e in F | v \in e]|.

Definition x38_subgraph_degree
    (G : sgraph) (F : {set {set G}}) (v : G) : nat :=
  #|[set e in F | v \in e]|.

End Legacy.

Module X37Legacy.

Definition degree_class_size
    (G : sgraph) (F : {set {set G}}) (k : nat) : nat :=
  #|[set v : G | Legacy.x37_subgraph_degree F v == k]|.

Definition close_to_uniform_degree_class
    (G : sgraph) (d : nat) (F : {set {set G}}) (k : nat) : Prop :=
  let m := degree_class_size F k in
  (d.+1 * m <= #|G| + 2 * d.+1)%N /\
  (#|G| <= d.+1 * (m + 2))%N.

Definition regular_graph_spanning_subgraph_degree_class_balance_statement : Prop :=
  forall (d : nat) (G : sgraph),
    regular G d ->
    exists F : {set {set G}},
      F \subset x37_edge_set G /\
      forall k : nat,
        k <= d ->
        @close_to_uniform_degree_class G d F k.

End X37Legacy.

Module X38Legacy.

Definition degree_class_size
    (G : sgraph) (F : {set {set G}}) (k : nat) : nat :=
  #|[set v : G | Legacy.x38_subgraph_degree F v == k]|.

Definition min_degree_spanning_subgraph_small_degree_multiplicity_statement : Prop :=
  forall (delta : nat) (G : sgraph),
    x38_min_degree_at_least G delta ->
    exists F : {set {set G}},
      F \subset x38_edge_set G /\
      forall k : nat,
        (delta.+1 * @degree_class_size G F k <= #|G| + 2 * delta.+1)%N.

End X38Legacy.

(** The two counts convert to [incidence_degree]; so does every chain and row below. *)
Lemma x37_subgraph_degree_compat (G : sgraph) (F : {set {set G}}) (v : G) :
  Legacy.x37_subgraph_degree F v = x37_subgraph_degree F v.
Proof. by []. Qed.

Lemma x38_subgraph_degree_compat (G : sgraph) (F : {set {set G}}) (v : G) :
  Legacy.x38_subgraph_degree F v = x38_subgraph_degree F v.
Proof. by []. Qed.

Lemma x37_degree_class_size_compat (G : sgraph) (F : {set {set G}}) (k : nat) :
  X37Legacy.degree_class_size F k = x37_degree_class_size F k.
Proof. by []. Qed.

Lemma x37_close_to_uniform_degree_class_compat (G : sgraph) (d : nat) (F : {set {set G}}) (k : nat) :
  X37Legacy.close_to_uniform_degree_class d F k <-> x37_close_to_uniform_degree_class d F k.
Proof. exact: iff_refl. Qed.

Lemma regular_graph_spanning_subgraph_degree_class_balance_statement_compat :
  X37Legacy.regular_graph_spanning_subgraph_degree_class_balance_statement <->
  regular_graph_spanning_subgraph_degree_class_balance_statement.
Proof. exact: iff_refl. Qed.

Lemma x38_degree_class_size_compat (G : sgraph) (F : {set {set G}}) (k : nat) :
  X38Legacy.degree_class_size F k = x38_degree_class_size F k.
Proof. by []. Qed.

Lemma min_degree_spanning_subgraph_small_degree_multiplicity_statement_compat :
  X38Legacy.min_degree_spanning_subgraph_small_degree_multiplicity_statement <->
  min_degree_spanning_subgraph_small_degree_multiplicity_statement.
Proof. exact: iff_refl. Qed.
