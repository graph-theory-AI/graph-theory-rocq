(** Frozen C7 source and complete statement declarations; baseline and exact substitutions
    are recorded in meta/migration_reports/bipartition.spec.json. *)
From GTBase Require Import base.
From Digraph Require Import prelude digraph oriented dipath.
From Digraph.conjectures Require Import X46 X53.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module X46Legacy.

Definition x46_bipartition
    (D : diGraphType) (A B : {set D}) (n : nat) : Prop :=
  [disjoint A & B] /\
  A :|: B = [set: D] /\
  #|A| = n /\
  #|B| = n /\
  forall u v : D,
    u --> v ->
    ((u \in A) && (v \in B)) || ((u \in B) && (v \in A)).

Definition bipartite_digraph_outdegree_girth_statement : Prop :=
  forall (k n : nat) (D : diGraphType) (A B : {set D}),
    1 <= k ->
    0 < n ->
    X46Legacy.x46_bipartition A B n ->
    (forall v : D, n < k.+1 * outdeg v) ->
    exists c : seq D,
      dicycle c /\
      size c <= 2 * k.

End X46Legacy.

Module X53Legacy.

Definition x53_bipartition (D : diGraphType) (A B : {set D}) : Prop :=
  [disjoint A & B] /\
  A :|: B = [set: D] /\
  forall u v : D,
    u --> v ->
    ((u \in A) && (v \in B)) || ((u \in B) && (v \in A)).

Definition bipartite_digraph_asymmetric_outdegree_girth_statement : Prop :=
  forall (k alpha_num alpha_den beta_num beta_den : nat),
    1 <= k ->
    x53_positive_rational alpha_num alpha_den ->
    x53_positive_rational beta_num beta_den ->
    x53_k_alpha_plus_beta_gt_one k alpha_num alpha_den beta_num beta_den ->
    forall (D : diGraphType) (A B : {set D}),
      0 < #|D| ->
      X53Legacy.x53_bipartition A B ->
      (forall v : D, v \in A ->
        beta_num * #|B| <= beta_den * x53_out_to B v) ->
      (forall v : D, v \in B ->
        alpha_num * #|A| <= alpha_den * x53_out_to A v) ->
      exists c : seq D,
        dicycle c /\
        size c <= 2 * k.

End X53Legacy.

Lemma x46_bipartition_compat (D : diGraphType) (A B : {set D}) n :
  X46Legacy.x46_bipartition A B n = x46_bipartition A B n.
Proof. by []. Qed.
Lemma bipartite_digraph_outdegree_girth_statement_compat :
  X46Legacy.bipartite_digraph_outdegree_girth_statement <->
  bipartite_digraph_outdegree_girth_statement.
Proof. exact: iff_refl. Qed.
Lemma x53_bipartition_compat (D : diGraphType) (A B : {set D}) :
  X53Legacy.x53_bipartition A B = x53_bipartition A B.
Proof. by []. Qed.
Lemma bipartite_digraph_asymmetric_outdegree_girth_statement_compat :
  X53Legacy.bipartite_digraph_asymmetric_outdegree_girth_statement <->
  bipartite_digraph_asymmetric_outdegree_girth_statement.
Proof. exact: iff_refl. Qed.
