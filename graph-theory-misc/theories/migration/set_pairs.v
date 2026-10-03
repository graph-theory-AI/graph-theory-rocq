(** A21 set pairs (graph-theory-misc): the frozen X41 and X144 raw complete and raw anticomplete pairs, both pure-pair
    chains, the two rows, and the complete X41 row.  Baseline, hashes and exact substitutions are recorded in
    meta/migration_reports/set_pairs.spec.json.
    - [Legacy]: the raw anticomplete pairs [forall cross pairs, ~~ (a -- b)] (no disjointness) are equivalent to
      upstream [~~ neighbor A B] by [GTBase.set_pairs.neighborNP]; the raw complete pairs [forall cross pairs, a -- b]
      to [complete_between A B] by [complete_betweenP].  Iffs, not conversions; no disjointness or nonempty guard is
      added.
    - [X41Legacy], [X144Legacy]: each pure pair keeps its own explicit disjointness, both nonemptiness conditions and
      the complete-OR-anticomplete alternative; the rows keep X41's documented sublinear A-side bound and X144's ordered
      [0 < e1 < e2], threshold, perfection and both power bounds.  A1's induced-H-freeness stays live in the per-row X41
      copy.
    - [X41Original] (text at the pre-migration 9e03072): over A1's frozen induced-H-freeness and the frozen pure pair.
      A1's module is aliased, not imported; the bridge reuses its certificate. *)
From Corelib Require Import Setoid Morphisms.
From GTBase Require Import base set_pairs.
From GTMisc.conjectures Require Import X41 X144.
From GTMisc.migration Require induced_free.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** A1's certificate module, aliased without Import: its module names coincide with this file's. *)
Module A1 := GTMisc.migration.induced_free.

Module Legacy.

Definition x41_anticomplete_between (G : sgraph) (A B : {set G}) : Prop :=
  forall a b : G, a \in A -> b \in B -> ~~ (a -- b).

Definition x41_complete_between (G : sgraph) (A B : {set G}) : Prop :=
  forall a b : G, a \in A -> b \in B -> a -- b.

Definition x144_anticomplete_between (G : sgraph) (A B : {set G}) : Prop :=
  forall a b : G, a \in A -> b \in B -> ~~ (a -- b).

Definition x144_complete_between (G : sgraph) (A B : {set G}) : Prop :=
  forall a b : G, a \in A -> b \in B -> a -- b.

End Legacy.

Module X41Legacy.

Definition x41_pure_pair (G : sgraph) (A B : {set G}) : Prop :=
  [disjoint A & B] /\
  A != set0 /\
  B != set0 /\
  (Legacy.x41_complete_between A B \/ Legacy.x41_anticomplete_between A B).

Definition sparse_linear_pure_pair_statement : Prop :=
  forall H : sgraph, exists eps_num eps_den : nat,
    0 < eps_num /\
    eps_num <= eps_den /\
    forall G : sgraph,
      1 < #|G| ->
      x41_induced_H_free H G ->
      exists A B : {set G},
        X41Legacy.x41_pure_pair A B /\
        eps_den ^ eps_den * #|A| ^ eps_den >= eps_num ^ eps_den * #|G| ^ eps_num /\
        eps_den * #|B| >= eps_num * #|G|.

End X41Legacy.

Module X144Legacy.

Definition x144_pure_pair (G : sgraph) (A B : {set G}) : Prop :=
  [disjoint A & B] /\
  A != set0 /\
  B != set0 /\
  (Legacy.x144_complete_between A B \/ Legacy.x144_anticomplete_between A B).

Definition fox_pure_pair_perfect_graphs_statement : Prop :=
  forall e1 e2 : nat,
    0 < e1 ->
    e1 < e2 ->
    exists N : nat,
      forall (n : nat) (G : sgraph),
        N <= n ->
        #|G| = n ->
        x144_perfect_graph G ->
        exists A B : {set G},
          X144Legacy.x144_pure_pair A B /\
          n ^ (e2 - e1) <= #|A| ^ e2 /\
          n ^ (e2 - e1) <= #|B| ^ e2.

End X144Legacy.

Module X41Original.

Definition sparse_linear_pure_pair_statement : Prop :=
  forall H : sgraph, exists eps_num eps_den : nat,
    0 < eps_num /\
    eps_num <= eps_den /\
    forall G : sgraph,
      1 < #|G| ->
      A1.Legacy.x41_induced_H_free H G ->
      exists A B : {set G},
        X41Legacy.x41_pure_pair A B /\
        eps_den ^ eps_den * #|A| ^ eps_den >= eps_num ^ eps_den * #|G| ^ eps_num /\
        eps_den * #|B| >= eps_num * #|G|.

End X41Original.

(** Not conversions: the raw bounded quantifications against the Boolean pairs, by reflection. *)
Lemma x41_anticomplete_between_compat (G : sgraph) (A B : {set G}) :
  Legacy.x41_anticomplete_between A B <-> x41_anticomplete_between A B.
Proof.
exact: (rwP (neighborNP A B)).
Qed.

Lemma x41_complete_between_compat (G : sgraph) (A B : {set G}) :
  Legacy.x41_complete_between A B <-> x41_complete_between A B.
Proof.
exact: (rwP (complete_betweenP A B)).
Qed.

Lemma x144_anticomplete_between_compat (G : sgraph) (A B : {set G}) :
  Legacy.x144_anticomplete_between A B <-> x144_anticomplete_between A B.
Proof.
exact: (rwP (neighborNP A B)).
Qed.

Lemma x144_complete_between_compat (G : sgraph) (A B : {set G}) :
  Legacy.x144_complete_between A B <-> x144_complete_between A B.
Proof.
exact: (rwP (complete_betweenP A B)).
Qed.

Lemma x41_pure_pair_compat (G : sgraph) (A B : {set G}) :
  X41Legacy.x41_pure_pair A B <-> x41_pure_pair A B.
Proof.
rewrite /X41Legacy.x41_pure_pair /x41_pure_pair.
setoid_rewrite x41_complete_between_compat.
setoid_rewrite x41_anticomplete_between_compat.
reflexivity.
Qed.

Lemma sparse_linear_pure_pair_statement_compat :
  X41Legacy.sparse_linear_pure_pair_statement <-> sparse_linear_pure_pair_statement.
Proof.
rewrite /X41Legacy.sparse_linear_pure_pair_statement /sparse_linear_pure_pair_statement.
setoid_rewrite x41_pure_pair_compat.
reflexivity.
Qed.

Lemma x144_pure_pair_compat (G : sgraph) (A B : {set G}) :
  X144Legacy.x144_pure_pair A B <-> x144_pure_pair A B.
Proof.
rewrite /X144Legacy.x144_pure_pair /x144_pure_pair.
setoid_rewrite x144_complete_between_compat.
setoid_rewrite x144_anticomplete_between_compat.
reflexivity.
Qed.

Lemma fox_pure_pair_perfect_graphs_statement_compat :
  X144Legacy.fox_pure_pair_perfect_graphs_statement <-> fox_pure_pair_perfect_graphs_statement.
Proof.
rewrite /X144Legacy.fox_pure_pair_perfect_graphs_statement /fox_pure_pair_perfect_graphs_statement.
setoid_rewrite x144_pure_pair_compat.
reflexivity.
Qed.

(** Complete X41: the frozen pure pair is rewritten, then A1's certificate for its frozen induced-H-freeness. *)
Lemma sparse_linear_pure_pair_statement_original_compat :
  X41Original.sparse_linear_pure_pair_statement <-> sparse_linear_pure_pair_statement.
Proof.
rewrite /X41Original.sparse_linear_pure_pair_statement.
setoid_rewrite x41_pure_pair_compat.
exact: A1.x41_statement_compat.
Qed.
