(** A21 set pairs (extremal): the frozen X57, X58 and X223 disjoint anticomplete pairs and D2ram's complete pair, X57's
    sparse strong Erdos-Hajnal chain, the four rows, and the complete X57 and X58 rows.  Baseline, hashes and exact
    substitutions are recorded in meta/migration_reports/set_pairs.spec.json.
    - [Legacy]: the X57/X58/X223 conjunctions [[disjoint A & B] /\ (a -- b -> False for cross pairs)] are equivalent
      to [GTBase.set_pairs.anticomplete A B] by [anticompleteP]; D2ram's [[disjoint A & B] /\ (forall cross pairs,
      a -- b)] is equivalent to [complete_between A B] by [disjoint_complete_betweenP], whose bridge proves the
      disjointness from cross completeness.  Iffs, not conversions; no nonempty guard is added.
    - [X57Legacy], [X58Legacy], [X223Legacy], [D2ramLegacy]: the chain and rows over the frozen helpers: X57's
      high-degree OR linear pair alternative and iff with forests; X58's Delta bound and its asymmetric power/linear
      bounds; X223's triangle-freeness and closed-neighbourhood bound (not X58's Delta predicate); D2ram's
      complete-in-G OR complete-in-[compl G] on the same parts, with no nonempty condition.  A1's induced-freeness stays
      live in the X57/X58 per-row copies.
    - [X57Original], [X58Original] (texts at the pre-migration 9e03072): over A1's frozen induced-freeness and the
      frozen pair.  A1's module is aliased, not imported; the bridges reuse its certificates. *)
From Corelib Require Import Setoid Morphisms.
From GTBase Require Import base set_pairs.
From Extremal.conjectures Require Import X57 X58 X223 D2ram.
From Extremal.migration Require induced_free.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** A1's certificate module, aliased without Import: its module names coincide with this file's. *)
Module A1 := Extremal.migration.induced_free.

(** [[/\ _, _ & _]] is a morphism for iff, so the frozen pieces can be rewritten inside it. *)
#[local] Instance and3_iff_morphism : Proper (iff ==> iff ==> iff ==> iff) and3.
Proof. by move=> a a' ha b b' hb c c' hc; split=> -[x y z]; split; by [apply/ha|apply/hb|apply/hc]. Qed.

Module Legacy.

Definition x57_anticomplete (G : sgraph) (A B : {set G}) : Prop :=
  [disjoint A & B] /\
  forall a b : G, a \in A -> b \in B -> a -- b -> False.

Definition x58_anticomplete (G : sgraph) (A B : {set G}) : Prop :=
  [disjoint A & B] /\
  forall a b : G, a \in A -> b \in B -> a -- b -> False.

Definition x223_anticomplete (G : sgraph) (A B : {set G}) : Prop :=
  [disjoint A & B] /\ forall a b : G, a \in A -> b \in B -> a -- b -> False.

Definition complete_bipartite_sub (G : sgraph) (A B : {set G}) : Prop :=
  [disjoint A & B] /\ (forall a b : G, a \in A -> b \in B -> a -- b).

End Legacy.

Module X57Legacy.

Definition x57_sparse_strong_eh_property (H : sgraph) : Prop :=
  exists eps_num eps_den : nat,
    0 < eps_num /\ eps_num <= eps_den /\
    forall G : sgraph,
      2 <= #|G| ->
      x57_induced_free G H ->
      (exists v : G, eps_num * #|G| <= eps_den * #|N(v)|) \/
      (exists A B : {set G},
        Legacy.x57_anticomplete A B /\
        eps_num * #|G| <= eps_den * #|A| /\
        eps_num * #|G| <= eps_den * #|B|).

Definition sparse_strong_eh_iff_forest_statement : Prop :=
  forall H : sgraph,
    X57Legacy.x57_sparse_strong_eh_property H <-> is_forest [set: H].

End X57Legacy.

Module X58Legacy.

Definition epsilon_bounded_h_free_anticomplete_pair_statement : Prop :=
  forall H : sgraph,
    exists eps_num eps_den : nat,
      0 < eps_num /\ eps_num <= eps_den /\
      forall G : sgraph,
        1 < #|G| ->
        x58_induced_free G H ->
        x58_epsilon_bounded G eps_num eps_den ->
        exists A B : {set G},
          Legacy.x58_anticomplete A B /\
          eps_num ^ eps_den * #|G| ^ eps_num <= eps_den ^ eps_den * #|A| ^ eps_den /\
          eps_num * #|G| <= eps_den * #|B|.

End X58Legacy.

Module X223Legacy.

Definition triangle_free_eps_bounded_anticomplete_pair_statement : Prop :=
  exists p d : nat,
    [/\ 0 < p, p <= d &
        forall G : sgraph,
          1 < #|G| ->
          induced_free G 'K_3 ->
          x223_eps_bounded G p d ->
          exists A B : {set G},
            [/\ Legacy.x223_anticomplete A B,
                p ^ d * #|G| ^ p <= d ^ d * #|A| ^ d &
                p * #|G| <= d * #|B|]].

End X223Legacy.

Module D2ramLegacy.

Definition complete_bipartite_subgraphs_of_perfect_graphs_statement : Prop :=
  forall a b : nat, (0 < a)%N -> (a < b)%N ->
    exists N : nat, forall (G : sgraph) (n : nat),
      #|G| = n -> (N <= n)%N -> perfect_graph G ->
      exists A B : {set G},
        (Legacy.complete_bipartite_sub A B
           /\ (n ^ (b - a) <= #|A| ^ b)%N /\ (n ^ (b - a) <= #|B| ^ b)%N)
        \/
        (@Legacy.complete_bipartite_sub (compl G) A B
           /\ (n ^ (b - a) <= #|A| ^ b)%N /\ (n ^ (b - a) <= #|B| ^ b)%N).

End D2ramLegacy.

Module X57Original.

Definition x57_sparse_strong_eh_property (H : sgraph) : Prop :=
  exists eps_num eps_den : nat,
    0 < eps_num /\ eps_num <= eps_den /\
    forall G : sgraph,
      2 <= #|G| ->
      A1.Legacy.x57_induced_free G H ->
      (exists v : G, eps_num * #|G| <= eps_den * #|N(v)|) \/
      (exists A B : {set G},
        Legacy.x57_anticomplete A B /\
        eps_num * #|G| <= eps_den * #|A| /\
        eps_num * #|G| <= eps_den * #|B|).

Definition sparse_strong_eh_iff_forest_statement : Prop :=
  forall H : sgraph,
    X57Original.x57_sparse_strong_eh_property H <-> is_forest [set: H].

End X57Original.

Module X58Original.

Definition epsilon_bounded_h_free_anticomplete_pair_statement : Prop :=
  forall H : sgraph,
    exists eps_num eps_den : nat,
      0 < eps_num /\ eps_num <= eps_den /\
      forall G : sgraph,
        1 < #|G| ->
        A1.Legacy.x58_induced_free G H ->
        x58_epsilon_bounded G eps_num eps_den ->
        exists A B : {set G},
          Legacy.x58_anticomplete A B /\
          eps_num ^ eps_den * #|G| ^ eps_num <= eps_den ^ eps_den * #|A| ^ eps_den /\
          eps_num * #|G| <= eps_den * #|B|.

End X58Original.

(** Not conversions: the raw conjunctions against the Boolean pairs, by reflection. *)
Lemma x57_anticomplete_compat (G : sgraph) (A B : {set G}) :
  Legacy.x57_anticomplete A B <-> x57_anticomplete A B.
Proof.
exact: (rwP (anticompleteP A B)).
Qed.

Lemma x58_anticomplete_compat (G : sgraph) (A B : {set G}) :
  Legacy.x58_anticomplete A B <-> x58_anticomplete A B.
Proof.
exact: (rwP (anticompleteP A B)).
Qed.

Lemma x223_anticomplete_compat (G : sgraph) (A B : {set G}) :
  Legacy.x223_anticomplete A B <-> x223_anticomplete A B.
Proof.
exact: (rwP (anticompleteP A B)).
Qed.

(** D2ram's explicit disjointness is implied by cross completeness ([complete_between_disjoint]). *)
Lemma complete_bipartite_sub_compat (G : sgraph) (A B : {set G}) :
  Legacy.complete_bipartite_sub A B <-> complete_bipartite_sub A B.
Proof.
exact: (rwP (disjoint_complete_betweenP A B)).
Qed.

Lemma x57_sparse_strong_eh_property_compat (H : sgraph) :
  X57Legacy.x57_sparse_strong_eh_property H <-> x57_sparse_strong_eh_property H.
Proof.
rewrite /X57Legacy.x57_sparse_strong_eh_property /x57_sparse_strong_eh_property.
setoid_rewrite x57_anticomplete_compat.
reflexivity.
Qed.

Lemma sparse_strong_eh_iff_forest_statement_compat :
  X57Legacy.sparse_strong_eh_iff_forest_statement <-> sparse_strong_eh_iff_forest_statement.
Proof.
rewrite /X57Legacy.sparse_strong_eh_iff_forest_statement /sparse_strong_eh_iff_forest_statement.
setoid_rewrite x57_sparse_strong_eh_property_compat.
reflexivity.
Qed.

Lemma epsilon_bounded_h_free_anticomplete_pair_statement_compat :
  X58Legacy.epsilon_bounded_h_free_anticomplete_pair_statement <->
  epsilon_bounded_h_free_anticomplete_pair_statement.
Proof.
rewrite /X58Legacy.epsilon_bounded_h_free_anticomplete_pair_statement
  /epsilon_bounded_h_free_anticomplete_pair_statement.
setoid_rewrite x58_anticomplete_compat.
reflexivity.
Qed.

Lemma triangle_free_eps_bounded_anticomplete_pair_statement_compat :
  X223Legacy.triangle_free_eps_bounded_anticomplete_pair_statement <->
  triangle_free_eps_bounded_anticomplete_pair_statement.
Proof.
rewrite /X223Legacy.triangle_free_eps_bounded_anticomplete_pair_statement
  /triangle_free_eps_bounded_anticomplete_pair_statement.
setoid_rewrite x223_anticomplete_compat.
reflexivity.
Qed.

(** Both branches, in G and in [compl G], on the same supplied parts. *)
Lemma complete_bipartite_subgraphs_of_perfect_graphs_statement_compat :
  D2ramLegacy.complete_bipartite_subgraphs_of_perfect_graphs_statement <->
  complete_bipartite_subgraphs_of_perfect_graphs_statement.
Proof.
rewrite /D2ramLegacy.complete_bipartite_subgraphs_of_perfect_graphs_statement
  /complete_bipartite_subgraphs_of_perfect_graphs_statement.
setoid_rewrite complete_bipartite_sub_compat.
reflexivity.
Qed.

(** Complete X57 and X58: the frozen pair is rewritten, then A1's certificates for its frozen induced-freeness. *)
Lemma x57_sparse_strong_eh_property_original_compat (H : sgraph) :
  X57Original.x57_sparse_strong_eh_property H <-> x57_sparse_strong_eh_property H.
Proof.
rewrite /X57Original.x57_sparse_strong_eh_property.
setoid_rewrite x57_anticomplete_compat.
exact: A1.x57_sparse_strong_eh_property_compat H.
Qed.

Lemma sparse_strong_eh_iff_forest_statement_original_compat :
  X57Original.sparse_strong_eh_iff_forest_statement <-> sparse_strong_eh_iff_forest_statement.
Proof.
rewrite /X57Original.sparse_strong_eh_iff_forest_statement /sparse_strong_eh_iff_forest_statement.
setoid_rewrite x57_sparse_strong_eh_property_original_compat.
reflexivity.
Qed.

Lemma epsilon_bounded_h_free_anticomplete_pair_statement_original_compat :
  X58Original.epsilon_bounded_h_free_anticomplete_pair_statement <->
  epsilon_bounded_h_free_anticomplete_pair_statement.
Proof.
rewrite /X58Original.epsilon_bounded_h_free_anticomplete_pair_statement.
setoid_rewrite x58_anticomplete_compat.
exact: A1.x58_statement_compat.
Qed.

(** Complete original: raw C12 perfection and raw A21 pair contract. *)
From Extremal.migration Require perfect_graphs.
Module C12 := Extremal.migration.perfect_graphs.

Module D2ramOriginal.

Definition complete_bipartite_subgraphs_of_perfect_graphs_statement : Prop :=
  forall a b : nat, (0 < a)%N -> (a < b)%N ->
    exists N : nat, forall (G : sgraph) (n : nat),
      #|G| = n -> (N <= n)%N -> C12.Legacy.perfect_graph G ->
      exists A B : {set G},
        (Legacy.complete_bipartite_sub A B
           /\ (n ^ (b - a) <= #|A| ^ b)%N /\ (n ^ (b - a) <= #|B| ^ b)%N)
        \/
        (@Legacy.complete_bipartite_sub (compl G) A B
           /\ (n ^ (b - a) <= #|A| ^ b)%N /\ (n ^ (b - a) <= #|B| ^ b)%N).

End D2ramOriginal.

Lemma complete_bipartite_subgraphs_of_perfect_graphs_statement_original_compat :
  D2ramOriginal.complete_bipartite_subgraphs_of_perfect_graphs_statement <-> complete_bipartite_subgraphs_of_perfect_graphs_statement.
Proof.
apply: (iff_trans _ C12.complete_bipartite_subgraphs_of_perfect_graphs_statement_compat).
unfold D2ramOriginal.complete_bipartite_subgraphs_of_perfect_graphs_statement, C12.Legacy.complete_bipartite_subgraphs_of_perfect_graphs_statement.
setoid_rewrite complete_bipartite_sub_compat.
reflexivity.
Qed.
