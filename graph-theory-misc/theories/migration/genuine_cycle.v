(** * GTMisc.migration.genuine_cycle — frozen genuine cycles of X113 and XE1 #883
    (library migration B10)

    Batch B, family [genuine-cycle] (meta/library_primitives/genuine-cycle.json).
    [Legacy] freezes, verbatim as they stood at the B10 baseline 00d6bb3, X113's
    [x113_is_cycle] ([ucycle (--) c /\ 2 < size c]) and XE1's generic
    [xe1_rel_cycle] over an ARBITRARY supplied relation [r : rel V] on a finite
    carrier ([ucycle r c /\ 2 < size c]).  The live helpers now unfold to
    [GTBase.walks_paths.seq_cycle (--) c] and [seq_cycle r c]; no symmetry or
    looplessness is added to the generic one.  The certificates are kernel-checked
    conversions; vocabulary_misc's [x113_is_cycleE] and
    [x113_is_cycle_equiv_xe1_rel_cycle] keep their statements.  [X113Legacy] freezes
    the distant-cycles and forest-after chain and the coarse Erdos-Posa row;
    [XE1Legacy] the small odd coprime cycles predicate and #883.

    History.  [X113Original] gives the complete X113 chain and row before B1 and B10:
    B1's frozen pairwise-distance predicate and vertex set
    (GTMisc.migration.path_vertices) with this family's frozen cycle.  It is
    convertible with B1's own certificates, which it reuses; B1's X113Legacy copies
    are unchanged.  Hashes and substitutions: meta/migration_reports/genuine_cycle.md. *)

From GTBase Require Import base.
From GTMisc.conjectures Require Import X113 XE1.
From GTMisc.migration Require path_vertices.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Legacy.

Definition x113_is_cycle (G : sgraph) (c : seq G) : Prop :=
  ucycle (--) c /\ 2 < size c.

Definition xe1_rel_cycle (V : finType) (r : rel V) (c : seq V) : Prop :=
  ucycle r c /\ 2 < size c.

End Legacy.

Module X113Legacy.

Definition has_k_distant_cycles
    (G : sgraph) (d k : nat) : Prop :=
  exists cs : seq (seq G),
    size cs = k /\
    uniq cs /\
    (forall c : seq G, c \in cs -> Legacy.x113_is_cycle c) /\
    x113_pairwise_distant_cycles d cs.

Definition is_forest_after
    (G : sgraph) (A : {set G}) : Prop :=
  forall c : seq G,
    Legacy.x113_is_cycle c ->
    [disjoint x113_path_vertices c & A] ->
    False.

Definition coarse_erdos_posa_cycles_forest_statement : Prop :=
  exists f g : nat -> nat,
    forall (k d : nat) (G : sgraph),
      1 <= k -> 1 <= d ->
      has_k_distant_cycles G d k \/
      exists X : {set G},
        #|X| <= f k /\
        is_forest_after (x113_set_ball (g d) X).

End X113Legacy.

Module X113Original.

Definition has_k_distant_cycles
    (G : sgraph) (d k : nat) : Prop :=
  exists cs : seq (seq G),
    size cs = k /\
    uniq cs /\
    (forall c : seq G, c \in cs -> Legacy.x113_is_cycle c) /\
    GTMisc.migration.path_vertices.X113Legacy.pairwise_distant_cycles d cs.

Definition is_forest_after
    (G : sgraph) (A : {set G}) : Prop :=
  forall c : seq G,
    Legacy.x113_is_cycle c ->
    [disjoint GTMisc.migration.path_vertices.Legacy.x113_path_vertices c & A] ->
    False.

Definition coarse_erdos_posa_cycles_forest_statement : Prop :=
  exists f g : nat -> nat,
    forall (k d : nat) (G : sgraph),
      1 <= k -> 1 <= d ->
      has_k_distant_cycles G d k \/
      exists X : {set G},
        #|X| <= f k /\
        is_forest_after (x113_set_ball (g d) X).

End X113Original.

Module XE1Legacy.

Definition all_small_odd_coprime_cycles (n : nat) (A : {set 'I_n}) : Prop :=
  forall ell : nat,
    odd ell -> 3 <= ell -> ell <= n %/ 3 + 1 ->
    exists c : seq 'I_n,
      Legacy.xe1_rel_cycle (@xe1_coprime_adj n) c /\
      size c = ell /\
      forall x : 'I_n, x \in c -> x \in A.

Definition erdos_883_statement : Prop :=
  (forall n : nat, forall A : {set 'I_n},
      #|A| > n %/ 2 + n %/ 3 - n %/ 6 ->
      all_small_odd_coprime_cycles A) /\
  (forall ell : nat, 1 <= ell ->
      exists N : nat,
        forall n : nat, N <= n ->
        forall A : {set 'I_n},
          #|A| > n %/ 2 + n %/ 3 - n %/ 6 ->
          xe1_complete_tripartite_1_l_l ell A).

End XE1Legacy.

(** ** Certificates *)

Lemma x113_is_cycle_compat (G : sgraph) (c : seq G) : Legacy.x113_is_cycle c = x113_is_cycle c.
Proof. by []. Qed.

Lemma xe1_rel_cycle_compat (V : finType) (r : rel V) (c : seq V) :
  Legacy.xe1_rel_cycle r c = xe1_rel_cycle r c.
Proof. by []. Qed.

Lemma x113_has_k_distant_cycles_compat (G : sgraph) (d k : nat) :
  X113Legacy.has_k_distant_cycles G d k <-> x113_has_k_distant_cycles G d k.
Proof. exact: iff_refl. Qed.

Lemma x113_is_forest_after_compat (G : sgraph) (A : {set G}) :
  X113Legacy.is_forest_after A <-> x113_is_forest_after A.
Proof. exact: iff_refl. Qed.

Lemma coarse_erdos_posa_cycles_forest_statement_compat :
  X113Legacy.coarse_erdos_posa_cycles_forest_statement <-> coarse_erdos_posa_cycles_forest_statement.
Proof. exact: iff_refl. Qed.

(** Before B1 and B10: convertible with B1's certificates. *)
Lemma x113_has_k_distant_cycles_original_compat (G : sgraph) (d k : nat) :
  X113Original.has_k_distant_cycles G d k <-> x113_has_k_distant_cycles G d k.
Proof. exact: GTMisc.migration.path_vertices.x113_has_k_distant_cycles_compat. Qed.

Lemma x113_is_forest_after_original_compat (G : sgraph) (A : {set G}) :
  X113Original.is_forest_after A <-> x113_is_forest_after A.
Proof. exact: GTMisc.migration.path_vertices.x113_is_forest_after_compat. Qed.

Lemma coarse_erdos_posa_cycles_forest_statement_original_compat :
  X113Original.coarse_erdos_posa_cycles_forest_statement <-> coarse_erdos_posa_cycles_forest_statement.
Proof. exact: GTMisc.migration.path_vertices.coarse_erdos_posa_cycles_forest_statement_compat. Qed.

Lemma xe1_all_small_odd_coprime_cycles_compat (n : nat) (A : {set 'I_n}) :
  XE1Legacy.all_small_odd_coprime_cycles A <-> xe1_all_small_odd_coprime_cycles A.
Proof. exact: iff_refl. Qed.

Lemma erdos_883_statement_compat : XE1Legacy.erdos_883_statement <-> erdos_883_statement.
Proof. exact: iff_refl. Qed.

Print Assumptions x113_is_cycle_compat.
Print Assumptions xe1_rel_cycle_compat.
Print Assumptions coarse_erdos_posa_cycles_forest_statement_compat.
Print Assumptions coarse_erdos_posa_cycles_forest_statement_original_compat.
Print Assumptions erdos_883_statement_compat.
