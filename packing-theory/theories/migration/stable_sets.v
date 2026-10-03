(** A20 stable sets (packing): the frozen X18 independent set and XE1 stable set, XE1's triangle-free independence
    guarantee, the X18 and XE1 #151 rows, and the complete #151 row.  Baseline, hashes and exact substitutions are
    recorded in meta/migration_reports/stable_sets.spec.json.
    - [Legacy]: X18's and XE1's [x -- y -> False] for all supplied pairs are equivalent to upstream [stable S] by
      [GTBase.stable_sets.stable_noedgeP] (iffs, not conversions).
    - [X18Legacy], [XE1Legacy]: X18's ordinal path graph and partition with arbitrary n and m, the common S and b, both
      natural inequalities and every [b i <= 1]; #151's greatest guaranteed stable size and natural subtraction.  A18's
      attained clique-transversal minimum stays live in the per-row #151 copy.
    - [XE1Original] (text at the pre-migration 9e03072): #151 over A18's frozen clique-transversal chain and the frozen
      guarantee.  A18's module is aliased, not imported; the bridge reuses its certificate. *)
From Corelib Require Import Setoid Morphisms.
From GTBase Require Import base stable_sets.
From Packing.conjectures Require Import X18 XE1.
From Packing.migration Require maximal_cliques.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** A18's certificate module, aliased without Import: its module names coincide with this file's. *)
Module A18 := Packing.migration.maximal_cliques.

Module Legacy.

Definition x18_independent_set (G : sgraph) (S : {set G}) : Prop :=
  forall u v : G, u \in S -> v \in S -> u -- v -> False.

Definition xe1_stable_set (G : sgraph) (S : {set G}) : Prop :=
  forall x y : G, x \in S -> y \in S -> x -- y -> False.

End Legacy.

Module X18Legacy.

Definition path_partition_independent_set_balance_statement : Prop :=
  forall (n m : nat) (V : 'I_m -> {set x18_path_graph n}),
    x18_vertex_partition V ->
    exists (S : {set x18_path_graph n}) (b : 'I_m -> nat),
      Legacy.x18_independent_set S /\
      (forall i : 'I_m, 2 * (#|S :&: V i| + b i) >= #|V i|)%N /\
      (2 * \sum_(i : 'I_m) b i <= m)%N /\
      forall i : 'I_m, b i <= 1.

End X18Legacy.

Module XE1Legacy.

Definition xe1_triangle_free_independence_guarantee (n h : nat) : Prop :=
  (forall G : sgraph,
      #|G| = n -> triangle_free G ->
      exists A : {set G}, Legacy.xe1_stable_set A /\ h <= #|A|) /\
  forall h' : nat,
    (forall G : sgraph,
      #|G| = n -> triangle_free G ->
      exists A : {set G}, Legacy.xe1_stable_set A /\ h' <= #|A|) -> h' <= h.

Definition erdos_151_statement : Prop :=
  forall (G : sgraph) (n h t : nat),
    #|G| = n ->
    XE1Legacy.xe1_triangle_free_independence_guarantee n h ->
    xe1_clique_transversal_number G t ->
    t <= n - h.

End XE1Legacy.

Module XE1Original.

Definition erdos_151_statement : Prop :=
  forall (G : sgraph) (n h t : nat),
    #|G| = n ->
    XE1Legacy.xe1_triangle_free_independence_guarantee n h ->
    A18.XE1Legacy.xe1_clique_transversal_number G t ->
    t <= n - h.

End XE1Original.

(** Not conversions: the raw [edge -> False] presentations against the upstream Boolean, by reflection. *)
Lemma x18_independent_set_compat (G : sgraph) (S : {set G}) :
  Legacy.x18_independent_set S <-> x18_independent_set S.
Proof.
exact: (rwP (stable_noedgeP S)).
Qed.

Lemma xe1_stable_set_compat (G : sgraph) (S : {set G}) :
  Legacy.xe1_stable_set S <-> xe1_stable_set S.
Proof.
exact: (rwP (stable_noedgeP S)).
Qed.

(** The same ordinal carrier, partition and witnesses S and b. *)
Lemma path_partition_independent_set_balance_statement_compat :
  X18Legacy.path_partition_independent_set_balance_statement <->
  path_partition_independent_set_balance_statement.
Proof.
rewrite /X18Legacy.path_partition_independent_set_balance_statement /path_partition_independent_set_balance_statement.
setoid_rewrite x18_independent_set_compat.
reflexivity.
Qed.

Lemma xe1_triangle_free_independence_guarantee_compat (n h : nat) :
  XE1Legacy.xe1_triangle_free_independence_guarantee n h <-> xe1_triangle_free_independence_guarantee n h.
Proof.
rewrite /XE1Legacy.xe1_triangle_free_independence_guarantee /xe1_triangle_free_independence_guarantee.
setoid_rewrite xe1_stable_set_compat.
reflexivity.
Qed.

Lemma erdos_151_statement_compat :
  XE1Legacy.erdos_151_statement <-> erdos_151_statement.
Proof.
rewrite /XE1Legacy.erdos_151_statement /erdos_151_statement.
setoid_rewrite xe1_triangle_free_independence_guarantee_compat.
reflexivity.
Qed.

(** Complete #151: the frozen guarantee is rewritten, then A18's certificate for its frozen transversal chain. *)
Lemma erdos_151_statement_original_compat :
  XE1Original.erdos_151_statement <-> erdos_151_statement.
Proof.
rewrite /XE1Original.erdos_151_statement.
setoid_rewrite xe1_triangle_free_independence_guarantee_compat.
exact: A18.erdos_151_statement_compat.
Qed.
