(** A20 stable sets (chromatic): the frozen X3 and XE1 stable sets, XE2's cochromatic chain, the X3, X7 and XE2
    #758/#762/#922 rows, and the complete X3 and #762 rows.  Baseline, hashes and exact substitutions are recorded in
    meta/migration_reports/stable_sets.spec.json.
    - [Legacy]: X3's and XE1's [x -- y -> False] for all supplied pairs are equivalent to upstream [stable S] by
      [GTBase.stable_sets.stable_noedgeP] (an iff, not a conversion); no nonempty or size guard is added.
    - [XE2Legacy], [X3Legacy], [X7Legacy]: the cochromatic colouring over a finite ordinal palette (empty colour classes
      allowed), its attained minimum and the attained maximum on n vertices, and the five rows over the frozen helpers.
      X3's outer [forall s, exists n], arbitrary cover index and common path witness, X7's [5 <= k], [omega < 5] and
      [chi = k + 3], #758's 12/4, #762's K_5 exclusion and [4 <= z], and #922's universal subset premise are verbatim.
      B3's induced path, B1's path support and A5's subgraph relation stay live in these per-row copies.
    - [X3Original], [XE2Original] (texts at the pre-migration 9e03072): X3 over B3's frozen induced path, B1's frozen
      path support and the frozen stable set; #762 over A5's frozen subgraph relation and the frozen cochromatic chain.
      B1's, B3's and A5's modules are aliased, not imported; the bridges reuse their certificates. *)
From Corelib Require Import Setoid Morphisms.
From GTBase Require Import base stable_sets.
From Chromatic.conjectures Require Import X3 XE1 XE2 X7.
From Chromatic.migration Require path_vertices consecutive_in_path subgraph_of.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** B1's, B3's and A5's certificate modules, aliased without Import: their module names coincide with this file's. *)
Module B1 := Chromatic.migration.path_vertices.
Module B3 := Chromatic.migration.consecutive_in_path.
Module A5 := Chromatic.migration.subgraph_of.

Module Legacy.

Definition x3_stable_set (G : sgraph) (S : {set G}) : Prop :=
  forall u v : G, u \in S -> v \in S -> u -- v -> False.

Definition xe1_stable_set (G : sgraph) (S : {set G}) : Prop :=
  forall x y : G, x \in S -> y \in S -> x -- y -> False.

End Legacy.

Module XE2Legacy.

Definition xe2_cochromatic_colouring (G : sgraph) (k : nat) : Prop :=
  exists col : G -> 'I_k,
    forall i : 'I_k,
      let S := [set v : G | col v == i] in
      clique S \/ Legacy.xe1_stable_set S.

Definition xe2_cochromatic_number (G : sgraph) (k : nat) : Prop :=
  XE2Legacy.xe2_cochromatic_colouring G k /\
  forall j : nat, XE2Legacy.xe2_cochromatic_colouring G j -> k <= j.

Definition xe2_max_cochromatic_on_n (n z : nat) : Prop :=
  (exists G : sgraph, #|G| = n /\ XE2Legacy.xe2_cochromatic_number G z) /\
  forall z' : nat,
    (exists G : sgraph, #|G| = n /\ XE2Legacy.xe2_cochromatic_number G z') -> z' <= z.

Definition erdos_758_statement : Prop :=
  XE2Legacy.xe2_max_cochromatic_on_n 12 4.

Definition erdos_762_statement : Prop :=
  forall (G : sgraph) (z : nat),
    ~ xe1_subgraph_of 'K_5 G ->
    XE2Legacy.xe2_cochromatic_number G z ->
    4 <= z ->
    χ([set: G]) <= z + 2.

Definition erdos_922_statement : Prop :=
  forall (k : nat) (G : sgraph),
    (forall S : {set G}, exists A : {set G},
        A \subset S /\ Legacy.xe1_stable_set A /\
        2 * #|A| + k >= #|S|) ->
    χ([set: G]) <= k + 2.

End XE2Legacy.

Module X3Legacy.

Definition stable_cover_unique_induced_path_statement : Prop :=
  forall s : nat, exists n : nat,
    forall (G : sgraph) (I : finType) (A : I -> {set G}),
      triangle_free G ->
      n <= χ([set: G]) ->
      (forall i : I, Legacy.x3_stable_set (A i)) ->
      x3_family_covers_vertices A ->
      exists p : seq G,
        size p = s /\
        x3_induced_path p /\
        forall v : G, v \in p -> x3_uniquely_covers_path_vertex A p v.

End X3Legacy.

Module X7Legacy.

Definition cochromatic_gap_three_statement : Prop :=
  forall k : nat, 5 <= k ->
    exists G : sgraph,
      ω([set: G]) < 5 /\
      XE2Legacy.xe2_cochromatic_number G k /\
      χ([set: G]) = k + 3.

End X7Legacy.

Module X3Original.

Definition stable_cover_unique_induced_path_statement : Prop :=
  forall s : nat, exists n : nat,
    forall (G : sgraph) (I : finType) (A : I -> {set G}),
      triangle_free G ->
      n <= χ([set: G]) ->
      (forall i : I, Legacy.x3_stable_set (A i)) ->
      x3_family_covers_vertices A ->
      exists p : seq G,
        size p = s /\
        B3.X3Legacy.induced_path p /\
        forall v : G, v \in p -> B1.X3Legacy.uniquely_covers_path_vertex A p v.

End X3Original.

Module XE2Original.

Definition erdos_762_statement : Prop :=
  forall (G : sgraph) (z : nat),
    ~ A5.Legacy.xe1_subgraph_of 'K_5 G ->
    XE2Legacy.xe2_cochromatic_number G z ->
    4 <= z ->
    χ([set: G]) <= z + 2.

End XE2Original.

(** Not conversions: the raw [edge -> False] presentations against the upstream Boolean, by reflection. *)
Lemma x3_stable_set_compat (G : sgraph) (S : {set G}) :
  Legacy.x3_stable_set S <-> x3_stable_set S.
Proof.
exact: (rwP (stable_noedgeP S)).
Qed.

Lemma xe1_stable_set_compat (G : sgraph) (S : {set G}) :
  Legacy.xe1_stable_set S <-> xe1_stable_set S.
Proof.
exact: (rwP (stable_noedgeP S)).
Qed.

(** The colour classes are the same sets for the same palette map; only their stability is rewritten. *)
Lemma xe2_cochromatic_colouring_compat (G : sgraph) (k : nat) :
  XE2Legacy.xe2_cochromatic_colouring G k <-> xe2_cochromatic_colouring G k.
Proof.
split=> -[col h]; exists col => i; case: (h i) => [cl|st]; [by left | right | by left | right].
- exact/xe1_stable_set_compat.
- exact/xe1_stable_set_compat.
Qed.

Lemma xe2_cochromatic_number_compat (G : sgraph) (k : nat) :
  XE2Legacy.xe2_cochromatic_number G k <-> xe2_cochromatic_number G k.
Proof.
rewrite /XE2Legacy.xe2_cochromatic_number /xe2_cochromatic_number.
setoid_rewrite xe2_cochromatic_colouring_compat.
reflexivity.
Qed.

Lemma xe2_max_cochromatic_on_n_compat (n z : nat) :
  XE2Legacy.xe2_max_cochromatic_on_n n z <-> xe2_max_cochromatic_on_n n z.
Proof.
rewrite /XE2Legacy.xe2_max_cochromatic_on_n /xe2_max_cochromatic_on_n.
setoid_rewrite xe2_cochromatic_number_compat.
reflexivity.
Qed.

Lemma erdos_758_statement_compat :
  XE2Legacy.erdos_758_statement <-> erdos_758_statement.
Proof.
rewrite /XE2Legacy.erdos_758_statement /erdos_758_statement.
setoid_rewrite xe2_max_cochromatic_on_n_compat.
reflexivity.
Qed.

Lemma erdos_762_statement_compat :
  XE2Legacy.erdos_762_statement <-> erdos_762_statement.
Proof.
rewrite /XE2Legacy.erdos_762_statement /erdos_762_statement.
setoid_rewrite xe2_cochromatic_number_compat.
reflexivity.
Qed.

Lemma erdos_922_statement_compat :
  XE2Legacy.erdos_922_statement <-> erdos_922_statement.
Proof.
rewrite /XE2Legacy.erdos_922_statement /erdos_922_statement.
setoid_rewrite xe1_stable_set_compat.
reflexivity.
Qed.

Lemma stable_cover_unique_induced_path_statement_compat :
  X3Legacy.stable_cover_unique_induced_path_statement <->
  stable_cover_unique_induced_path_statement.
Proof.
rewrite /X3Legacy.stable_cover_unique_induced_path_statement /stable_cover_unique_induced_path_statement.
setoid_rewrite x3_stable_set_compat.
reflexivity.
Qed.

Lemma cochromatic_gap_three_statement_compat :
  X7Legacy.cochromatic_gap_three_statement <-> cochromatic_gap_three_statement.
Proof.
rewrite /X7Legacy.cochromatic_gap_three_statement /cochromatic_gap_three_statement.
setoid_rewrite xe2_cochromatic_number_compat.
reflexivity.
Qed.

(** Complete X3: the frozen stable set is rewritten, then B3's complete-row certificate (B3's induced path and B1's path
    support convert to the live ones). *)
Lemma stable_cover_unique_induced_path_statement_original_compat :
  X3Original.stable_cover_unique_induced_path_statement <->
  stable_cover_unique_induced_path_statement.
Proof.
rewrite /X3Original.stable_cover_unique_induced_path_statement.
setoid_rewrite x3_stable_set_compat.
exact: B3.stable_cover_unique_induced_path_statement_original_compat.
Qed.

(** Complete #762: the frozen cochromatic chain is rewritten, then A5's certificate for its frozen subgraph relation. *)
Lemma erdos_762_statement_original_compat :
  XE2Original.erdos_762_statement <-> erdos_762_statement.
Proof.
rewrite /XE2Original.erdos_762_statement.
setoid_rewrite xe2_cochromatic_number_compat.
exact: A5.erdos_762_statement_compat.
Qed.
