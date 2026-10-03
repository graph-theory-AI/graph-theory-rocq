(** A9 cut sizes: the frozen X76/X78 graph cut sizes and rows, then the complete rows. Baseline,
    hashes and exact substitutions are recorded in meta/migration_reports/cut_size.spec.json.
    - [Legacy]: the two cut sizes at the baseline (post-M1: they count over M1's alias edge sets,
      which convert to [E(G)]; [x76_cut_size_compat] and [x78_cut_size_compat] are conversions).
    - [X76Legacy], [X78Legacy]: the rows over these frozen cut sizes; A7's counts and A5's
      containment stay live there.
    - [X76Original], [X78Original]: the complete rows, pre-M1.  The cut sizes are the 061154c bodies
      over M1's frozen comprehension (bridged by M1's certificates); the counts are A7's pre-M1 copies
      and X78's containment is A5's frozen helper. *)
From Corelib Require Import Setoid Morphisms.
From GTBase Require Import base.
From Extremal.conjectures Require Import X76 X78.
From Extremal.migration Require simple_edges subgraph_of edge_count.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Earlier families' certificate modules, aliased without Import: their module names coincide
    with this file's. *)
Module M1 := Extremal.migration.simple_edges.
Module A5 := Extremal.migration.subgraph_of.
Module A7 := Extremal.migration.edge_count.

#[local] Instance and3_iff_morphism : Proper (iff ==> iff ==> iff ==> iff) and3.
Proof. by move=> a a' ha b b' hb c c' hc; split=> -[x y z]; split; by [apply/ha|apply/hb|apply/hc]. Qed.

#[local] Instance and4_iff_morphism : Proper (iff ==> iff ==> iff ==> iff ==> iff) and4.
Proof.
by move=> a a' ha b b' hb c c' hc d d' hd; split=> -[x y z w]; split;
  by [apply/ha|apply/hb|apply/hc|apply/hd].
Qed.

Module Legacy.

Definition x76_cut_size (G : sgraph) (A : {set G}) : nat :=
  #|[set e in x76_edge_set G | ~~ [disjoint e & A] && ~~ (e \subset A)]|.

Definition x78_cut_size (G : sgraph) (A : {set G}) : nat :=
  #|[set e in x78_edge_set G | ~~ [disjoint e & A] && ~~ (e \subset A)]|.

End Legacy.

Module X76Legacy.

Definition ck_free_max_cut_polynomial_surplus_statement : Prop :=
  forall k : nat,
    3 <= k ->
    exists cnum cden N : nat,
      [/\ 0 < cnum, 0 < cden
        & forall (G : sgraph) (m : nat),
            N <= m ->
            x76_edge_count G = m ->
            ~ x76_has_cycle_length G k ->
            exists (A : {set G}) (s : nat),
              x76_power_surplus k cnum cden m s /\
              m + 2 * s <= 2 * Legacy.x76_cut_size A].

End X76Legacy.

Module X78Legacy.

Definition h_free_max_cut_three_fourths_surplus_statement : Prop :=
  forall H : sgraph,
    exists cnum cden N : nat,
      [/\ 0 < cnum, 0 < cden
        & forall (G : sgraph) (m : nat),
            N <= m ->
            x78_edge_count G = m ->
            ~ x78_subgraph_of H G ->
            exists (A : {set G}) (s : nat),
              x78_three_fourths_surplus cnum cden m s /\
              m + 2 * s <= 2 * Legacy.x78_cut_size A].

End X78Legacy.

Module X76Original.

Definition x76_cut_size (G : sgraph) (A : {set G}) : nat :=
  #|[set e in M1.Legacy.edge_set G | ~~ [disjoint e & A] && ~~ (e \subset A)]|.

Definition ck_free_max_cut_polynomial_surplus_statement : Prop :=
  forall k : nat,
    3 <= k ->
    exists cnum cden N : nat,
      [/\ 0 < cnum, 0 < cden
        & forall (G : sgraph) (m : nat),
            N <= m ->
            A7.X76Original.x76_edge_count G = m ->
            ~ x76_has_cycle_length G k ->
            exists (A : {set G}) (s : nat),
              x76_power_surplus k cnum cden m s /\
              m + 2 * s <= 2 * X76Original.x76_cut_size A].

End X76Original.

Module X78Original.

Definition x78_cut_size (G : sgraph) (A : {set G}) : nat :=
  #|[set e in M1.Legacy.edge_set G | ~~ [disjoint e & A] && ~~ (e \subset A)]|.

Definition h_free_max_cut_three_fourths_surplus_statement : Prop :=
  forall H : sgraph,
    exists cnum cden N : nat,
      [/\ 0 < cnum, 0 < cden
        & forall (G : sgraph) (m : nat),
            N <= m ->
            A7.X78Original.x78_edge_count G = m ->
            ~ A5.Legacy.x78_subgraph_of H G ->
            exists (A : {set G}) (s : nat),
              x78_three_fourths_surplus cnum cden m s /\
              m + 2 * s <= 2 * X78Original.x78_cut_size A].

End X78Original.

Lemma x76_cut_size_compat (G : sgraph) (A : {set G}) : Legacy.x76_cut_size A = x76_cut_size A.
Proof. by []. Qed.

Lemma x78_cut_size_compat (G : sgraph) (A : {set G}) : Legacy.x78_cut_size A = x78_cut_size A.
Proof. by []. Qed.

Lemma ck_free_max_cut_polynomial_surplus_statement_compat :
  X76Legacy.ck_free_max_cut_polynomial_surplus_statement <-> ck_free_max_cut_polynomial_surplus_statement.
Proof. exact: iff_refl. Qed.

Lemma h_free_max_cut_three_fourths_surplus_statement_compat :
  X78Legacy.h_free_max_cut_three_fourths_surplus_statement <-> h_free_max_cut_three_fourths_surplus_statement.
Proof. exact: iff_refl. Qed.

Lemma x76_cut_size_original_compat (G : sgraph) (A : {set G}) :
  X76Original.x76_cut_size A = x76_cut_size A.
Proof. by rewrite /X76Original.x76_cut_size M1.x76_edge_set_compat. Qed.

Lemma ck_free_max_cut_polynomial_surplus_statement_original_compat :
  X76Original.ck_free_max_cut_polynomial_surplus_statement <-> ck_free_max_cut_polynomial_surplus_statement.
Proof. rewrite /X76Original.ck_free_max_cut_polynomial_surplus_statement /ck_free_max_cut_polynomial_surplus_statement; setoid_rewrite x76_cut_size_original_compat; setoid_rewrite A7.x76_edge_count_original_compat; reflexivity. Qed.

Lemma x78_cut_size_original_compat (G : sgraph) (A : {set G}) :
  X78Original.x78_cut_size A = x78_cut_size A.
Proof. by rewrite /X78Original.x78_cut_size M1.x78_edge_set_compat. Qed.

Lemma h_free_max_cut_three_fourths_surplus_statement_original_compat :
  X78Original.h_free_max_cut_three_fourths_surplus_statement <-> h_free_max_cut_three_fourths_surplus_statement.
Proof. rewrite /X78Original.h_free_max_cut_three_fourths_surplus_statement /h_free_max_cut_three_fourths_surplus_statement; setoid_rewrite x78_cut_size_original_compat; setoid_rewrite A7.x78_edge_count_original_compat; setoid_rewrite A5.x78_subgraph_of_compat; reflexivity. Qed.
