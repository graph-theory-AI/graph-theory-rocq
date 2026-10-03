(** * Extremal.migration.cycle_lengths — frozen raw cycle-length existence of X59 and X76, and the
    X59/X76/X96 rows (library migration B15)

    Batch B, family [cycle-lengths] (meta/library_primitives/cycle-lengths.json).  [Legacy]
    freezes, verbatim as they stood at the B15 baseline 4b63976, X59's and X76's RAW existence
    [exists c, ucycle (--) c /\ size c = n]: no length guard, so raw length 0 is always witnessed
    and raw length 2 is an edge.  The live helpers now unfold to
    [GTBase.walks_paths.has_ucycle_length (--) n], whose body is this term, so every certificate
    is a kernel-checked conversion; the genuine view is only reached through the explicit guard
    [2 < n] ([has_ucycle_lengthE]), which the rows satisfy (length 4; X76's [3 <= k]) but the
    helpers do not assume.  [X59Legacy], [X76Legacy] and [X96Legacy] freeze the three rows and
    X96's cross-file chain [c4_free] with this family's helpers only; A5's containment, A7's
    counts and A9's cut size stay live there.

    History (complete rows, over the earlier families' frozen copies, aliased without Import):
    - [X59Original] (A5+B15): A5's frozen [x59_subgraph_of] and this family's frozen existence;
      convertible to A5's X59 row, so A5's certificate certifies it.
    - [X76Original] (A7+A9+B15, pre-M1): A7's frozen pre-M1 count [A7.X76Original.x76_edge_count]
      and A9's pre-M1 cut size [A9.X76Original.x76_cut_size] (both over M1's frozen edge set) and
      this family's frozen existence; convertible to A9's complete X76 Original, so A9's
      certificate certifies it.
    - [X96Original] (A5+A7+B15): A7's frozen raw rank count, A5's frozen containment and this
      family's frozen chain; convertible to A7's complete X96 Original, so A7's certificate
      certifies it.
    The A5, A7 and A9 per-row snapshots still call live helpers of this family and are documented
    reciprocally.  Hashes and substitutions: meta/migration_reports/cycle_lengths.md. *)

From GTBase Require Import base.
From Extremal.conjectures Require Import X4 X59 X76 X96.
From Extremal.migration Require subgraph_of edge_count cut_size.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** The earlier families' frozen copies, without Import. *)
Module A5 := Extremal.migration.subgraph_of.
Module A7 := Extremal.migration.edge_count.
Module A9 := Extremal.migration.cut_size.

Module Legacy.

Definition x59_has_cycle_length (G : sgraph) (n : nat) : Prop :=
  exists c : seq G, ucycle (--) c /\ size c = n.

Definition x76_has_cycle_length (G : sgraph) (k : nat) : Prop :=
  exists c : seq G, ucycle (--) c /\ size c = k.

End Legacy.

Module X59Legacy.

Definition c4_free_subgraph_polynomial_average_degree_statement : Prop :=
  exists p : seq nat,
    forall (k : nat) (G : sgraph),
      average_degree_geq G (x59_poly_eval p k) 1 ->
      exists H : sgraph,
        x59_subgraph_of H G /\
        ~ Legacy.x59_has_cycle_length H 4 /\
        average_degree_geq H k 1.

End X59Legacy.

Module X59Original.

Definition c4_free_subgraph_polynomial_average_degree_statement : Prop :=
  exists p : seq nat,
    forall (k : nat) (G : sgraph),
      average_degree_geq G (x59_poly_eval p k) 1 ->
      exists H : sgraph,
        A5.Legacy.x59_subgraph_of H G /\
        ~ Legacy.x59_has_cycle_length H 4 /\
        average_degree_geq H k 1.

End X59Original.

Module X76Legacy.

Definition ck_free_max_cut_polynomial_surplus_statement : Prop :=
  forall k : nat,
    3 <= k ->
    exists cnum cden N : nat,
      [/\ 0 < cnum, 0 < cden
        & forall (G : sgraph) (m : nat),
            N <= m ->
            x76_edge_count G = m ->
            ~ Legacy.x76_has_cycle_length G k ->
            exists (A : {set G}) (s : nat),
              x76_power_surplus k cnum cden m s /\
              m + 2 * s <= 2 * x76_cut_size A].

End X76Legacy.

Module X76Original.

Definition ck_free_max_cut_polynomial_surplus_statement : Prop :=
  forall k : nat,
    3 <= k ->
    exists cnum cden N : nat,
      [/\ 0 < cnum, 0 < cden
        & forall (G : sgraph) (m : nat),
            N <= m ->
            A7.X76Original.x76_edge_count G = m ->
            ~ Legacy.x76_has_cycle_length G k ->
            exists (A : {set G}) (s : nat),
              x76_power_surplus k cnum cden m s /\
              m + 2 * s <= 2 * A9.X76Original.x76_cut_size A].

End X76Original.

Module X96Legacy.

Definition c4_free (G : sgraph) : Prop :=
  ~ Legacy.x59_has_cycle_length G 4.

Definition bollobas_erdos_large_c4_free_subgraph_statement : Prop :=
  exists cnum cden : nat,
    [/\ 0 < cnum, 0 < cden
      & forall (m : nat) (G : sgraph),
          x4_edge_count G = m ->
          exists H : sgraph,
            [/\ x59_subgraph_of H G,
                c4_free H
              & x96_m_three_fourths_lower cnum cden m (x4_edge_count H)]].

End X96Legacy.

Module X96Original.

Definition bollobas_erdos_large_c4_free_subgraph_statement : Prop :=
  exists cnum cden : nat,
    [/\ 0 < cnum, 0 < cden
      & forall (m : nat) (G : sgraph),
          A7.Legacy.x4_edge_count G = m ->
          exists H : sgraph,
            [/\ A5.Legacy.x59_subgraph_of H G,
                X96Legacy.c4_free H
              & x96_m_three_fourths_lower cnum cden m (A7.Legacy.x4_edge_count H)]].

End X96Original.

(** ** Certificates *)

Lemma x59_has_cycle_length_compat (G : sgraph) (n : nat) :
  Legacy.x59_has_cycle_length G n <-> x59_has_cycle_length G n.
Proof. exact: iff_refl. Qed.

Lemma x76_has_cycle_length_compat (G : sgraph) (k : nat) :
  Legacy.x76_has_cycle_length G k <-> x76_has_cycle_length G k.
Proof. exact: iff_refl. Qed.

Lemma c4_free_subgraph_polynomial_average_degree_statement_compat :
  X59Legacy.c4_free_subgraph_polynomial_average_degree_statement <->
  c4_free_subgraph_polynomial_average_degree_statement.
Proof. exact: iff_refl. Qed.

(** Before A5 and B15: A5's frozen containment and this family's frozen existence (A5's
    certificate, by conversion). *)
Lemma c4_free_subgraph_polynomial_average_degree_statement_original_compat :
  X59Original.c4_free_subgraph_polynomial_average_degree_statement <->
  c4_free_subgraph_polynomial_average_degree_statement.
Proof. exact: A5.c4_free_subgraph_polynomial_average_degree_statement_compat. Qed.

Lemma ck_free_max_cut_polynomial_surplus_statement_compat :
  X76Legacy.ck_free_max_cut_polynomial_surplus_statement <-> ck_free_max_cut_polynomial_surplus_statement.
Proof. exact: iff_refl. Qed.

(** Before M1, A7, A9 and B15: the pre-M1 count and cut size with this family's frozen existence
    (A9's complete certificate, by conversion). *)
Lemma ck_free_max_cut_polynomial_surplus_statement_original_compat :
  X76Original.ck_free_max_cut_polynomial_surplus_statement <-> ck_free_max_cut_polynomial_surplus_statement.
Proof. exact: A9.ck_free_max_cut_polynomial_surplus_statement_original_compat. Qed.

Lemma x96_c4_free_compat (G : sgraph) : X96Legacy.c4_free G <-> x96_c4_free G.
Proof. exact: iff_refl. Qed.

Lemma bollobas_erdos_large_c4_free_subgraph_statement_compat :
  X96Legacy.bollobas_erdos_large_c4_free_subgraph_statement <-> bollobas_erdos_large_c4_free_subgraph_statement.
Proof. exact: iff_refl. Qed.

(** Before A5, A7 and B15: A7's frozen raw rank count, A5's frozen containment and this family's
    frozen chain (A7's complete certificate, by conversion). *)
Lemma bollobas_erdos_large_c4_free_subgraph_statement_original_compat :
  X96Original.bollobas_erdos_large_c4_free_subgraph_statement <-> bollobas_erdos_large_c4_free_subgraph_statement.
Proof. exact: A7.bollobas_erdos_large_c4_free_subgraph_statement_original_compat. Qed.

Print Assumptions x59_has_cycle_length_compat.
Print Assumptions x76_has_cycle_length_compat.
Print Assumptions c4_free_subgraph_polynomial_average_degree_statement_compat.
Print Assumptions c4_free_subgraph_polynomial_average_degree_statement_original_compat.
Print Assumptions ck_free_max_cut_polynomial_surplus_statement_compat.
Print Assumptions ck_free_max_cut_polynomial_surplus_statement_original_compat.
Print Assumptions bollobas_erdos_large_c4_free_subgraph_statement_compat.
Print Assumptions bollobas_erdos_large_c4_free_subgraph_statement_original_compat.
