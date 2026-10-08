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
From Extremal.conjectures Require Import X84 X85.
From Extremal.migration Require subgraph_of edge_count cut_size.
From Extremal.migration Require simple_edges incidence_degree.

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

(** ** B29 (2026-10-04): X84's edge-family cycles

    Since B29 the X84 helpers [x84_cycle_edge_set], [x84_cycle_count] and [x84_has_cycle_length] are aliases of
    [Extremal.foundations.edge_cycles] ([edge_family_cycle], [edge_family_cycle_count],
    [has_edge_family_cycle_length]), the same bodies by conversion: the five conjuncts in order (host edges, support
    larger than two, as many members as support vertices, incidence degree two, connected support) over an arbitrary
    supplied family.  [X84EdgeLegacy] / [X85EdgeLegacy] freeze them and the two complete current rows at the
    family baseline 4b63976, keeping the live M1 / A10 aliases and the unchanged local support vocabulary.
    [X84EdgeOriginal] / [X85EdgeOriginal] freeze the pre-M1 support, relation and connectivity of 061154c, the cycle,
    count and length chains and both rows over M1's raw [Legacy.edge_set] and A10's raw [Legacy.x84_degree_in]
    (aliased, not imported); their certificates use M1's proved set equality [x84_edge_set_compat] and A10's
    conversion [x84_degree_in_compat], and transport the rows pointwise with the same family and witnesses. *)

Module M1 := Extremal.migration.simple_edges.
Module ID := Extremal.migration.incidence_degree.

Module X84EdgeLegacy.

Definition cycle_edge_set (G : sgraph) (F : {set {set G}}) : bool :=
  [&& F \subset x84_edge_set G,
      2 < #|x84_support F|,
      #|F| == #|x84_support F|,
      [forall v in x84_support F, x84_degree_in F v == 2]
    & x84_connected_support F].

Definition cycle_count (G : sgraph) : nat :=
  #|[set F : {set {set G}} | @cycle_edge_set G F]|.

Definition has_cycle_length (G : sgraph) (l : nat) : Prop :=
  exists F : {set {set G}},
    @cycle_edge_set G F /\ #|x84_support F| = l.

Definition odd_cycle_free_turan2_unique_cycle_extremal_statement : Prop :=
  forall k : nat, 1 < k ->
  exists N : nat, forall n : nat, N <= n ->
    ~ has_cycle_length (x84_turan2 n) (2 * k + 1) /\
    forall G : sgraph, #|G| = n ->
      ~ has_cycle_length G (2 * k + 1) ->
      cycle_count G <= cycle_count (x84_turan2 n) /\
      (cycle_count G = cycle_count (x84_turan2 n) ->
         inhabited (G ≃ x84_turan2 n)).

End X84EdgeLegacy.

Module X85EdgeLegacy.

Definition arman_tsaturian_average_degree_cycle_count_statement : Prop :=
  exists c den N : nat,
    [/\ 0 < c, 1 < den &
      forall (n d : nat) (G : sgraph),
        N <= d -> #|G| = n -> x85_average_degree_exact G d ->
        x85_log_corrected_exponential_bound c den n d (X84EdgeLegacy.cycle_count G)].

End X85EdgeLegacy.

Module X84EdgeOriginal.

Definition support (G : sgraph) (F : {set {set G}}) : {set G} :=
  [set v : G | [exists e in F, v \in e]].

Definition edge_rel (G : sgraph) (F : {set {set G}}) : rel G :=
  fun x y => [set x; y] \in F.

Definition connected_support (G : sgraph) (F : {set {set G}}) : bool :=
  [forall x in support F,
    [forall y in support F, connect (edge_rel F) x y]].

Definition cycle_edge_set (G : sgraph) (F : {set {set G}}) : bool :=
  [&& F \subset M1.Legacy.edge_set G,
      2 < #|support F|,
      #|F| == #|support F|,
      [forall v in support F, ID.Legacy.x84_degree_in F v == 2]
    & connected_support F].

Definition cycle_count (G : sgraph) : nat :=
  #|[set F : {set {set G}} | @cycle_edge_set G F]|.

Definition has_cycle_length (G : sgraph) (l : nat) : Prop :=
  exists F : {set {set G}},
    @cycle_edge_set G F /\ #|support F| = l.

Definition odd_cycle_free_turan2_unique_cycle_extremal_statement : Prop :=
  forall k : nat, 1 < k ->
  exists N : nat, forall n : nat, N <= n ->
    ~ has_cycle_length (x84_turan2 n) (2 * k + 1) /\
    forall G : sgraph, #|G| = n ->
      ~ has_cycle_length G (2 * k + 1) ->
      cycle_count G <= cycle_count (x84_turan2 n) /\
      (cycle_count G = cycle_count (x84_turan2 n) ->
         inhabited (G ≃ x84_turan2 n)).

End X84EdgeOriginal.

Module X85EdgeOriginal.

Definition arman_tsaturian_average_degree_cycle_count_statement : Prop :=
  exists c den N : nat,
    [/\ 0 < c, 1 < den &
      forall (n d : nat) (G : sgraph),
        N <= d -> #|G| = n -> x85_average_degree_exact G d ->
        x85_log_corrected_exponential_bound c den n d (X84EdgeOriginal.cycle_count G)].

End X85EdgeOriginal.

(** *** B29 current sources and rows: conversions *)

Lemma x84_cycle_edge_set_compat (G : sgraph) (F : {set {set G}}) :
  X84EdgeLegacy.cycle_edge_set F = x84_cycle_edge_set F.
Proof. by []. Qed.

Lemma x84_cycle_count_compat (G : sgraph) : X84EdgeLegacy.cycle_count G = x84_cycle_count G.
Proof. by []. Qed.

Lemma x84_has_cycle_length_compat (G : sgraph) (l : nat) :
  X84EdgeLegacy.has_cycle_length G l <-> x84_has_cycle_length G l.
Proof. exact: iff_refl. Qed.

Lemma odd_cycle_free_turan2_unique_cycle_extremal_statement_compat :
  X84EdgeLegacy.odd_cycle_free_turan2_unique_cycle_extremal_statement <->
  odd_cycle_free_turan2_unique_cycle_extremal_statement.
Proof. exact: iff_refl. Qed.

Lemma arman_tsaturian_average_degree_cycle_count_statement_compat :
  X85EdgeLegacy.arman_tsaturian_average_degree_cycle_count_statement <->
  arman_tsaturian_average_degree_cycle_count_statement.
Proof. exact: iff_refl. Qed.

(** *** Before M1, A10 and B29: the raw local vocabulary and the complete rows *)

Lemma x84_support_frozen_compat (G : sgraph) (F : {set {set G}}) :
  X84EdgeOriginal.support F = x84_support F.
Proof. by []. Qed.

Lemma x84_edge_rel_frozen_compat (G : sgraph) (F : {set {set G}}) :
  X84EdgeOriginal.edge_rel F = x84_edge_rel F.
Proof. by []. Qed.

Lemma x84_connected_support_frozen_compat (G : sgraph) (F : {set {set G}}) :
  X84EdgeOriginal.connected_support F = x84_connected_support F.
Proof. by []. Qed.

(** M1's raw edge set is the host edge set by a proved set equality; A10's raw degree is the incidence degree by
    conversion. *)
Lemma x84_cycle_edge_set_original_compat (G : sgraph) (F : {set {set G}}) :
  X84EdgeOriginal.cycle_edge_set F = x84_cycle_edge_set F.
Proof. by rewrite /X84EdgeOriginal.cycle_edge_set M1.x84_edge_set_compat. Qed.

Lemma x84_cycle_count_original_compat (G : sgraph) : X84EdgeOriginal.cycle_count G = x84_cycle_count G.
Proof. by apply: eq_card => F; rewrite !inE x84_cycle_edge_set_original_compat. Qed.

Lemma x84_has_cycle_length_original_compat (G : sgraph) (l : nat) :
  X84EdgeOriginal.has_cycle_length G l <-> x84_has_cycle_length G l.
Proof.
split=> -[F [cF sF]]; exists F; split=> //.
  by move: cF; rewrite x84_cycle_edge_set_original_compat.
by rewrite x84_cycle_edge_set_original_compat.
Qed.

Lemma odd_cycle_free_turan2_unique_cycle_extremal_statement_original_compat :
  X84EdgeOriginal.odd_cycle_free_turan2_unique_cycle_extremal_statement <->
  odd_cycle_free_turan2_unique_cycle_extremal_statement.
Proof.
split=> h k k1; have [N hN] := h k k1; exists N => n Nn; have [nt hG] := hN n Nn; split.
- by move=> hl; apply: nt; apply/x84_has_cycle_length_original_compat.
- move=> G cG nG; rewrite -!x84_cycle_count_original_compat; apply: hG => // hx; apply: nG.
  exact/x84_has_cycle_length_original_compat.
- by move=> hl; apply: nt; apply/x84_has_cycle_length_original_compat.
- move=> G cG nG; rewrite !x84_cycle_count_original_compat; apply: hG => // hx; apply: nG.
  exact/x84_has_cycle_length_original_compat.
Qed.

Lemma arman_tsaturian_average_degree_cycle_count_statement_original_compat :
  X85EdgeOriginal.arman_tsaturian_average_degree_cycle_count_statement <->
  arman_tsaturian_average_degree_cycle_count_statement.
Proof.
split=> -[c [den [N [c0 d1 h]]]]; exists c, den, N; split=> // n d G Nd nG avg.
  by rewrite -x84_cycle_count_original_compat; apply: h.
by rewrite x84_cycle_count_original_compat; apply: h.
Qed.

Print Assumptions x84_cycle_edge_set_compat.
Print Assumptions x84_cycle_count_compat.
Print Assumptions x84_has_cycle_length_compat.
Print Assumptions odd_cycle_free_turan2_unique_cycle_extremal_statement_compat.
Print Assumptions arman_tsaturian_average_degree_cycle_count_statement_compat.
Print Assumptions x84_support_frozen_compat.
Print Assumptions x84_edge_rel_frozen_compat.
Print Assumptions x84_connected_support_frozen_compat.
Print Assumptions x84_cycle_edge_set_original_compat.
Print Assumptions x84_cycle_count_original_compat.
Print Assumptions x84_has_cycle_length_original_compat.
Print Assumptions odd_cycle_free_turan2_unique_cycle_extremal_statement_original_compat.
Print Assumptions arman_tsaturian_average_degree_cycle_count_statement_original_compat.
