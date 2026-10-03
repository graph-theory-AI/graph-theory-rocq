(** * Extremal.migration.subgraph_of -- frozen ordinary subgraph containment certificates

    Batch A, family A5 (ordinary [subgraph_of] containment), X59, X78, X96, X98 and the extremal XE1/XE2 rows.
    [Legacy] freezes the three helpers verbatim as they stood at 49ddc03 ([x59_],
    [x78_] and the extremal [xe1_subgraph_of]).  [XE1Legacy] freezes the six affected XE1
    chains, prefix dropped ([graph_ramsey], [graph_ramsey_number],
    [diagonal_ramsey_number], [c4_forcing_min_degree], [turan_number_for_graph],
    [min_turan_over_size_edges]), and its thirteen statements; [XE2Legacy] the nine XE2
    statements, which reach XE1 across modules; [X59Legacy], [X78Legacy], [X96Legacy] and
    [X98Legacy] the remaining rows (X96 and X98 reach [x59_subgraph_of] across modules).

    X98 history: B3 (49ddc03) froze X98's subdivision Record and statement in
    [Extremal.migration.consecutive_in_path.X98Legacy]; that snapshot still calls the
    live [x59_subgraph_of], and is documented as a known snapshot in this family's spec.
    [X98Original] is the combined pre-B3, pre-A5 row: B3's frozen Record and this
    family's frozen helper.  Other M1 edge/count aliases in these rows stay live, so no
    row here is claimed to be a pre-M1 original.

    The live helpers now unfold to [GTBase.common.has_subgraph G H], host first (the
    reverse of the local argument order).  [has_subgraphP] proves the unconditional
    witness characterization, so each helper certificate is that iff, and every chain
    and statement certificate transports it through the unchanged statement structure
    by setoid rewriting under the logical connectives.  The local [and3]/[and4]
    instances only add the [[/\ ...]] forms; no axiom is used.  The regeneration spec
    is meta/migration_reports/subgraph_of.spec.json. *)

From GTBase Require Import base.
From Extremal.conjectures Require Import X4 X59 X78 X96 X98 XE1 XE2.
From Extremal.migration Require consecutive_in_path consecutive_in_cycle.
From Corelib Require Import Setoid Morphisms.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

#[local] Instance and3_iff_morphism : Proper (iff ==> iff ==> iff ==> iff) and3.
Proof. by move=> a a' ha b b' hb c c' hc; split=> -[x y z]; split; by [apply/ha|apply/hb|apply/hc]. Qed.

#[local] Instance and4_iff_morphism : Proper (iff ==> iff ==> iff ==> iff ==> iff) and4.
Proof.
move=> a a' ha b b' hb c c' hc d d' hd; split=> -[x y z w]; split;
  by [apply/ha|apply/hb|apply/hc|apply/hd].
Qed.

Module Legacy.

Definition x59_subgraph_of (H G : sgraph) : Prop :=
  exists f : H -> G,
    injective f /\
    forall x y : H, x -- y -> f x -- f y.

Definition x78_subgraph_of (H G : sgraph) : Prop :=
  exists f : H -> G,
    injective f /\
    forall x y : H, x -- y -> f x -- f y.

Definition xe1_subgraph_of (H G : sgraph) : Prop :=
  exists f : H -> G, injective f /\ forall x y : H, x -- y -> f x -- f y.

End Legacy.

Module XE1Legacy.

Definition graph_ramsey (H K : sgraph) (R : nat) : Prop :=
  forall G : sgraph, #|G| = R ->
    Legacy.xe1_subgraph_of H G \/ Legacy.xe1_subgraph_of K (xe1_complement_graph G).

Definition graph_ramsey_number (H K : sgraph) (R : nat) : Prop :=
  graph_ramsey H K R /\
  forall R' : nat, graph_ramsey H K R' -> R <= R'.

Definition diagonal_ramsey_number (H : sgraph) (R : nat) : Prop :=
  graph_ramsey_number H H R.

Definition c4_forcing_min_degree (n f : nat) : Prop :=
  (forall G : sgraph, #|G| = n -> xe1_min_degree_at_least G f -> Legacy.xe1_subgraph_of (cycle_graph 4) G) /\
  forall f' : nat,
    (forall G : sgraph, #|G| = n -> xe1_min_degree_at_least G f' -> Legacy.xe1_subgraph_of (cycle_graph 4) G) ->
    f <= f'.

Definition turan_number_for_graph (F : sgraph) (n m : nat) : Prop :=
  (exists G : sgraph, #|G| = n /\ x4_edge_count G = m /\ ~ Legacy.xe1_subgraph_of F G) /\
  forall m' : nat,
    (exists G : sgraph, #|G| = n /\ x4_edge_count G = m' /\ ~ Legacy.xe1_subgraph_of F G) ->
    m' <= m.

Definition min_turan_over_size_edges (k l n a : nat) : Prop :=
  (exists F : sgraph,
      #|F| = k /\ x4_edge_count F = l /\ turan_number_for_graph F n a) /\
  forall b : nat,
    (exists F : sgraph,
      #|F| = k /\ x4_edge_count F = l /\ turan_number_for_graph F n b) ->
    a <= b.

Definition erdos_1035_statement : Prop :=
  exists c d : nat,
    0 < c /\ c < d /\
    forall n : nat, forall G : sgraph,
      #|G| = 2 ^ n ->
      (forall v : G, d * #|N(v)| > (d - c) * 2 ^ n) ->
      Legacy.xe1_subgraph_of (xe1_hypercube n) G.

Definition erdos_545_statement : Prop :=
  forall (m n t RG RH : nat) (G H : sgraph),
    x4_edge_count G = m -> xe1_no_isolated_vertices G ->
    m = 'C(n, 2) + t -> t < n ->
    xe1_complete_plus_vertex H n t ->
    graph_ramsey_number G G RG ->
    graph_ramsey_number H H RH ->
    RG <= RH.

Definition erdos_548_statement : Prop :=
  forall (n k : nat) (G T : sgraph),
    k.+1 <= n ->
    #|G| = n -> #|T| = k.+1 -> xe1_tree T ->
    2 * x4_edge_count G >= (k - 1) * n + 2 ->
    Legacy.xe1_subgraph_of T G.

Definition erdos_550_statement : Prop :=
  forall (k : nat) (sizes : 'I_k -> nat) (m1 m2 : nat),
    2 <= k ->
    (forall i : 'I_k, 0 < sizes i) ->
    xe1_two_smallest_part_sizes sizes m1 m2 ->
    exists N : nat,
    forall (n RTB RTG : nat) (T G : sgraph),
      N <= n -> xe1_tree T -> #|T| = n ->
      xe1_complete_multipartite_with_sizes G sizes ->
      graph_ramsey_number T (KB m1 m2) RTB ->
      graph_ramsey_number T G RTG ->
      RTG <= (χ([set: G]) - 1) * (RTB - 1) + m1.

Definition erdos_552_statement : Prop :=
  forall c M : nat, exists n R s : nat,
    M <= n /\
    xe1_sqrt_floor n s /\
    graph_ramsey_number (cycle_graph 4) (KB 1 n) R /\
    R + c <= n + s.

Definition erdos_566_statement : Prop :=
  forall G : sgraph,
    (forall k : nat, xe1_every_k_set_sparse G k) ->
    exists C : nat,
      forall (H : sgraph) (m R : nat),
        x4_edge_count H = m -> xe1_no_isolated_vertices H ->
        graph_ramsey_number G H R ->
        R <= C * m.

Definition erdos_567_statement : Prop :=
  forall G : sgraph,
    (G = xe1_hypercube 3 \/ G = KB 3 3 \/ xe1_h5_graph G) ->
    exists C : nat,
      forall (H : sgraph) (m R : nat),
        x4_edge_count H = m -> xe1_no_isolated_vertices H ->
        graph_ramsey_number G H R ->
        R <= C * m.

Definition erdos_568_statement : Prop :=
  forall G : sgraph,
    (exists C1 : nat, forall (n R : nat) (T : sgraph),
      xe1_tree T -> #|T| = n -> graph_ramsey_number G T R -> R <= C1 * n) ->
    (exists C2 : nat, forall (n R : nat),
      graph_ramsey_number G 'K_n R -> R <= C2 * n ^ 2) ->
    exists C : nat, forall (H : sgraph) (m R : nat),
      x4_edge_count H = m -> xe1_no_isolated_vertices H ->
      graph_ramsey_number G H R ->
      R <= C * m.

Definition erdos_766_statement : Prop :=
  forall k l : nat, k < l -> 4 * l.+1 <= k ^ 2 ->
    exists N : nat,
      forall n a b : nat,
        N <= n ->
        min_turan_over_size_edges k l n a ->
        min_turan_over_size_edges k l.+1 n b ->
        a < b.

Definition erdos_802_statement : Prop :=
  forall r : nat, exists C : nat,
    0 < C /\
    forall (G : sgraph) (n t : nat),
      ~ Legacy.xe1_subgraph_of 'K_r G ->
      #|G| = n ->
      \sum_(v in G) #|N(v)| <= t * #|G| ->
      exists A : {set G},
        xe1_stable_set A /\ C * t * #|A| >= n * trunc_log 2 t.

Definition erdos_812_statement : Prop :=
  (exists cnum cden N : nat, 0 < cnum /\ 0 < cden /\
    forall n Rn Rn1 : nat,
      N <= n ->
      graph_ramsey_number 'K_n 'K_n Rn ->
      graph_ramsey_number 'K_n.+1 'K_n.+1 Rn1 ->
      cden * Rn1 >= (cden + cnum) * Rn) /\
  (exists Cnum Cden N : nat, 0 < Cnum /\ 0 < Cden /\
    forall n Rn Rn1 : nat,
      N <= n ->
      graph_ramsey_number 'K_n 'K_n Rn ->
      graph_ramsey_number 'K_n.+1 'K_n.+1 Rn1 ->
      Cden * Rn + Cnum * n ^ 2 <= Cden * Rn1).

Definition erdos_85_statement : Prop :=
  exists N : nat,
    forall n fn fn1 : nat,
      N <= n -> 4 <= n ->
      c4_forcing_min_degree n fn ->
      c4_forcing_min_degree n.+1 fn1 ->
      fn <= fn1.

Definition erdos_87_statement : Prop :=
  exists cnum cden N : nat,
    0 < cnum /\ 0 < cden /\
    forall (k RG RK : nat) (G : sgraph),
      N <= k ->
      χ([set: G]) = k ->
      diagonal_ramsey_number G RG ->
      graph_ramsey_number 'K_k 'K_k RK ->
      cden * RG >= cnum * RK.

End XE1Legacy.

Module XE2Legacy.

Definition erdos_1018_statement : Prop :=
  forall eps_num eps_den : nat,
    0 < eps_num -> 0 < eps_den ->
    exists C N : nat,
      forall (n : nat) (G : sgraph),
        N <= n -> #|G| = n ->
        xe2_superlinear_edge_threshold eps_num eps_den n (x4_edge_count G) ->
        exists H : sgraph,
          Legacy.xe1_subgraph_of H G /\ #|H| <= C /\ ~ wagner_planar H.

Definition erdos_1019_statement : Prop :=
  forall (n : nat) (G : sgraph),
    #|G| = n ->
    x4_edge_count G = (n ^ 2) %/ 4 + (n.+1 %/ 2) ->
    exists H : sgraph, Legacy.xe1_subgraph_of H G /\ xe2_saturated_planar H.

Definition erdos_1080_statement : Prop :=
  exists cnum cden : nat,
    0 < cnum /\ 0 < cden /\
    forall (n : nat) (G : sgraph),
      #|G| = n ->
      (exists a b : nat, xe2_cube_square_floor n a /\ xe2_bipartition_sizes G a b) ->
      cden * x4_edge_count G >= cnum * n ->
      Legacy.xe1_subgraph_of (cycle_graph 6) G.

Definition erdos_22_statement : Prop :=
  forall eps_num eps_den : nat,
    0 < eps_num -> 0 < eps_den ->
    exists N : nat,
      forall n : nat, N <= n ->
        exists G : sgraph,
          #|G| = n /\
          8 * x4_edge_count G >= n ^ 2 /\
          ~ Legacy.xe1_subgraph_of 'K_4 G /\
          forall A : {set G}, xe1_stable_set A -> eps_den * #|A| <= eps_num * n.

Definition erdos_547_statement : Prop :=
  forall (n R : nat) (T : sgraph),
    2 <= n ->
    xe1_tree T -> #|T| = n ->
    XE1Legacy.diagonal_ramsey_number T R ->
    R <= 2 * n - 2.

Definition erdos_549_statement : Prop :=
  forall (k R : nat) (T : sgraph),
    xe1_tree T -> xe2_bipartition_sizes T k (2 * k) ->
    XE1Legacy.diagonal_ramsey_number T R ->
    R = 4 * k - 1.

Definition erdos_570_statement : Prop :=
  forall k : nat, 3 <= k ->
    exists M : nat,
      forall (H : sgraph) (m R : nat),
        M <= m ->
        x4_edge_count H = m -> xe1_no_isolated_vertices H ->
        XE1Legacy.graph_ramsey_number (cycle_graph k) H R ->
        R <= 2 * m + ((k - 1) %/ 2).

Definition erdos_800_statement : Prop :=
  exists C : nat,
    forall (G : sgraph) (n R : nat),
      #|G| = n ->
      (forall x y : G, x -- y -> #|N(x)| < 3 \/ #|N(y)| < 3) ->
      XE1Legacy.diagonal_ramsey_number G R ->
      R <= C * n.

Definition erdos_803_statement : Prop :=
  exists D C : nat,
    forall m : nat, 1 <= m -> exists N : nat,
      forall (n : nat) (G : sgraph),
        N <= n -> #|G| = n -> n * trunc_log 2 n <= x4_edge_count G ->
        exists H : sgraph,
          Legacy.xe1_subgraph_of H G /\ #|H| = m /\
          (exists d : nat, xe2_min_degree H d /\ Delta H <= D * d) /\
          C * x4_edge_count H >= m * trunc_log 2 m.

End XE2Legacy.

Module X59Legacy.

Definition c4_free_subgraph_polynomial_average_degree_statement : Prop :=
  exists p : seq nat,
    forall (k : nat) (G : sgraph),
      average_degree_geq G (x59_poly_eval p k) 1 ->
      exists H : sgraph,
        Legacy.x59_subgraph_of H G /\
        ~ x59_has_cycle_length H 4 /\
        average_degree_geq H k 1.

End X59Legacy.

Module X78Legacy.

Definition h_free_max_cut_three_fourths_surplus_statement : Prop :=
  forall H : sgraph,
    exists cnum cden N : nat,
      [/\ 0 < cnum, 0 < cden
        & forall (G : sgraph) (m : nat),
            N <= m ->
            x78_edge_count G = m ->
            ~ Legacy.x78_subgraph_of H G ->
            exists (A : {set G}) (s : nat),
              x78_three_fourths_surplus cnum cden m s /\
              m + 2 * s <= 2 * x78_cut_size A].

End X78Legacy.

Module X96Legacy.

Definition bollobas_erdos_large_c4_free_subgraph_statement : Prop :=
  exists cnum cden : nat,
    [/\ 0 < cnum, 0 < cden
      & forall (m : nat) (G : sgraph),
          x4_edge_count G = m ->
          exists H : sgraph,
            [/\ Legacy.x59_subgraph_of H G,
                x96_c4_free H
              & x96_m_three_fourths_lower cnum cden m (x4_edge_count H)]].

End X96Legacy.

Module X98Legacy.

Definition polynomial_kuhn_osthus_induced_subdivision_statement : Prop :=
  forall H : sgraph,
    exists p : seq nat,
      forall (s : nat) (G : sgraph),
        1 <= s ->
        ~ Legacy.x59_subgraph_of (KB s s) G ->
        average_degree_geq G (x59_poly_eval p s) 1 ->
        x98_induced_subdivision H G.

End X98Legacy.

Module X98Original.

Definition polynomial_kuhn_osthus_induced_subdivision_statement : Prop :=
  forall H : sgraph,
    exists p : seq nat,
      forall (s : nat) (G : sgraph),
        1 <= s ->
        ~ Legacy.x59_subgraph_of (KB s s) G ->
        average_degree_geq G (x59_poly_eval p s) 1 ->
        Extremal.migration.consecutive_in_path.X98Legacy.induced_subdivision H G.

End X98Original.

(** B4 history: erdos_567 before both A5 and B4, with A5's frozen Ramsey-number chain and B4's
    frozen [h5_graph] (Extremal.migration.consecutive_in_cycle, fbf33a0). *)
Module XE1Original.

Definition erdos_567_statement : Prop :=
  forall G : sgraph,
    (G = xe1_hypercube 3 \/ G = KB 3 3 \/ Extremal.migration.consecutive_in_cycle.XE1Legacy.h5_graph G) ->
    exists C : nat,
      forall (H : sgraph) (m R : nat),
        x4_edge_count H = m -> xe1_no_isolated_vertices H ->
        XE1Legacy.graph_ramsey_number G H R ->
        R <= C * m.

End XE1Original.

(** ** Certificates *)

Lemma x59_subgraph_of_compat (H G : sgraph) :
  Legacy.x59_subgraph_of H G <-> x59_subgraph_of H G.
Proof. exact: iff_sym (has_subgraphP G H). Qed.

Lemma x78_subgraph_of_compat (H G : sgraph) :
  Legacy.x78_subgraph_of H G <-> x78_subgraph_of H G.
Proof. exact: iff_sym (has_subgraphP G H). Qed.

Lemma xe1_subgraph_of_compat (H G : sgraph) :
  Legacy.xe1_subgraph_of H G <-> xe1_subgraph_of H G.
Proof. exact: iff_sym (has_subgraphP G H). Qed.

Lemma graph_ramsey_compat (H K : sgraph) (R : nat) :
  XE1Legacy.graph_ramsey H K R <-> xe1_graph_ramsey H K R.
Proof. rewrite /XE1Legacy.graph_ramsey /xe1_graph_ramsey; try setoid_rewrite xe1_subgraph_of_compat; reflexivity. Qed.

Lemma graph_ramsey_number_compat (H K : sgraph) (R : nat) :
  XE1Legacy.graph_ramsey_number H K R <-> xe1_graph_ramsey_number H K R.
Proof. rewrite /XE1Legacy.graph_ramsey_number /xe1_graph_ramsey_number; try setoid_rewrite graph_ramsey_compat; reflexivity. Qed.

Lemma diagonal_ramsey_number_compat (H : sgraph) (R : nat) :
  XE1Legacy.diagonal_ramsey_number H R <-> xe1_diagonal_ramsey_number H R.
Proof. rewrite /XE1Legacy.diagonal_ramsey_number /xe1_diagonal_ramsey_number; try setoid_rewrite graph_ramsey_number_compat; reflexivity. Qed.

Lemma c4_forcing_min_degree_compat (n f : nat) :
  XE1Legacy.c4_forcing_min_degree n f <-> xe1_c4_forcing_min_degree n f.
Proof. rewrite /XE1Legacy.c4_forcing_min_degree /xe1_c4_forcing_min_degree; try setoid_rewrite xe1_subgraph_of_compat; reflexivity. Qed.

Lemma turan_number_for_graph_compat (F : sgraph) (n m : nat) :
  XE1Legacy.turan_number_for_graph F n m <-> xe1_turan_number_for_graph F n m.
Proof. rewrite /XE1Legacy.turan_number_for_graph /xe1_turan_number_for_graph; try setoid_rewrite xe1_subgraph_of_compat; reflexivity. Qed.

Lemma min_turan_over_size_edges_compat (k l n a : nat) :
  XE1Legacy.min_turan_over_size_edges k l n a <-> xe1_min_turan_over_size_edges k l n a.
Proof. rewrite /XE1Legacy.min_turan_over_size_edges /xe1_min_turan_over_size_edges; try setoid_rewrite turan_number_for_graph_compat; reflexivity. Qed.

Lemma erdos_1035_statement_compat :
  XE1Legacy.erdos_1035_statement <-> erdos_1035_statement.
Proof. rewrite /XE1Legacy.erdos_1035_statement /erdos_1035_statement; try setoid_rewrite xe1_subgraph_of_compat; reflexivity. Qed.

Lemma erdos_545_statement_compat :
  XE1Legacy.erdos_545_statement <-> erdos_545_statement.
Proof. rewrite /XE1Legacy.erdos_545_statement /erdos_545_statement; try setoid_rewrite graph_ramsey_number_compat; reflexivity. Qed.

Lemma erdos_548_statement_compat :
  XE1Legacy.erdos_548_statement <-> erdos_548_statement.
Proof. rewrite /XE1Legacy.erdos_548_statement /erdos_548_statement; try setoid_rewrite xe1_subgraph_of_compat; reflexivity. Qed.

Lemma erdos_550_statement_compat :
  XE1Legacy.erdos_550_statement <-> erdos_550_statement.
Proof. rewrite /XE1Legacy.erdos_550_statement /erdos_550_statement; try setoid_rewrite graph_ramsey_number_compat; reflexivity. Qed.

Lemma erdos_552_statement_compat :
  XE1Legacy.erdos_552_statement <-> erdos_552_statement.
Proof. rewrite /XE1Legacy.erdos_552_statement /erdos_552_statement; try setoid_rewrite graph_ramsey_number_compat; reflexivity. Qed.

Lemma erdos_566_statement_compat :
  XE1Legacy.erdos_566_statement <-> erdos_566_statement.
Proof. rewrite /XE1Legacy.erdos_566_statement /erdos_566_statement; try setoid_rewrite graph_ramsey_number_compat; reflexivity. Qed.

Lemma erdos_567_statement_compat :
  XE1Legacy.erdos_567_statement <-> erdos_567_statement.
Proof. rewrite /XE1Legacy.erdos_567_statement /erdos_567_statement; try setoid_rewrite graph_ramsey_number_compat; reflexivity. Qed.

Lemma erdos_568_statement_compat :
  XE1Legacy.erdos_568_statement <-> erdos_568_statement.
Proof. rewrite /XE1Legacy.erdos_568_statement /erdos_568_statement; try setoid_rewrite graph_ramsey_number_compat; reflexivity. Qed.

Lemma erdos_766_statement_compat :
  XE1Legacy.erdos_766_statement <-> erdos_766_statement.
Proof. rewrite /XE1Legacy.erdos_766_statement /erdos_766_statement; try setoid_rewrite min_turan_over_size_edges_compat; reflexivity. Qed.

Lemma erdos_802_statement_compat :
  XE1Legacy.erdos_802_statement <-> erdos_802_statement.
Proof. rewrite /XE1Legacy.erdos_802_statement /erdos_802_statement; try setoid_rewrite xe1_subgraph_of_compat; reflexivity. Qed.

Lemma erdos_812_statement_compat :
  XE1Legacy.erdos_812_statement <-> erdos_812_statement.
Proof. rewrite /XE1Legacy.erdos_812_statement /erdos_812_statement; try setoid_rewrite graph_ramsey_number_compat; reflexivity. Qed.

Lemma erdos_85_statement_compat :
  XE1Legacy.erdos_85_statement <-> erdos_85_statement.
Proof. rewrite /XE1Legacy.erdos_85_statement /erdos_85_statement; try setoid_rewrite c4_forcing_min_degree_compat; reflexivity. Qed.

Lemma erdos_87_statement_compat :
  XE1Legacy.erdos_87_statement <-> erdos_87_statement.
Proof. rewrite /XE1Legacy.erdos_87_statement /erdos_87_statement; try setoid_rewrite diagonal_ramsey_number_compat; try setoid_rewrite graph_ramsey_number_compat; reflexivity. Qed.

Lemma erdos_1018_statement_compat :
  XE2Legacy.erdos_1018_statement <-> erdos_1018_statement.
Proof. rewrite /XE2Legacy.erdos_1018_statement /erdos_1018_statement; try setoid_rewrite xe1_subgraph_of_compat; reflexivity. Qed.

Lemma erdos_1019_statement_compat :
  XE2Legacy.erdos_1019_statement <-> erdos_1019_statement.
Proof. rewrite /XE2Legacy.erdos_1019_statement /erdos_1019_statement; try setoid_rewrite xe1_subgraph_of_compat; reflexivity. Qed.

Lemma erdos_1080_statement_compat :
  XE2Legacy.erdos_1080_statement <-> erdos_1080_statement.
Proof. rewrite /XE2Legacy.erdos_1080_statement /erdos_1080_statement; try setoid_rewrite xe1_subgraph_of_compat; reflexivity. Qed.

Lemma erdos_22_statement_compat :
  XE2Legacy.erdos_22_statement <-> erdos_22_statement.
Proof. rewrite /XE2Legacy.erdos_22_statement /erdos_22_statement; try setoid_rewrite xe1_subgraph_of_compat; reflexivity. Qed.

Lemma erdos_547_statement_compat :
  XE2Legacy.erdos_547_statement <-> erdos_547_statement.
Proof. rewrite /XE2Legacy.erdos_547_statement /erdos_547_statement; try setoid_rewrite diagonal_ramsey_number_compat; reflexivity. Qed.

Lemma erdos_549_statement_compat :
  XE2Legacy.erdos_549_statement <-> erdos_549_statement.
Proof. rewrite /XE2Legacy.erdos_549_statement /erdos_549_statement; try setoid_rewrite diagonal_ramsey_number_compat; reflexivity. Qed.

Lemma erdos_570_statement_compat :
  XE2Legacy.erdos_570_statement <-> erdos_570_statement.
Proof. rewrite /XE2Legacy.erdos_570_statement /erdos_570_statement; try setoid_rewrite graph_ramsey_number_compat; reflexivity. Qed.

Lemma erdos_800_statement_compat :
  XE2Legacy.erdos_800_statement <-> erdos_800_statement.
Proof. rewrite /XE2Legacy.erdos_800_statement /erdos_800_statement; try setoid_rewrite diagonal_ramsey_number_compat; reflexivity. Qed.

Lemma erdos_803_statement_compat :
  XE2Legacy.erdos_803_statement <-> erdos_803_statement.
Proof. rewrite /XE2Legacy.erdos_803_statement /erdos_803_statement; try setoid_rewrite xe1_subgraph_of_compat; reflexivity. Qed.

Lemma c4_free_subgraph_polynomial_average_degree_statement_compat :
  X59Legacy.c4_free_subgraph_polynomial_average_degree_statement <-> c4_free_subgraph_polynomial_average_degree_statement.
Proof. rewrite /X59Legacy.c4_free_subgraph_polynomial_average_degree_statement /c4_free_subgraph_polynomial_average_degree_statement; try setoid_rewrite x59_subgraph_of_compat; reflexivity. Qed.

Lemma h_free_max_cut_three_fourths_surplus_statement_compat :
  X78Legacy.h_free_max_cut_three_fourths_surplus_statement <-> h_free_max_cut_three_fourths_surplus_statement.
Proof. rewrite /X78Legacy.h_free_max_cut_three_fourths_surplus_statement /h_free_max_cut_three_fourths_surplus_statement; try setoid_rewrite x78_subgraph_of_compat; reflexivity. Qed.

Lemma bollobas_erdos_large_c4_free_subgraph_statement_compat :
  X96Legacy.bollobas_erdos_large_c4_free_subgraph_statement <-> bollobas_erdos_large_c4_free_subgraph_statement.
Proof. rewrite /X96Legacy.bollobas_erdos_large_c4_free_subgraph_statement /bollobas_erdos_large_c4_free_subgraph_statement; try setoid_rewrite x59_subgraph_of_compat; reflexivity. Qed.

Lemma polynomial_kuhn_osthus_induced_subdivision_statement_compat :
  X98Legacy.polynomial_kuhn_osthus_induced_subdivision_statement <-> polynomial_kuhn_osthus_induced_subdivision_statement.
Proof. rewrite /X98Legacy.polynomial_kuhn_osthus_induced_subdivision_statement /polynomial_kuhn_osthus_induced_subdivision_statement; try setoid_rewrite x59_subgraph_of_compat; reflexivity. Qed.

Lemma polynomial_kuhn_osthus_induced_subdivision_statement_original_compat :
  X98Original.polynomial_kuhn_osthus_induced_subdivision_statement <-> polynomial_kuhn_osthus_induced_subdivision_statement.
Proof.
rewrite /X98Original.polynomial_kuhn_osthus_induced_subdivision_statement /polynomial_kuhn_osthus_induced_subdivision_statement; setoid_rewrite x59_subgraph_of_compat;
  setoid_rewrite Extremal.migration.consecutive_in_path.x98_induced_subdivision_compat; reflexivity.
Qed.

Lemma erdos_567_statement_original_compat :
  XE1Original.erdos_567_statement <-> erdos_567_statement.
Proof.
rewrite /XE1Original.erdos_567_statement /erdos_567_statement; setoid_rewrite graph_ramsey_number_compat;
  setoid_rewrite Extremal.migration.consecutive_in_cycle.xe1_h5_graph_compat; reflexivity.
Qed.

Print Assumptions x59_subgraph_of_compat.
Print Assumptions x78_subgraph_of_compat.
Print Assumptions xe1_subgraph_of_compat.
Print Assumptions graph_ramsey_compat.
Print Assumptions graph_ramsey_number_compat.
Print Assumptions diagonal_ramsey_number_compat.
Print Assumptions c4_forcing_min_degree_compat.
Print Assumptions turan_number_for_graph_compat.
Print Assumptions min_turan_over_size_edges_compat.
Print Assumptions erdos_1035_statement_compat.
Print Assumptions erdos_545_statement_compat.
Print Assumptions erdos_548_statement_compat.
Print Assumptions erdos_550_statement_compat.
Print Assumptions erdos_552_statement_compat.
Print Assumptions erdos_566_statement_compat.
Print Assumptions erdos_567_statement_compat.
Print Assumptions erdos_568_statement_compat.
Print Assumptions erdos_766_statement_compat.
Print Assumptions erdos_802_statement_compat.
Print Assumptions erdos_812_statement_compat.
Print Assumptions erdos_85_statement_compat.
Print Assumptions erdos_87_statement_compat.
Print Assumptions erdos_1018_statement_compat.
Print Assumptions erdos_1019_statement_compat.
Print Assumptions erdos_1080_statement_compat.
Print Assumptions erdos_22_statement_compat.
Print Assumptions erdos_547_statement_compat.
Print Assumptions erdos_549_statement_compat.
Print Assumptions erdos_570_statement_compat.
Print Assumptions erdos_800_statement_compat.
Print Assumptions erdos_803_statement_compat.
Print Assumptions c4_free_subgraph_polynomial_average_degree_statement_compat.
Print Assumptions h_free_max_cut_three_fourths_surplus_statement_compat.
Print Assumptions bollobas_erdos_large_c4_free_subgraph_statement_compat.
Print Assumptions polynomial_kuhn_osthus_induced_subdivision_statement_compat.
Print Assumptions polynomial_kuhn_osthus_induced_subdivision_statement_original_compat.
Print Assumptions erdos_567_statement_original_compat.
