(** A7 edge counts: frozen extremal helpers, intermediate chains and corpus rows, then complete
    Originals composing the earlier families' frozen copies. Baseline, hashes and exact
    substitutions are recorded in meta/migration_reports/edge_count.spec.json.
    - [Legacy], [D2ramLegacy], [D2turLegacy]: the seven extremal helper bodies at the baseline
      ([x76]/[x78] count M1's alias edge sets: post-M1 bodies).
    - [XnnLegacy]: every affected chain and row at the baseline, over this family's frozen helpers;
      other families' helpers stay live there.
    - [XnnOriginal]: complete rows. X76/X78 are pre-M1 (count bodies at 061154c over M1's frozen
      comprehension); the others are the 9e03072 texts, which reach no M1 helper. *)
From Corelib Require Import Setoid Morphisms.
From GTBase Require Import base.
From Extremal.conjectures Require Import D2ram D2tur X4 X59 X76 X78 X88 X96 XE1 XE2.
From Extremal.migration Require simple_edges delete_edges internal_vertices subgraph_of complement
  consecutive_in_cycle bipartition.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Earlier families' certificate modules, aliased without Import: their [Legacy], [XnnLegacy] and
    [XnnOriginal] module names coincide with this file's. *)
Module M1 := Extremal.migration.simple_edges.
Module A2 := Extremal.migration.delete_edges.
Module B2 := Extremal.migration.internal_vertices.
Module A5 := Extremal.migration.subgraph_of.
Module A6 := Extremal.migration.complement.
Module B4 := Extremal.migration.consecutive_in_cycle.
Module C7 := Extremal.migration.bipartition.

#[local] Instance and3_iff_morphism : Proper (iff ==> iff ==> iff ==> iff) and3.
Proof. by move=> a a' ha b b' hb c c' hc; split=> -[x y z]; split; by [apply/ha|apply/hb|apply/hc]. Qed.

#[local] Instance and4_iff_morphism : Proper (iff ==> iff ==> iff ==> iff ==> iff) and4.
Proof.
by move=> a a' ha b b' hb c c' hc d d' hd; split=> -[x y z w]; split;
  by [apply/ha|apply/hb|apply/hc|apply/hd].
Qed.

Module Legacy.

Definition x4_edge_count (G : sgraph) : nat :=
  #|[set p : G * G |
      (p.1 -- p.2) && ((enum_rank p.1) < (enum_rank p.2))%N]|.

Definition x76_edge_count (G : sgraph) : nat := #|x76_edge_set G|.

Definition x78_edge_count (G : sgraph) : nat := #|x78_edge_set G|.

End Legacy.

Module D2ramLegacy.

Definition edge_count (G : sgraph) : nat := #|E(G)|.

Definition common_graph (H : sgraph) : Prop :=
  exists N : nat, forall (n : nat) (col : rel 'I_n), symmetric col -> (N <= n)%N ->
    (n ^ #|H| <= mono_copies H col * 2 ^ D2ramLegacy.edge_count H)%N.

Definition chromatic_number_of_common_graphs_statement : Prop :=
  exists k : nat,
    forall H : sgraph, (0 < #|H|)%N -> D2ramLegacy.common_graph H -> (χ([set: H]) <= k)%N.

End D2ramLegacy.

Module D2turLegacy.

Definition edge_count (G : sgraph) : nat := #|[set p : G * G | oedge p]|.

Definition is_turan_number (n : nat) (k : nat) (Fam : 'I_k -> sgraph) (m : nat) : Prop :=
  (exists G : sgraph, [/\ #|G| = n, D2turLegacy.edge_count G = m & family_free G Fam]) /\
  (forall m' : nat,
     (exists G : sgraph, [/\ #|G| = n, D2turLegacy.edge_count G = m' & family_free G Fam]) ->
     (m' <= m)%N).

Definition turan_number_of_a_finite_family_statement : Prop :=
  forall (k : nat) (Fam : 'I_k -> sgraph), (0 < k)%N ->
    exists (i : 'I_k) (C N : nat),
      forall (n mFam mF0 : nat), (N <= n)%N ->
        D2turLegacy.is_turan_number n Fam mFam ->
        D2turLegacy.is_turan_number n (fun _ : 'I_1 => Fam i) mF0 ->
        (mF0 <= C * mFam)%N.

Definition sidorenkos_statement : Prop :=
  forall H G : sgraph, bipartite H -> (0 < #|G|)%N ->
    ((oedges G) ^ (D2turLegacy.edge_count H) * (#|G|) ^ (#|H|)
       <= hom_count H G * (#|G|) ^ (2 * D2turLegacy.edge_count H))%N.

End D2turLegacy.

Module X4Legacy.

Definition turan_number (r n m : nat) : Prop :=
  (exists G : sgraph,
     [/\ #|G| = n, Legacy.x4_edge_count G = m & x4_K_free G (r.+1)]) /\
  forall m' : nat,
    (exists G : sgraph,
       [/\ #|G| = n, Legacy.x4_edge_count G = m' & x4_K_free G (r.+1)]) ->
    m' <= m.

Definition turan_degree_sum_clique_statement : Prop :=
  forall r n tr : nat, 2 <= r -> r <= n ->
    turan_number r n tr ->
    forall G : sgraph, #|G| = n -> tr <= Legacy.x4_edge_count G ->
      exists S : {set G},
        #|S| = r /\ clique S /\
        2 * r * Legacy.x4_edge_count G <= n * x4_degree_sum S.

Definition book_triangle_edge_statement : Prop :=
  forall G : sgraph, forall n : nat,
    #|G| = n -> n * n < 4 * Legacy.x4_edge_count G ->
    exists x y : G, x -- y /\ n <= 6 * #|N(x) :&: N(y)|.

Definition c5_edge_count_above_turan_statement : Prop :=
  forall G : sgraph, forall n : nat,
    #|G| = n -> n * n < 4 * Legacy.x4_edge_count G ->
    2 * n * n <= 9 * x4_c5_edge_count G.

Definition triangle_supersaturation_statement : Prop :=
  forall G : sgraph, forall n t : nat,
    #|G| = n -> t < n %/ 2 ->
    Legacy.x4_edge_count G = n * n %/ 4 + t ->
    t * (n %/ 2) <= x4_triangle_count G.

End X4Legacy.

Module X76Legacy.

Definition ck_free_max_cut_polynomial_surplus_statement : Prop :=
  forall k : nat,
    3 <= k ->
    exists cnum cden N : nat,
      [/\ 0 < cnum, 0 < cden
        & forall (G : sgraph) (m : nat),
            N <= m ->
            Legacy.x76_edge_count G = m ->
            ~ x76_has_cycle_length G k ->
            exists (A : {set G}) (s : nat),
              x76_power_surplus k cnum cden m s /\
              m + 2 * s <= 2 * x76_cut_size A].

End X76Legacy.

Module X78Legacy.

Definition h_free_max_cut_three_fourths_surplus_statement : Prop :=
  forall H : sgraph,
    exists cnum cden N : nat,
      [/\ 0 < cnum, 0 < cden
        & forall (G : sgraph) (m : nat),
            N <= m ->
            Legacy.x78_edge_count G = m ->
            ~ x78_subgraph_of H G ->
            exists (A : {set G}) (s : nat),
              x78_three_fourths_surplus cnum cden m s /\
              m + 2 * s <= 2 * x78_cut_size A].

End X78Legacy.

Module X88Legacy.

Definition pentagonal_turan_stability_dominates_clique_count_statement : Prop :=
  forall r : nat,
    2 <= r ->
    exists delta_num delta_den : nat,
      [/\ 0 < delta_num, 0 < delta_den
        & forall (n tr : nat) (G : sgraph),
            X4Legacy.turan_number r n tr ->
            x4_K_free G r.+1 ->
            #|G| = n ->
            delta_den * tr <= delta_den * Legacy.x4_edge_count G + delta_num * n ^ 2 ->
            exists Gstar : sgraph,
              [/\ x88_pentagonal_turan_graph Gstar r n,
                  Legacy.x4_edge_count G <= Legacy.x4_edge_count Gstar
                & x88_edit_to_r_partite G r <= x88_edit_to_r_partite Gstar r]].

End X88Legacy.

Module X96Legacy.

Definition bollobas_erdos_large_c4_free_subgraph_statement : Prop :=
  exists cnum cden : nat,
    [/\ 0 < cnum, 0 < cden
      & forall (m : nat) (G : sgraph),
          Legacy.x4_edge_count G = m ->
          exists H : sgraph,
            [/\ x59_subgraph_of H G,
                x96_c4_free H
              & x96_m_three_fourths_lower cnum cden m (Legacy.x4_edge_count H)]].

End X96Legacy.

Module XE1Legacy.

Definition size_ramsey (H K : sgraph) (m : nat) : Prop :=
  exists G : sgraph,
    Legacy.x4_edge_count G = m /\
    forall col : rel G, symmetric col ->
      (exists f : H -> G, injective f /\ forall x y : H, x -- y -> f x -- f y /\ col (f x) (f y)) \/
      (exists f : K -> G, injective f /\ forall x y : K, x -- y -> f x -- f y /\ ~~ col (f x) (f y)).

Definition size_ramsey_number (H K : sgraph) (m : nat) : Prop :=
  size_ramsey H K m /\
  forall m' : nat, size_ramsey H K m' -> m <= m'.

Definition every_k_set_sparse (G : sgraph) (k : nat) : Prop :=
  forall S : {set G}, #|S| = k -> Legacy.x4_edge_count (induced S) <= 2 * k - 3.

Definition turan_number_for_graph (F : sgraph) (n m : nat) : Prop :=
  (exists G : sgraph, #|G| = n /\ Legacy.x4_edge_count G = m /\ ~ xe1_subgraph_of F G) /\
  forall m' : nat,
    (exists G : sgraph, #|G| = n /\ Legacy.x4_edge_count G = m' /\ ~ xe1_subgraph_of F G) ->
    m' <= m.

Definition min_turan_over_size_edges (k l n a : nat) : Prop :=
  (exists F : sgraph,
      #|F| = k /\ Legacy.x4_edge_count F = l /\ turan_number_for_graph F n a) /\
  forall b : nat,
    (exists F : sgraph,
      #|F| = k /\ Legacy.x4_edge_count F = l /\ turan_number_for_graph F n b) ->
    a <= b.

Definition erdos_128_statement : Prop :=
  forall (n : nat) (G : sgraph),
    #|G| = n ->
    (forall S : {set G}, n %/ 2 <= #|S| -> n ^ 2 < 50 * Legacy.x4_edge_count (induced S)) ->
    exists T : {set G}, x4_triangle_set T.

Definition erdos_545_statement : Prop :=
  forall (m n t RG RH : nat) (G H : sgraph),
    Legacy.x4_edge_count G = m -> xe1_no_isolated_vertices G ->
    m = 'C(n, 2) + t -> t < n ->
    xe1_complete_plus_vertex H n t ->
    xe1_graph_ramsey_number G G RG ->
    xe1_graph_ramsey_number H H RH ->
    RG <= RH.

Definition erdos_548_statement : Prop :=
  forall (n k : nat) (G T : sgraph),
    k.+1 <= n ->
    #|G| = n -> #|T| = k.+1 -> xe1_tree T ->
    2 * Legacy.x4_edge_count G >= (k - 1) * n + 2 ->
    xe1_subgraph_of T G.

Definition erdos_561_statement : Prop :=
  forall (ns ms : seq nat) (F1 F2 : sgraph) (m formula : nat),
    0 < size ns -> 0 < size ms ->
    xe1_positive_sequence ns -> xe1_positive_sequence ms ->
    xe1_nonincreasing_sequence ns -> xe1_nonincreasing_sequence ms ->
    xe1_star_forest_with_leaves F1 ns ->
    xe1_star_forest_with_leaves F2 ms ->
    xe1_star_forest_formula ns ms formula ->
    size_ramsey_number F1 F2 m ->
    m = formula.

Definition erdos_566_statement : Prop :=
  forall G : sgraph,
    (forall k : nat, every_k_set_sparse G k) ->
    exists C : nat,
      forall (H : sgraph) (m R : nat),
        Legacy.x4_edge_count H = m -> xe1_no_isolated_vertices H ->
        xe1_graph_ramsey_number G H R ->
        R <= C * m.

Definition erdos_567_statement : Prop :=
  forall G : sgraph,
    (G = xe1_hypercube 3 \/ G = KB 3 3 \/ xe1_h5_graph G) ->
    exists C : nat,
      forall (H : sgraph) (m R : nat),
        Legacy.x4_edge_count H = m -> xe1_no_isolated_vertices H ->
        xe1_graph_ramsey_number G H R ->
        R <= C * m.

Definition erdos_568_statement : Prop :=
  forall G : sgraph,
    (exists C1 : nat, forall (n R : nat) (T : sgraph),
      xe1_tree T -> #|T| = n -> xe1_graph_ramsey_number G T R -> R <= C1 * n) ->
    (exists C2 : nat, forall (n R : nat),
      xe1_graph_ramsey_number G 'K_n R -> R <= C2 * n ^ 2) ->
    exists C : nat, forall (H : sgraph) (m R : nat),
      Legacy.x4_edge_count H = m -> xe1_no_isolated_vertices H ->
      xe1_graph_ramsey_number G H R ->
      R <= C * m.

Definition erdos_766_statement : Prop :=
  forall k l : nat, k < l -> 4 * l.+1 <= k ^ 2 ->
    exists N : nat,
      forall n a b : nat,
        N <= n ->
        min_turan_over_size_edges k l n a ->
        min_turan_over_size_edges k l.+1 n b ->
        a < b.

End XE1Legacy.

Module XE2Legacy.

Definition saturated_planar (G : sgraph) : Prop :=
  3 < #|G| /\ wagner_planar G /\ Legacy.x4_edge_count G = 3 * #|G| - 6.

Definition incident_chord_extremal (k n m : nat) : Prop :=
  (exists G : sgraph,
      #|G| = n /\ Legacy.x4_edge_count G = m /\
      xe2_no_cycle_with_incident_chords G k) /\
  forall m' : nat,
    (exists G : sgraph,
      #|G| = n /\ Legacy.x4_edge_count G = m' /\
      xe2_no_cycle_with_incident_chords G k) ->
    m' <= m.

Definition erdos_1009_statement : Prop :=
  forall cnum cden : nat, 0 < cnum -> 0 < cden -> exists f : nat,
    forall (n k : nat) (G : sgraph),
      #|G| = n ->
      Legacy.x4_edge_count G >= (n ^ 2) %/ 4 + k ->
      cden * k < cnum * n ->
      exists ts : seq {set G},
        xe2_edge_disjoint_triangles ts /\ k <= size ts + f.

Definition erdos_1018_statement : Prop :=
  forall eps_num eps_den : nat,
    0 < eps_num -> 0 < eps_den ->
    exists C N : nat,
      forall (n : nat) (G : sgraph),
        N <= n -> #|G| = n ->
        xe2_superlinear_edge_threshold eps_num eps_den n (Legacy.x4_edge_count G) ->
        exists H : sgraph,
          xe1_subgraph_of H G /\ #|H| <= C /\ ~ wagner_planar H.

Definition erdos_1019_statement : Prop :=
  forall (n : nat) (G : sgraph),
    #|G| = n ->
    Legacy.x4_edge_count G = (n ^ 2) %/ 4 + (n.+1 %/ 2) ->
    exists H : sgraph, xe1_subgraph_of H G /\ saturated_planar H.

Definition erdos_1080_statement : Prop :=
  exists cnum cden : nat,
    0 < cnum /\ 0 < cden /\
    forall (n : nat) (G : sgraph),
      #|G| = n ->
      (exists a b : nat, xe2_cube_square_floor n a /\ xe2_bipartition_sizes G a b) ->
      cden * Legacy.x4_edge_count G >= cnum * n ->
      xe1_subgraph_of (cycle_graph 6) G.

Definition erdos_22_statement : Prop :=
  forall eps_num eps_den : nat,
    0 < eps_num -> 0 < eps_den ->
    exists N : nat,
      forall n : nat, N <= n ->
        exists G : sgraph,
          #|G| = n /\
          8 * Legacy.x4_edge_count G >= n ^ 2 /\
          ~ xe1_subgraph_of 'K_4 G /\
          forall A : {set G}, xe1_stable_set A -> eps_den * #|A| <= eps_num * n.

Definition erdos_559_statement : Prop :=
  forall d : nat, exists C : nat,
    forall (G : sgraph) (n m : nat),
      #|G| = n -> Delta G <= d ->
      XE1Legacy.size_ramsey_number G G m ->
      m <= C * n.

Definition erdos_570_statement : Prop :=
  forall k : nat, 3 <= k ->
    exists M : nat,
      forall (H : sgraph) (m R : nat),
        M <= m ->
        Legacy.x4_edge_count H = m -> xe1_no_isolated_vertices H ->
        xe1_graph_ramsey_number (cycle_graph k) H R ->
        R <= 2 * m + ((k - 1) %/ 2).

Definition erdos_613_statement : Prop :=
  forall (n : nat) (G : sgraph),
    3 <= n ->
    Legacy.x4_edge_count G = 'C(2 * n + 1, 2) - 'C(n, 2) - 1 ->
    xe2_bipartite_plus_bounded_degree G n.

Definition erdos_742_statement : Prop :=
  forall (n : nat) (G : sgraph),
    #|G| = n ->
    xe2_diameter_critical_two G ->
    4 * Legacy.x4_edge_count G <= n ^ 2.

Definition erdos_767_statement : Prop :=
  forall k : nat, exists N : nat,
    forall (n m : nat),
      N <= n ->
      incident_chord_extremal k n m ->
      m = (k + 1) * n - (k + 1) ^ 2.

Definition erdos_801_statement : Prop :=
  exists C N : nat,
    0 < C /\
    forall (G : sgraph) (n s : nat),
      N <= n ->
      #|G| = n ->
      xe1_sqrt_floor n s ->
      (forall A : {set G}, xe1_stable_set A -> #|A| <= s) ->
      exists S : {set G},
        #|S| <= s /\ C * Legacy.x4_edge_count (induced S) >= s * trunc_log 2 n.

Definition erdos_803_statement : Prop :=
  exists D C : nat,
    forall m : nat, 1 <= m -> exists N : nat,
      forall (n : nat) (G : sgraph),
        N <= n -> #|G| = n -> n * trunc_log 2 n <= Legacy.x4_edge_count G ->
        exists H : sgraph,
          xe1_subgraph_of H G /\ #|H| = m /\
          (exists d : nat, xe2_min_degree H d /\ Delta H <= D * d) /\
          C * Legacy.x4_edge_count H >= m * trunc_log 2 m.

Definition erdos_814_statement : Prop :=
  forall k : nat, 2 <= k ->
    exists c d : nat,
      0 < c /\ c < d /\
      forall (n : nat) (G : sgraph),
        k - 1 <= n ->
        #|G| = n ->
        Legacy.x4_edge_count G =
          (k - 1) * (n - k + 2) + 'C(k - 2, 2) + 1 ->
        exists S : {set G},
          0 < #|S| /\
          d * #|S| <= (d - c) * n /\
          forall v : induced S, k <= #|N(v)|.

Definition erdos_816_statement : Prop :=
  forall (n : nat) (G : sgraph),
    #|G| = 2 * n + 1 ->
    Legacy.x4_edge_count G = n ^ 2 + n + 1 ->
    exists x y : G,
      x != y /\ #|N(x)| = #|N(y)| /\ @xe2_path_length3 G x y.

Definition erdos_915_statement : Prop :=
  forall (n m : nat) (G : sgraph),
    #|G| = 1 + n * (m - 1) ->
    Legacy.x4_edge_count G = 1 + n * 'C(m, 2) ->
    exists x y : G, exists P : 'I_m -> seq G,
      x != y /\
      (forall i : 'I_m,
        if P i is z :: p then z = x /\ last z p = y /\ path (--) z p else False) /\
      xe2_paths_internally_disjoint x y P /\
      xe2_paths_edge_disjoint P.

End XE2Legacy.

Module X76Original.

Definition x76_edge_count (G : sgraph) : nat := #|M1.Legacy.edge_set G|.

Definition ck_free_max_cut_polynomial_surplus_statement : Prop :=
  forall k : nat,
    3 <= k ->
    exists cnum cden N : nat,
      [/\ 0 < cnum, 0 < cden
        & forall (G : sgraph) (m : nat),
            N <= m ->
            X76Original.x76_edge_count G = m ->
            ~ x76_has_cycle_length G k ->
            exists (A : {set G}) (s : nat),
              x76_power_surplus k cnum cden m s /\
              m + 2 * s <= 2 * x76_cut_size A].

End X76Original.

Module X78Original.

Definition x78_edge_count (G : sgraph) : nat := #|M1.Legacy.edge_set G|.

Definition h_free_max_cut_three_fourths_surplus_statement : Prop :=
  forall H : sgraph,
    exists cnum cden N : nat,
      [/\ 0 < cnum, 0 < cden
        & forall (G : sgraph) (m : nat),
            N <= m ->
            X78Original.x78_edge_count G = m ->
            ~ A5.Legacy.x78_subgraph_of H G ->
            exists (A : {set G}) (s : nat),
              x78_three_fourths_surplus cnum cden m s /\
              m + 2 * s <= 2 * x78_cut_size A].

End X78Original.

Module X4Original.

Definition c5_edge_count_above_turan_statement : Prop :=
  forall G : sgraph, forall n : nat,
    #|G| = n -> n * n < 4 * Legacy.x4_edge_count G ->
    2 * n * n <= 9 * B4.X4Legacy.c5_edge_count G.

End X4Original.

Module X96Original.

Definition bollobas_erdos_large_c4_free_subgraph_statement : Prop :=
  exists cnum cden : nat,
    [/\ 0 < cnum, 0 < cden
      & forall (m : nat) (G : sgraph),
          Legacy.x4_edge_count G = m ->
          exists H : sgraph,
            [/\ A5.Legacy.x59_subgraph_of H G,
                x96_c4_free H
              & x96_m_three_fourths_lower cnum cden m (Legacy.x4_edge_count H)]].

End X96Original.

Module XE1Original.

Definition turan_number_for_graph (F : sgraph) (n m : nat) : Prop :=
  (exists G : sgraph, #|G| = n /\ Legacy.x4_edge_count G = m /\ ~ A5.Legacy.xe1_subgraph_of F G) /\
  forall m' : nat,
    (exists G : sgraph, #|G| = n /\ Legacy.x4_edge_count G = m' /\ ~ A5.Legacy.xe1_subgraph_of F G) ->
    m' <= m.

Definition min_turan_over_size_edges (k l n a : nat) : Prop :=
  (exists F : sgraph,
      #|F| = k /\ Legacy.x4_edge_count F = l /\ XE1Original.turan_number_for_graph F n a) /\
  forall b : nat,
    (exists F : sgraph,
      #|F| = k /\ Legacy.x4_edge_count F = l /\ XE1Original.turan_number_for_graph F n b) ->
    a <= b.

Definition erdos_545_statement : Prop :=
  forall (m n t RG RH : nat) (G H : sgraph),
    Legacy.x4_edge_count G = m -> xe1_no_isolated_vertices G ->
    m = 'C(n, 2) + t -> t < n ->
    xe1_complete_plus_vertex H n t ->
    A6.XE1Original.graph_ramsey_number G G RG ->
    A6.XE1Original.graph_ramsey_number H H RH ->
    RG <= RH.

Definition erdos_548_statement : Prop :=
  forall (n k : nat) (G T : sgraph),
    k.+1 <= n ->
    #|G| = n -> #|T| = k.+1 -> xe1_tree T ->
    2 * Legacy.x4_edge_count G >= (k - 1) * n + 2 ->
    A5.Legacy.xe1_subgraph_of T G.

Definition erdos_566_statement : Prop :=
  forall G : sgraph,
    (forall k : nat, XE1Legacy.every_k_set_sparse G k) ->
    exists C : nat,
      forall (H : sgraph) (m R : nat),
        Legacy.x4_edge_count H = m -> xe1_no_isolated_vertices H ->
        A6.XE1Original.graph_ramsey_number G H R ->
        R <= C * m.

Definition erdos_567_statement : Prop :=
  forall G : sgraph,
    (G = xe1_hypercube 3 \/ G = KB 3 3 \/ B4.XE1Legacy.h5_graph G) ->
    exists C : nat,
      forall (H : sgraph) (m R : nat),
        Legacy.x4_edge_count H = m -> xe1_no_isolated_vertices H ->
        A6.XE1Original.graph_ramsey_number G H R ->
        R <= C * m.

Definition erdos_568_statement : Prop :=
  forall G : sgraph,
    (exists C1 : nat, forall (n R : nat) (T : sgraph),
      xe1_tree T -> #|T| = n -> A6.XE1Original.graph_ramsey_number G T R -> R <= C1 * n) ->
    (exists C2 : nat, forall (n R : nat),
      A6.XE1Original.graph_ramsey_number G 'K_n R -> R <= C2 * n ^ 2) ->
    exists C : nat, forall (H : sgraph) (m R : nat),
      Legacy.x4_edge_count H = m -> xe1_no_isolated_vertices H ->
      A6.XE1Original.graph_ramsey_number G H R ->
      R <= C * m.

Definition erdos_766_statement : Prop :=
  forall k l : nat, k < l -> 4 * l.+1 <= k ^ 2 ->
    exists N : nat,
      forall n a b : nat,
        N <= n ->
        XE1Original.min_turan_over_size_edges k l n a ->
        XE1Original.min_turan_over_size_edges k l.+1 n b ->
        a < b.

End XE1Original.

Module XE2Original.

Definition incident_chord_extremal (k n m : nat) : Prop :=
  (exists G : sgraph,
      #|G| = n /\ Legacy.x4_edge_count G = m /\
      B4.XE2Legacy.no_cycle_with_incident_chords G k) /\
  forall m' : nat,
    (exists G : sgraph,
      #|G| = n /\ Legacy.x4_edge_count G = m' /\
      B4.XE2Legacy.no_cycle_with_incident_chords G k) ->
    m' <= m.

Definition erdos_570_statement : Prop :=
  forall k : nat, 3 <= k ->
    exists M : nat,
      forall (H : sgraph) (m R : nat),
        M <= m ->
        Legacy.x4_edge_count H = m -> xe1_no_isolated_vertices H ->
        A6.XE1Original.graph_ramsey_number (cycle_graph k) H R ->
        R <= 2 * m + ((k - 1) %/ 2).

Definition erdos_1018_statement : Prop :=
  forall eps_num eps_den : nat,
    0 < eps_num -> 0 < eps_den ->
    exists C N : nat,
      forall (n : nat) (G : sgraph),
        N <= n -> #|G| = n ->
        xe2_superlinear_edge_threshold eps_num eps_den n (Legacy.x4_edge_count G) ->
        exists H : sgraph,
          A5.Legacy.xe1_subgraph_of H G /\ #|H| <= C /\ ~ wagner_planar H.

Definition erdos_1019_statement : Prop :=
  forall (n : nat) (G : sgraph),
    #|G| = n ->
    Legacy.x4_edge_count G = (n ^ 2) %/ 4 + (n.+1 %/ 2) ->
    exists H : sgraph, A5.Legacy.xe1_subgraph_of H G /\ XE2Legacy.saturated_planar H.

Definition erdos_1080_statement : Prop :=
  exists cnum cden : nat,
    0 < cnum /\ 0 < cden /\
    forall (n : nat) (G : sgraph),
      #|G| = n ->
      (exists a b : nat, xe2_cube_square_floor n a /\ C7.XE2Legacy.xe2_bipartition_sizes G a b) ->
      cden * Legacy.x4_edge_count G >= cnum * n ->
      A5.Legacy.xe1_subgraph_of (cycle_graph 6) G.

Definition erdos_22_statement : Prop :=
  forall eps_num eps_den : nat,
    0 < eps_num -> 0 < eps_den ->
    exists N : nat,
      forall n : nat, N <= n ->
        exists G : sgraph,
          #|G| = n /\
          8 * Legacy.x4_edge_count G >= n ^ 2 /\
          ~ A5.Legacy.xe1_subgraph_of 'K_4 G /\
          forall A : {set G}, xe1_stable_set A -> eps_den * #|A| <= eps_num * n.

Definition erdos_803_statement : Prop :=
  exists D C : nat,
    forall m : nat, 1 <= m -> exists N : nat,
      forall (n : nat) (G : sgraph),
        N <= n -> #|G| = n -> n * trunc_log 2 n <= Legacy.x4_edge_count G ->
        exists H : sgraph,
          A5.Legacy.xe1_subgraph_of H G /\ #|H| = m /\
          (exists d : nat, xe2_min_degree H d /\ Delta H <= D * d) /\
          C * Legacy.x4_edge_count H >= m * trunc_log 2 m.

Definition erdos_613_statement : Prop :=
  forall (n : nat) (G : sgraph),
    3 <= n ->
    Legacy.x4_edge_count G = 'C(2 * n + 1, 2) - 'C(n, 2) - 1 ->
    A2.XE2Legacy.bipartite_plus_bounded_degree G n.

Definition erdos_742_statement : Prop :=
  forall (n : nat) (G : sgraph),
    #|G| = n ->
    A2.XE2Legacy.diameter_critical_two G ->
    4 * Legacy.x4_edge_count G <= n ^ 2.

Definition erdos_915_statement : Prop :=
  forall (n m : nat) (G : sgraph),
    #|G| = 1 + n * (m - 1) ->
    Legacy.x4_edge_count G = 1 + n * 'C(m, 2) ->
    exists x y : G, exists P : 'I_m -> seq G,
      x != y /\
      (forall i : 'I_m,
        if P i is z :: p then z = x /\ last z p = y /\ path (--) z p else False) /\
      B2.XE2Legacy.paths_internally_disjoint x y P /\
      xe2_paths_edge_disjoint P.

Definition erdos_767_statement : Prop :=
  forall k : nat, exists N : nat,
    forall (n m : nat),
      N <= n ->
      XE2Original.incident_chord_extremal k n m ->
      m = (k + 1) * n - (k + 1) ^ 2.

End XE2Original.

Lemma x4_edge_count_compat (G : sgraph) : Legacy.x4_edge_count G = x4_edge_count G.
Proof. exact: GTBase.common.edge_count_rank G. Qed.

Lemma x76_edge_count_compat (G : sgraph) : Legacy.x76_edge_count G = x76_edge_count G.
Proof. by []. Qed.

Lemma x78_edge_count_compat (G : sgraph) : Legacy.x78_edge_count G = x78_edge_count G.
Proof. by []. Qed.

Lemma d2ram_edge_count_compat (G : sgraph) : D2ramLegacy.edge_count G = Extremal.conjectures.D2ram.edge_count G.
Proof. by []. Qed.

Lemma d2ram_common_graph_compat (H : sgraph) :
  @D2ramLegacy.common_graph H <-> @Extremal.conjectures.D2ram.common_graph H.
Proof. rewrite /D2ramLegacy.common_graph /Extremal.conjectures.D2ram.common_graph; try setoid_rewrite d2ram_edge_count_compat; reflexivity. Qed.

Lemma chromatic_number_of_common_graphs_statement_compat :
  D2ramLegacy.chromatic_number_of_common_graphs_statement <-> Extremal.conjectures.D2ram.chromatic_number_of_common_graphs_statement.
Proof. rewrite /D2ramLegacy.chromatic_number_of_common_graphs_statement /Extremal.conjectures.D2ram.chromatic_number_of_common_graphs_statement; try setoid_rewrite d2ram_common_graph_compat; try setoid_rewrite d2ram_edge_count_compat; reflexivity. Qed.

Lemma d2tur_edge_count_compat (G : sgraph) : D2turLegacy.edge_count G = Extremal.conjectures.D2tur.edge_count G.
Proof. exact: GTBase.common.edge_count_rank G. Qed.

Lemma d2tur_is_turan_number_compat (n : nat) (k : nat) (Fam : 'I_k -> sgraph) (m : nat) :
  @D2turLegacy.is_turan_number n k Fam m <-> @Extremal.conjectures.D2tur.is_turan_number n k Fam m.
Proof. rewrite /D2turLegacy.is_turan_number /Extremal.conjectures.D2tur.is_turan_number; try setoid_rewrite d2tur_edge_count_compat; reflexivity. Qed.

Lemma turan_number_of_a_finite_family_statement_compat :
  D2turLegacy.turan_number_of_a_finite_family_statement <-> Extremal.conjectures.D2tur.turan_number_of_a_finite_family_statement.
Proof. rewrite /D2turLegacy.turan_number_of_a_finite_family_statement /Extremal.conjectures.D2tur.turan_number_of_a_finite_family_statement; try setoid_rewrite d2tur_is_turan_number_compat; try setoid_rewrite d2tur_edge_count_compat; reflexivity. Qed.

Lemma sidorenkos_statement_compat :
  D2turLegacy.sidorenkos_statement <-> Extremal.conjectures.D2tur.sidorenkos_statement.
Proof. rewrite /D2turLegacy.sidorenkos_statement /Extremal.conjectures.D2tur.sidorenkos_statement; try setoid_rewrite d2tur_is_turan_number_compat; try setoid_rewrite d2tur_edge_count_compat; reflexivity. Qed.

Lemma turan_number_compat (r n m : nat) :
  @X4Legacy.turan_number r n m <-> @x4_turan_number r n m.
Proof. rewrite /X4Legacy.turan_number /x4_turan_number; try setoid_rewrite x4_edge_count_compat; reflexivity. Qed.

Lemma turan_degree_sum_clique_statement_compat :
  X4Legacy.turan_degree_sum_clique_statement <-> turan_degree_sum_clique_statement.
Proof. rewrite /X4Legacy.turan_degree_sum_clique_statement /turan_degree_sum_clique_statement; try setoid_rewrite x4_edge_count_compat; try setoid_rewrite turan_number_compat; reflexivity. Qed.

Lemma book_triangle_edge_statement_compat :
  X4Legacy.book_triangle_edge_statement <-> book_triangle_edge_statement.
Proof. rewrite /X4Legacy.book_triangle_edge_statement /book_triangle_edge_statement; try setoid_rewrite x4_edge_count_compat; reflexivity. Qed.

Lemma c5_edge_count_above_turan_statement_compat :
  X4Legacy.c5_edge_count_above_turan_statement <-> c5_edge_count_above_turan_statement.
Proof. rewrite /X4Legacy.c5_edge_count_above_turan_statement /c5_edge_count_above_turan_statement; try setoid_rewrite x4_edge_count_compat; reflexivity. Qed.

Lemma triangle_supersaturation_statement_compat :
  X4Legacy.triangle_supersaturation_statement <-> triangle_supersaturation_statement.
Proof. rewrite /X4Legacy.triangle_supersaturation_statement /triangle_supersaturation_statement; try setoid_rewrite x4_edge_count_compat; reflexivity. Qed.

Lemma ck_free_max_cut_polynomial_surplus_statement_compat :
  X76Legacy.ck_free_max_cut_polynomial_surplus_statement <-> ck_free_max_cut_polynomial_surplus_statement.
Proof. rewrite /X76Legacy.ck_free_max_cut_polynomial_surplus_statement /ck_free_max_cut_polynomial_surplus_statement; try setoid_rewrite x76_edge_count_compat; reflexivity. Qed.

Lemma h_free_max_cut_three_fourths_surplus_statement_compat :
  X78Legacy.h_free_max_cut_three_fourths_surplus_statement <-> h_free_max_cut_three_fourths_surplus_statement.
Proof. rewrite /X78Legacy.h_free_max_cut_three_fourths_surplus_statement /h_free_max_cut_three_fourths_surplus_statement; try setoid_rewrite x78_edge_count_compat; reflexivity. Qed.

Lemma pentagonal_turan_stability_dominates_clique_count_statement_compat :
  X88Legacy.pentagonal_turan_stability_dominates_clique_count_statement <-> pentagonal_turan_stability_dominates_clique_count_statement.
Proof. rewrite /X88Legacy.pentagonal_turan_stability_dominates_clique_count_statement /pentagonal_turan_stability_dominates_clique_count_statement; try setoid_rewrite x4_edge_count_compat; try setoid_rewrite turan_number_compat; reflexivity. Qed.

Lemma bollobas_erdos_large_c4_free_subgraph_statement_compat :
  X96Legacy.bollobas_erdos_large_c4_free_subgraph_statement <-> bollobas_erdos_large_c4_free_subgraph_statement.
Proof. rewrite /X96Legacy.bollobas_erdos_large_c4_free_subgraph_statement /bollobas_erdos_large_c4_free_subgraph_statement; try setoid_rewrite x4_edge_count_compat; reflexivity. Qed.

Lemma size_ramsey_compat (H K : sgraph) (m : nat) :
  @XE1Legacy.size_ramsey H K m <-> @xe1_size_ramsey H K m.
Proof. rewrite /XE1Legacy.size_ramsey /xe1_size_ramsey; try setoid_rewrite x4_edge_count_compat; reflexivity. Qed.

Lemma size_ramsey_number_compat (H K : sgraph) (m : nat) :
  @XE1Legacy.size_ramsey_number H K m <-> @xe1_size_ramsey_number H K m.
Proof. rewrite /XE1Legacy.size_ramsey_number /xe1_size_ramsey_number; try setoid_rewrite size_ramsey_compat; reflexivity. Qed.

Lemma every_k_set_sparse_compat (G : sgraph) (k : nat) :
  @XE1Legacy.every_k_set_sparse G k <-> @xe1_every_k_set_sparse G k.
Proof. rewrite /XE1Legacy.every_k_set_sparse /xe1_every_k_set_sparse; try setoid_rewrite x4_edge_count_compat; reflexivity. Qed.

Lemma turan_number_for_graph_compat (F : sgraph) (n m : nat) :
  @XE1Legacy.turan_number_for_graph F n m <-> @xe1_turan_number_for_graph F n m.
Proof. rewrite /XE1Legacy.turan_number_for_graph /xe1_turan_number_for_graph; try setoid_rewrite x4_edge_count_compat; reflexivity. Qed.

Lemma min_turan_over_size_edges_compat (k l n a : nat) :
  @XE1Legacy.min_turan_over_size_edges k l n a <-> @xe1_min_turan_over_size_edges k l n a.
Proof. rewrite /XE1Legacy.min_turan_over_size_edges /xe1_min_turan_over_size_edges; try setoid_rewrite x4_edge_count_compat; try setoid_rewrite turan_number_for_graph_compat; reflexivity. Qed.

Lemma erdos_128_statement_compat :
  XE1Legacy.erdos_128_statement <-> erdos_128_statement.
Proof. rewrite /XE1Legacy.erdos_128_statement /erdos_128_statement; try setoid_rewrite x4_edge_count_compat; reflexivity. Qed.

Lemma erdos_545_statement_compat :
  XE1Legacy.erdos_545_statement <-> erdos_545_statement.
Proof. rewrite /XE1Legacy.erdos_545_statement /erdos_545_statement; try setoid_rewrite x4_edge_count_compat; reflexivity. Qed.

Lemma erdos_548_statement_compat :
  XE1Legacy.erdos_548_statement <-> erdos_548_statement.
Proof. rewrite /XE1Legacy.erdos_548_statement /erdos_548_statement; try setoid_rewrite x4_edge_count_compat; reflexivity. Qed.

Lemma erdos_561_statement_compat :
  XE1Legacy.erdos_561_statement <-> erdos_561_statement.
Proof. rewrite /XE1Legacy.erdos_561_statement /erdos_561_statement; try setoid_rewrite size_ramsey_number_compat; reflexivity. Qed.

Lemma erdos_566_statement_compat :
  XE1Legacy.erdos_566_statement <-> erdos_566_statement.
Proof. rewrite /XE1Legacy.erdos_566_statement /erdos_566_statement; try setoid_rewrite x4_edge_count_compat; try setoid_rewrite every_k_set_sparse_compat; reflexivity. Qed.

Lemma erdos_567_statement_compat :
  XE1Legacy.erdos_567_statement <-> erdos_567_statement.
Proof. rewrite /XE1Legacy.erdos_567_statement /erdos_567_statement; try setoid_rewrite x4_edge_count_compat; reflexivity. Qed.

Lemma erdos_568_statement_compat :
  XE1Legacy.erdos_568_statement <-> erdos_568_statement.
Proof. rewrite /XE1Legacy.erdos_568_statement /erdos_568_statement; try setoid_rewrite x4_edge_count_compat; reflexivity. Qed.

Lemma erdos_766_statement_compat :
  XE1Legacy.erdos_766_statement <-> erdos_766_statement.
Proof. rewrite /XE1Legacy.erdos_766_statement /erdos_766_statement; try setoid_rewrite min_turan_over_size_edges_compat; reflexivity. Qed.

Lemma saturated_planar_compat (G : sgraph) :
  @XE2Legacy.saturated_planar G <-> @xe2_saturated_planar G.
Proof. rewrite /XE2Legacy.saturated_planar /xe2_saturated_planar; try setoid_rewrite x4_edge_count_compat; reflexivity. Qed.

Lemma incident_chord_extremal_compat (k n m : nat) :
  @XE2Legacy.incident_chord_extremal k n m <-> @xe2_incident_chord_extremal k n m.
Proof. rewrite /XE2Legacy.incident_chord_extremal /xe2_incident_chord_extremal; try setoid_rewrite x4_edge_count_compat; reflexivity. Qed.

Lemma erdos_1009_statement_compat :
  XE2Legacy.erdos_1009_statement <-> erdos_1009_statement.
Proof. rewrite /XE2Legacy.erdos_1009_statement /erdos_1009_statement; try setoid_rewrite x4_edge_count_compat; reflexivity. Qed.

Lemma erdos_1018_statement_compat :
  XE2Legacy.erdos_1018_statement <-> erdos_1018_statement.
Proof. rewrite /XE2Legacy.erdos_1018_statement /erdos_1018_statement; try setoid_rewrite x4_edge_count_compat; reflexivity. Qed.

Lemma erdos_1019_statement_compat :
  XE2Legacy.erdos_1019_statement <-> erdos_1019_statement.
Proof. rewrite /XE2Legacy.erdos_1019_statement /erdos_1019_statement; try setoid_rewrite x4_edge_count_compat; try setoid_rewrite saturated_planar_compat; reflexivity. Qed.

Lemma erdos_1080_statement_compat :
  XE2Legacy.erdos_1080_statement <-> erdos_1080_statement.
Proof. rewrite /XE2Legacy.erdos_1080_statement /erdos_1080_statement; try setoid_rewrite x4_edge_count_compat; reflexivity. Qed.

Lemma erdos_22_statement_compat :
  XE2Legacy.erdos_22_statement <-> erdos_22_statement.
Proof. rewrite /XE2Legacy.erdos_22_statement /erdos_22_statement; try setoid_rewrite x4_edge_count_compat; reflexivity. Qed.

Lemma erdos_559_statement_compat :
  XE2Legacy.erdos_559_statement <-> erdos_559_statement.
Proof. rewrite /XE2Legacy.erdos_559_statement /erdos_559_statement; try setoid_rewrite size_ramsey_number_compat; reflexivity. Qed.

Lemma erdos_570_statement_compat :
  XE2Legacy.erdos_570_statement <-> erdos_570_statement.
Proof. rewrite /XE2Legacy.erdos_570_statement /erdos_570_statement; try setoid_rewrite x4_edge_count_compat; reflexivity. Qed.

Lemma erdos_613_statement_compat :
  XE2Legacy.erdos_613_statement <-> erdos_613_statement.
Proof. rewrite /XE2Legacy.erdos_613_statement /erdos_613_statement; try setoid_rewrite x4_edge_count_compat; reflexivity. Qed.

Lemma erdos_742_statement_compat :
  XE2Legacy.erdos_742_statement <-> erdos_742_statement.
Proof. rewrite /XE2Legacy.erdos_742_statement /erdos_742_statement; try setoid_rewrite x4_edge_count_compat; reflexivity. Qed.

Lemma erdos_767_statement_compat :
  XE2Legacy.erdos_767_statement <-> erdos_767_statement.
Proof. rewrite /XE2Legacy.erdos_767_statement /erdos_767_statement; try setoid_rewrite incident_chord_extremal_compat; reflexivity. Qed.

Lemma erdos_801_statement_compat :
  XE2Legacy.erdos_801_statement <-> erdos_801_statement.
Proof. rewrite /XE2Legacy.erdos_801_statement /erdos_801_statement; try setoid_rewrite x4_edge_count_compat; reflexivity. Qed.

Lemma erdos_803_statement_compat :
  XE2Legacy.erdos_803_statement <-> erdos_803_statement.
Proof. rewrite /XE2Legacy.erdos_803_statement /erdos_803_statement; try setoid_rewrite x4_edge_count_compat; reflexivity. Qed.

Lemma erdos_814_statement_compat :
  XE2Legacy.erdos_814_statement <-> erdos_814_statement.
Proof. rewrite /XE2Legacy.erdos_814_statement /erdos_814_statement; try setoid_rewrite x4_edge_count_compat; reflexivity. Qed.

Lemma erdos_816_statement_compat :
  XE2Legacy.erdos_816_statement <-> erdos_816_statement.
Proof. rewrite /XE2Legacy.erdos_816_statement /erdos_816_statement; try setoid_rewrite x4_edge_count_compat; reflexivity. Qed.

Lemma erdos_915_statement_compat :
  XE2Legacy.erdos_915_statement <-> erdos_915_statement.
Proof. rewrite /XE2Legacy.erdos_915_statement /erdos_915_statement; try setoid_rewrite x4_edge_count_compat; reflexivity. Qed.

Lemma x76_edge_count_original_compat (G : sgraph) :
  @X76Original.x76_edge_count G = @x76_edge_count G.
Proof. rewrite /X76Original.x76_edge_count /x76_edge_count; try setoid_rewrite M1.x76_edge_set_compat; reflexivity. Qed.

Lemma x78_edge_count_original_compat (G : sgraph) :
  @X78Original.x78_edge_count G = @x78_edge_count G.
Proof. rewrite /X78Original.x78_edge_count /x78_edge_count; try setoid_rewrite M1.x78_edge_set_compat; reflexivity. Qed.

Lemma turan_number_for_graph_original_compat (F : sgraph) (n m : nat) :
  @XE1Original.turan_number_for_graph F n m <-> @xe1_turan_number_for_graph F n m.
Proof. rewrite /XE1Original.turan_number_for_graph /xe1_turan_number_for_graph; try setoid_rewrite x4_edge_count_compat; try setoid_rewrite A5.xe1_subgraph_of_compat; reflexivity. Qed.

Lemma min_turan_over_size_edges_original_compat (k l n a : nat) :
  @XE1Original.min_turan_over_size_edges k l n a <-> @xe1_min_turan_over_size_edges k l n a.
Proof. rewrite /XE1Original.min_turan_over_size_edges /xe1_min_turan_over_size_edges; try setoid_rewrite x4_edge_count_compat; try setoid_rewrite turan_number_for_graph_original_compat; reflexivity. Qed.

Lemma incident_chord_extremal_original_compat (k n m : nat) :
  @XE2Original.incident_chord_extremal k n m <-> @xe2_incident_chord_extremal k n m.
Proof. rewrite /XE2Original.incident_chord_extremal /xe2_incident_chord_extremal; try setoid_rewrite x4_edge_count_compat; try setoid_rewrite B4.xe2_no_cycle_with_incident_chords_compat; reflexivity. Qed.

Lemma c5_edge_count_above_turan_statement_original_compat :
  X4Original.c5_edge_count_above_turan_statement <-> c5_edge_count_above_turan_statement.
Proof. rewrite /X4Original.c5_edge_count_above_turan_statement /c5_edge_count_above_turan_statement; try setoid_rewrite x4_edge_count_compat; try setoid_rewrite B4.x4_c5_edge_count_compat; reflexivity. Qed.

Lemma ck_free_max_cut_polynomial_surplus_statement_original_compat :
  X76Original.ck_free_max_cut_polynomial_surplus_statement <-> ck_free_max_cut_polynomial_surplus_statement.
Proof. rewrite /X76Original.ck_free_max_cut_polynomial_surplus_statement /ck_free_max_cut_polynomial_surplus_statement; try setoid_rewrite x76_edge_count_original_compat; reflexivity. Qed.

Lemma h_free_max_cut_three_fourths_surplus_statement_original_compat :
  X78Original.h_free_max_cut_three_fourths_surplus_statement <-> h_free_max_cut_three_fourths_surplus_statement.
Proof. rewrite /X78Original.h_free_max_cut_three_fourths_surplus_statement /h_free_max_cut_three_fourths_surplus_statement; try setoid_rewrite A5.x78_subgraph_of_compat; try setoid_rewrite x78_edge_count_original_compat; reflexivity. Qed.

Lemma bollobas_erdos_large_c4_free_subgraph_statement_original_compat :
  X96Original.bollobas_erdos_large_c4_free_subgraph_statement <-> bollobas_erdos_large_c4_free_subgraph_statement.
Proof. rewrite /X96Original.bollobas_erdos_large_c4_free_subgraph_statement /bollobas_erdos_large_c4_free_subgraph_statement; try setoid_rewrite x4_edge_count_compat; try setoid_rewrite A5.x59_subgraph_of_compat; reflexivity. Qed.

Lemma erdos_545_statement_original_compat :
  XE1Original.erdos_545_statement <-> erdos_545_statement.
Proof. rewrite /XE1Original.erdos_545_statement /erdos_545_statement; try setoid_rewrite x4_edge_count_compat; try setoid_rewrite A6.graph_ramsey_number_original_compat; reflexivity. Qed.

Lemma erdos_548_statement_original_compat :
  XE1Original.erdos_548_statement <-> erdos_548_statement.
Proof. rewrite /XE1Original.erdos_548_statement /erdos_548_statement; try setoid_rewrite x4_edge_count_compat; try setoid_rewrite A5.xe1_subgraph_of_compat; reflexivity. Qed.

Lemma erdos_566_statement_original_compat :
  XE1Original.erdos_566_statement <-> erdos_566_statement.
Proof. rewrite /XE1Original.erdos_566_statement /erdos_566_statement; try setoid_rewrite x4_edge_count_compat; try setoid_rewrite A6.graph_ramsey_number_original_compat; try setoid_rewrite every_k_set_sparse_compat; reflexivity. Qed.

Lemma erdos_567_statement_original_compat :
  XE1Original.erdos_567_statement <-> erdos_567_statement.
Proof. rewrite /XE1Original.erdos_567_statement /erdos_567_statement; try setoid_rewrite x4_edge_count_compat; try setoid_rewrite A6.graph_ramsey_number_original_compat; try setoid_rewrite B4.xe1_h5_graph_compat; reflexivity. Qed.

Lemma erdos_568_statement_original_compat :
  XE1Original.erdos_568_statement <-> erdos_568_statement.
Proof. rewrite /XE1Original.erdos_568_statement /erdos_568_statement; try setoid_rewrite x4_edge_count_compat; try setoid_rewrite A6.graph_ramsey_number_original_compat; reflexivity. Qed.

Lemma erdos_766_statement_original_compat :
  XE1Original.erdos_766_statement <-> erdos_766_statement.
Proof. rewrite /XE1Original.erdos_766_statement /erdos_766_statement; try setoid_rewrite min_turan_over_size_edges_original_compat; reflexivity. Qed.

Lemma erdos_570_statement_original_compat :
  XE2Original.erdos_570_statement <-> erdos_570_statement.
Proof. rewrite /XE2Original.erdos_570_statement /erdos_570_statement; try setoid_rewrite x4_edge_count_compat; try setoid_rewrite A6.graph_ramsey_number_original_compat; reflexivity. Qed.

Lemma erdos_1018_statement_original_compat :
  XE2Original.erdos_1018_statement <-> erdos_1018_statement.
Proof. rewrite /XE2Original.erdos_1018_statement /erdos_1018_statement; try setoid_rewrite x4_edge_count_compat; try setoid_rewrite A5.xe1_subgraph_of_compat; reflexivity. Qed.

Lemma erdos_1019_statement_original_compat :
  XE2Original.erdos_1019_statement <-> erdos_1019_statement.
Proof. rewrite /XE2Original.erdos_1019_statement /erdos_1019_statement; try setoid_rewrite x4_edge_count_compat; try setoid_rewrite A5.xe1_subgraph_of_compat; try setoid_rewrite saturated_planar_compat; reflexivity. Qed.

Lemma erdos_1080_statement_original_compat :
  XE2Original.erdos_1080_statement <-> erdos_1080_statement.
Proof. rewrite /XE2Original.erdos_1080_statement /erdos_1080_statement; try setoid_rewrite x4_edge_count_compat; try setoid_rewrite A5.xe1_subgraph_of_compat; try setoid_rewrite C7.xe2_bipartition_sizes_compat; reflexivity. Qed.

Lemma erdos_22_statement_original_compat :
  XE2Original.erdos_22_statement <-> erdos_22_statement.
Proof. rewrite /XE2Original.erdos_22_statement /erdos_22_statement; try setoid_rewrite x4_edge_count_compat; try setoid_rewrite A5.xe1_subgraph_of_compat; reflexivity. Qed.

Lemma erdos_803_statement_original_compat :
  XE2Original.erdos_803_statement <-> erdos_803_statement.
Proof. rewrite /XE2Original.erdos_803_statement /erdos_803_statement; try setoid_rewrite x4_edge_count_compat; try setoid_rewrite A5.xe1_subgraph_of_compat; reflexivity. Qed.

Lemma erdos_613_statement_original_compat :
  XE2Original.erdos_613_statement <-> erdos_613_statement.
Proof. rewrite /XE2Original.erdos_613_statement /erdos_613_statement; try setoid_rewrite x4_edge_count_compat; try setoid_rewrite A2.xe2_bipartite_plus_bounded_degree_compat; reflexivity. Qed.

Lemma erdos_742_statement_original_compat :
  XE2Original.erdos_742_statement <-> erdos_742_statement.
Proof. rewrite /XE2Original.erdos_742_statement /erdos_742_statement; try setoid_rewrite x4_edge_count_compat; try setoid_rewrite A2.xe2_diameter_critical_two_compat; reflexivity. Qed.

Lemma erdos_915_statement_original_compat :
  XE2Original.erdos_915_statement <-> erdos_915_statement.
Proof.
rewrite /XE2Original.erdos_915_statement /erdos_915_statement.
split=> h n m G cardG edges.
- have [x [y [P [xy [ends [dis edis]]]]]] := h n m G cardG (etrans (x4_edge_count_compat G) edges).
  by exists x, y, P; do !split=> //; apply/B2.xe2_paths_internally_disjoint_compat.
- have [x [y [P [xy [ends [dis edis]]]]]] := h n m G cardG (etrans (esym (x4_edge_count_compat G)) edges).
  by exists x, y, P; do !split=> //; apply/B2.xe2_paths_internally_disjoint_compat.
Qed.

Lemma erdos_767_statement_original_compat :
  XE2Original.erdos_767_statement <-> erdos_767_statement.
Proof. rewrite /XE2Original.erdos_767_statement /erdos_767_statement; try setoid_rewrite incident_chord_extremal_original_compat; reflexivity. Qed.
