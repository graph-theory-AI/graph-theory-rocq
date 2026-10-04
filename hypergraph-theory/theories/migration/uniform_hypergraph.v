(** * D1: uniform finite hypergraphs, Hypergraph certificate

    Frozen at the C25 mathematical baseline 3be65eed7084abfae36dee74f7117b598325bc4c
    (implementation parent 277986293d4d5e97b5381db21d35dcd8da95ace9, tooling only).
    - [UniformLegacy]: the seven conjecture-local set-family copies, the public Section-bound
      [hg_uniform]/[hg_uniformb] and the public natural-valued [hg_turan] over the frozen
      Boolean view, verbatim.  The live sources now unfold to
      [GTBase.hypergraph_uniformity.uniform_family] / [uniform_familyb].
    - [<Phase>UniformLegacy]: the reached chains and the complete current rows, each in a
      module importing only its own conjecture module, so that every other name resolves as in
      the source file (U12's Berge edge-connectivity [hg_connected] stays U12's).  These current
      copies keep unrelated live aliases, e.g. A9/A10 cut and degree vocabulary.
    - [<Phase>UniformOriginal]: the five complete A9/A10 + D1 Originals, over the frozen
      uniformity and the A9/A10 frozen modules reached through the aliases [CS]/[ID] (no Import):
      X209's minimum/excess chain over [CS.X209Legacy.scaled_excess] (unused T' and outer-carrier
      E' kept), X6 #834 and XE2 #833 with [ID.Legacy.x6_hg_degree], X108 with
      [ID.X108Legacy.d_degenerate], X225 #01 with the frozen [hg_turan] and the actual frozen
      [ID.FoundationLegacy.dmax] (its opaque [degenerate_ex] witness is reused, not replaced). *)
From GTBase Require Import base.
Require Hypergraph.foundations.hypergraph.
Require Hypergraph.conjectures.U12 Hypergraph.conjectures.X104 Hypergraph.conjectures.X108.
Require Hypergraph.conjectures.X119 Hypergraph.conjectures.X137 Hypergraph.conjectures.X209.
Require Hypergraph.conjectures.X217 Hypergraph.conjectures.X225 Hypergraph.conjectures.X6.
Require Hypergraph.conjectures.XE1 Hypergraph.conjectures.XE2.
Require Hypergraph.migration.cut_size Hypergraph.migration.incidence_degree.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module CS := Hypergraph.migration.cut_size.
Module ID := Hypergraph.migration.incidence_degree.

Module UniformLegacy.

Definition k_uniform (T : finType) (E : {set {set T}}) (k : nat) : Prop :=
  forall e : {set T}, e \in E -> #|e| = k.

Definition x104_uniform (T : finType) (E : {set {set T}}) (r : nat) : Prop :=
  forall e : {set T}, e \in E -> #|e| = r.

Definition x108_uniform (T : finType) (E : {set {set T}}) (r : nat) : Prop :=
  forall e : {set T}, e \in E -> #|e| = r.

Definition x119_uniform (T : finType) (E : {set {set T}}) (r : nat) : Prop :=
  forall e : {set T}, e \in E -> #|e| = r.

Definition x137_uniform (T : finType) (F : {set {set T}}) (r : nat) : Prop :=
  forall A : {set T}, A \in F -> #|A| = r.

Definition x209_uniform (T : finType) (E : {set {set T}}) (k : nat) : Prop :=
  forall e : {set T}, e \in E -> #|e| = k.

Definition x6_uniform (T : finType) (E : {set {set T}}) (r : nat) : Prop :=
  forall e : {set T}, e \in E -> #|e| = r.

Section Hypergraph.
Variable T : finType.
Implicit Types (E : {set {set T}}) (e S : {set T}) (v : T).

Definition hg_uniform E (k : nat) : Prop := forall e, e \in E -> #|e| = k.

Definition hg_uniformb E (k : nat) : bool := [forall e in E, #|e| == k].

End Hypergraph.

Import Hypergraph.foundations.hypergraph.

Definition hg_turan (S : finType) (F : {set {set S}}) (k n : nat) : nat :=
  \max_(E : {set {set 'I_n}} | UniformLegacy.hg_uniformb E k && ~~ hg_containsb F E) #|E|.

End UniformLegacy.

Module U12UniformLegacy.
Import Hypergraph.conjectures.U12.

Definition k_forest (T : finType) (E : {set {set T}}) (k : nat) : Prop :=
  UniformLegacy.k_uniform E k /\ berge_acyclic E.

Definition k_tree (T : finType) (E : {set {set T}}) (k : nat) : Prop :=
  U12UniformLegacy.k_forest E k /\ hg_connected E.

Definition critical_k_forest (T : finType) (E : {set {set T}}) (k : nat) : Prop :=
  U12UniformLegacy.k_forest E k /\
  (forall e : {set T}, #|e| = k -> e \notin E -> berge_cycle (e |: E)).

Definition are_critical_k_forests_tight_statement : Prop :=
  forall (k : nat) (T : finType) (E : {set {set T}}),
    0 < k ->
    E != set0 ->
    U12UniformLegacy.critical_k_forest E k ->
    U12UniformLegacy.k_tree E k.

Definition turans_problem_for_hypergraphs_statement : Prop :=
  forall (n : nat) (T : finType) (E : {set {set T}}),
    0 < n ->
    UniformLegacy.k_uniform E 3 ->
    #|T| = 3 * n ->
    ~ contains_complete E 4 3 ->
    2 * #|E| <= n ^ 2 * (5 * n - 3).

End U12UniformLegacy.

Module X104UniformLegacy.
Import Hypergraph.conjectures.X104.

Definition brown_erdos_sos_three_uniform_statement : Prop :=
  forall e eps_num eps_den : nat,
    3 <= e ->
    0 < eps_num ->
    0 < eps_den ->
    exists N : nat,
      forall (T : finType) (E : {set {set T}}),
        N <= #|T| ->
        UniformLegacy.x104_uniform E 3 ->
        x104_brown_erdos_sos_free E e ->
        eps_den * #|E| <= eps_num * (#|T| ^ 2).

End X104UniformLegacy.

Module X108UniformLegacy.
Import Hypergraph.conjectures.X108.

Definition three_uniform_degenerate_hypergraph_ramsey_linear_statement : Prop :=
  forall d : nat,
    exists c : nat,
      forall (T : finType) (E : {set {set T}}),
        UniformLegacy.x108_uniform E 3 ->
        x108_d_degenerate E d ->
        x108_two_colour_ramsey_at_most E (c * #|T|).

End X108UniformLegacy.

Module X119UniformLegacy.
Import Hypergraph.conjectures.X119.

Definition conlon_fox_sudakov_three_uniform_ramsey_tower_statement : Prop :=
  forall q : nat,
    2 <= q ->
    exists cq : nat,
      forall (T : finType) (E : {set {set T}}),
        UniformLegacy.x119_uniform E 3 ->
        x119_no_isolated E ->
        forall R : nat,
          x119_ramsey_number E q R ->
          R <= 2 ^ (2 ^ (cq * x119_sqrt #|E|)).

End X119UniformLegacy.

Module X137UniformLegacy.
Import Hypergraph.conjectures.X137.

Definition erdos_rado_sunflower_statement : Prop :=
  forall k : nat,
    2 <= k ->
    exists C : nat,
      forall (r : nat) (T : finType) (F : {set {set T}}),
        UniformLegacy.x137_uniform F r ->
        C ^ r < #|F| ->
        exists petals : seq {set T},
          [/\ size petals = k,
              uniq petals,
              (forall A : {set T}, A \in petals -> A \in F) &
              x137_sunflower petals].

End X137UniformLegacy.

Module X209UniformLegacy.
Import Hypergraph.conjectures.X209.

Definition x209_is_min_scaled_excess (r k m x : nat) : Prop :=
  exists (T : finType) (E : {set {set T}}),
    [/\ UniformLegacy.x209_uniform E k, #|E| = m, x209_scaled_excess E r k x &
        forall (T' : finType) (E' : {set {set T}}) (y : nat),
          UniformLegacy.x209_uniform E' k ->
          #|E'| = m ->
          x209_scaled_excess E' r k y ->
          x <= y].

Definition hypergraph_cut_excess_theta_sqrt_statement : Prop :=
  forall r k : nat,
    2 <= r ->
    r <= k ->
    exists excess : nat -> nat,
      (forall m : nat, X209UniformLegacy.x209_is_min_scaled_excess r k m (excess m)) /\
      big_Theta_nat (fun m => (excess m) ^ 2) (fun m => m).

End X209UniformLegacy.

Module X217UniformLegacy.
Import Hypergraph.conjectures.X217.

Definition hypergraph_cop_number_sqrt_n_over_k_statement : Prop :=
  exists C : nat,
    0 < C /\
    forall (T : finType) (E : {set {set T}}) (k c : nat),
      0 < k ->
      k <= #|T| ->
      UniformLegacy.hg_uniform E k ->
      hg_connected E ->
      hg_is_cop_number E c ->
      c ^ 2 * k <= C ^ 2 * #|T|.

End X217UniformLegacy.

Module X225UniformLegacy.
Import Hypergraph.conjectures.X225.

Definition kpartite_hypergraph_turan_exponent_dmax_statement : Prop :=
  forall k : nat,
    2 <= k ->
    exists ck : nat,
      0 < ck /\
      forall (S : finType) (F : {set {set S}}) (part : S -> 'I_k),
        F != set0 ->
        UniformLegacy.hg_uniform F k ->
        hg_partite_uniform part F ->
        exists K : nat,
          0 < K /\
          eventually (fun n =>
            (UniformLegacy.hg_turan F k n) ^ (hg_dmax F k) * n ^ ck <= K * n ^ (k * hg_dmax F k)).

Definition latin_square_hypergraph_turan_exponent_statement : Prop :=
  exists a b : nat,
    [/\ 0 < a,
        0 < b &
        forall (d : nat) (L : 'I_d -> 'I_d -> 'I_d),
          2 <= d ->
          x225_latin_square L ->
          eventually (fun n =>
            n ^ (3 * d) <= (UniformLegacy.hg_turan (x225_latin_hypergraph L) 3 n) ^ d * n ^ a /\
            (UniformLegacy.hg_turan (x225_latin_hypergraph L) 3 n) ^ d * n ^ b <= n ^ (3 * d))].

End X225UniformLegacy.

Module X6UniformLegacy.
Import Hypergraph.conjectures.X6.

Definition x6_extremal_no_k_matching (n r k m : nat) : Prop :=
  (exists (T : finType) (E : {set {set T}}),
     [/\ #|T| = n, UniformLegacy.x6_uniform E r, #|E| = m & x6_no_k_matching E k]) /\
  forall m' : nat,
    (exists (T : finType) (E : {set {set T}}),
       [/\ #|T| = n, UniformLegacy.x6_uniform E r, #|E| = m' & x6_no_k_matching E k]) ->
    m' <= m.

Definition critical_three_uniform_min_degree_seven_statement : Prop :=
  exists (T : finType) (E : {set {set T}}),
    UniformLegacy.x6_uniform E 3 /\
    x6_chromatic_edge_critical E 3 /\
    (forall v : T, 7 <= x6_hg_degree E v).

Definition erdos_matching_extremal_formula_statement : Prop :=
  forall n r k m : nat,
    3 <= r -> 1 <= k ->
    r * k - 1 <= n ->
    X6UniformLegacy.x6_extremal_no_k_matching n r k m ->
    m = maxn 'C(r * k - 1, r) ('C(n, r) - 'C(n - k + 1, r)).

Definition three_uniform_hypergraph_dense_small_configuration_statement : Prop :=
  forall (n : nat) (T : finType) (E : {set {set T}}),
    UniformLegacy.x6_uniform E 3 ->
    #|T| = 3 * n ->
    n ^ 3 + 1 <= #|E| ->
    (exists S : {set T}, #|S| = 4 /\ 3 <= x6_edges_on E S) \/
    (exists S : {set T}, #|S| = 5 /\ 7 <= x6_edges_on E S).

End X6UniformLegacy.

Module XE1UniformLegacy.
Import Hypergraph.conjectures.X6.
Import Hypergraph.conjectures.XE1.

Definition xe1_extremal_no_complete_uniform (n r q m : nat) : Prop :=
  (exists (T : finType) (E : {set {set T}}),
      [/\ #|T| = n, UniformLegacy.x6_uniform E r, ~ xe1_contains_complete_uniform E r q
        & #|E| = m]) /\
  forall m' : nat,
    (exists (T : finType) (E : {set {set T}}),
      [/\ #|T| = n, UniformLegacy.x6_uniform E r, ~ xe1_contains_complete_uniform E r q
        & #|E| = m']) ->
    m' <= m.

Definition erdos_719_statement : Prop :=
  forall (r n ex : nat) (T : finType) (E : {set {set T}}),
    2 <= r -> #|T| = n -> UniformLegacy.x6_uniform E r ->
    XE1UniformLegacy.xe1_extremal_no_complete_uniform n r r.+1 ex ->
    xe1_hypergraph_decomposition_bound E r ex.

Definition erdos_836_statement : Prop :=
  (exists C : nat,
      forall (r : nat) (T : finType) (E : {set {set T}}),
        2 <= r -> UniformLegacy.x6_uniform E r -> x6_chromatic_number E 3 ->
        xe1_intersecting_hypergraph E ->
        (forall v : T, exists e : {set T}, e \in E /\ v \in e) ->
        #|T| <= C * r ^ 2) /\
  (exists cnum cden : nat,
      0 < cnum /\ 0 < cden /\
      forall (r : nat) (T : finType) (E : {set {set T}}),
        2 <= r -> UniformLegacy.x6_uniform E r -> x6_chromatic_number E 3 ->
        xe1_intersecting_hypergraph E ->
        exists e f : {set T},
          e \in E /\ f \in E /\ e != f /\ cnum * r <= cden * #|e :&: f|).

End XE1UniformLegacy.

Module XE2UniformLegacy.
Import Hypergraph.conjectures.X6.
Import Hypergraph.conjectures.XE1.
Import Hypergraph.conjectures.XE2.

Definition erdos_775_statement : Prop :=
  exists C : nat,
    forall n : nat, exists (T : finType) (E : {set {set T}}) (L : seq nat),
      #|T| = n /\
      UniformLegacy.x6_uniform E 3 /\
      xe2_clique_size_set E L /\
      n <= size L + C.

Definition erdos_832_statement : Prop :=
  forall r : nat, 3 <= r ->
    exists K : nat,
      forall (k : nat) (T : finType) (E : {set {set T}}),
        K <= k ->
        UniformLegacy.x6_uniform E r ->
        x6_chromatic_number E k ->
        'C((r - 1) * (k - 1) + 1, r) <= #|E| /\
        (#|E| = 'C((r - 1) * (k - 1) + 1, r) ->
          exists S : {set T},
            #|S| = (r - 1) * (k - 1) + 1 /\
            xe2_complete_uniform_on E r S).

Definition erdos_833_statement : Prop :=
  exists cnum cden : nat,
    0 < cnum /\ 0 < cden /\
    forall (r : nat) (T : finType) (E : {set {set T}}),
      2 <= r ->
      UniformLegacy.x6_uniform E r ->
      x6_chromatic_number E 3 ->
      exists v : T,
        xe2_fractional_exponential_degree cnum cden r (x6_hg_degree E v).

End XE2UniformLegacy.

Module X209UniformOriginal.
Import Hypergraph.conjectures.X209.

Definition x209_is_min_scaled_excess (r k m x : nat) : Prop :=
  exists (T : finType) (E : {set {set T}}),
    [/\ UniformLegacy.x209_uniform E k, #|E| = m, CS.X209Legacy.scaled_excess E r k x &
        forall (T' : finType) (E' : {set {set T}}) (y : nat),
          UniformLegacy.x209_uniform E' k ->
          #|E'| = m ->
          CS.X209Legacy.scaled_excess E' r k y ->
          x <= y].

Definition hypergraph_cut_excess_theta_sqrt_statement : Prop :=
  forall r k : nat,
    2 <= r ->
    r <= k ->
    exists excess : nat -> nat,
      (forall m : nat, X209UniformOriginal.x209_is_min_scaled_excess r k m (excess m)) /\
      big_Theta_nat (fun m => (excess m) ^ 2) (fun m => m).

End X209UniformOriginal.

Module X6UniformOriginal.
Import Hypergraph.conjectures.X6.

Definition critical_three_uniform_min_degree_seven_statement : Prop :=
  exists (T : finType) (E : {set {set T}}),
    UniformLegacy.x6_uniform E 3 /\
    x6_chromatic_edge_critical E 3 /\
    (forall v : T, 7 <= ID.Legacy.x6_hg_degree E v).

End X6UniformOriginal.

Module XE2UniformOriginal.
Import Hypergraph.conjectures.X6.
Import Hypergraph.conjectures.XE1.
Import Hypergraph.conjectures.XE2.

Definition erdos_833_statement : Prop :=
  exists cnum cden : nat,
    0 < cnum /\ 0 < cden /\
    forall (r : nat) (T : finType) (E : {set {set T}}),
      2 <= r ->
      UniformLegacy.x6_uniform E r ->
      x6_chromatic_number E 3 ->
      exists v : T,
        xe2_fractional_exponential_degree cnum cden r (ID.Legacy.x6_hg_degree E v).

End XE2UniformOriginal.

Module X108UniformOriginal.
Import Hypergraph.conjectures.X108.

Definition three_uniform_degenerate_hypergraph_ramsey_linear_statement : Prop :=
  forall d : nat,
    exists c : nat,
      forall (T : finType) (E : {set {set T}}),
        UniformLegacy.x108_uniform E 3 ->
        ID.X108Legacy.d_degenerate E d ->
        x108_two_colour_ramsey_at_most E (c * #|T|).

End X108UniformOriginal.

Module X225UniformOriginal.
Import Hypergraph.conjectures.X225.

Definition kpartite_hypergraph_turan_exponent_dmax_statement : Prop :=
  forall k : nat,
    2 <= k ->
    exists ck : nat,
      0 < ck /\
      forall (S : finType) (F : {set {set S}}) (part : S -> 'I_k),
        F != set0 ->
        UniformLegacy.hg_uniform F k ->
        hg_partite_uniform part F ->
        exists K : nat,
          0 < K /\
          eventually (fun n =>
            (UniformLegacy.hg_turan F k n) ^ (ID.FoundationLegacy.dmax F k) * n ^ ck <= K * n ^ (k * ID.FoundationLegacy.dmax F k)).

End X225UniformOriginal.

Lemma k_uniform_compat (T : finType) (E : {set {set T}}) (k : nat) :
  @UniformLegacy.k_uniform T E k <->
  @Hypergraph.conjectures.U12.k_uniform T E k.
Proof.
exact: iff_refl.
Qed.

Lemma x104_uniform_compat (T : finType) (E : {set {set T}}) (r : nat) :
  @UniformLegacy.x104_uniform T E r <->
  @Hypergraph.conjectures.X104.x104_uniform T E r.
Proof.
exact: iff_refl.
Qed.

Lemma x108_uniform_compat (T : finType) (E : {set {set T}}) (r : nat) :
  @UniformLegacy.x108_uniform T E r <->
  @Hypergraph.conjectures.X108.x108_uniform T E r.
Proof.
exact: iff_refl.
Qed.

Lemma x119_uniform_compat (T : finType) (E : {set {set T}}) (r : nat) :
  @UniformLegacy.x119_uniform T E r <->
  @Hypergraph.conjectures.X119.x119_uniform T E r.
Proof.
exact: iff_refl.
Qed.

Lemma x137_uniform_compat (T : finType) (F : {set {set T}}) (r : nat) :
  @UniformLegacy.x137_uniform T F r <->
  @Hypergraph.conjectures.X137.x137_uniform T F r.
Proof.
exact: iff_refl.
Qed.

Lemma x209_uniform_compat (T : finType) (E : {set {set T}}) (k : nat) :
  @UniformLegacy.x209_uniform T E k <->
  @Hypergraph.conjectures.X209.x209_uniform T E k.
Proof.
exact: iff_refl.
Qed.

Lemma x6_uniform_compat (T : finType) (E : {set {set T}}) (r : nat) :
  @UniformLegacy.x6_uniform T E r <->
  @Hypergraph.conjectures.X6.x6_uniform T E r.
Proof.
exact: iff_refl.
Qed.

Lemma hg_uniform_compat (T : finType) (E : {set {set T}}) (k : nat) :
  @UniformLegacy.hg_uniform T E k <->
  @Hypergraph.foundations.hypergraph.hg_uniform T E k.
Proof.
exact: iff_refl.
Qed.

Lemma hg_uniformb_compat (T : finType) (E : {set {set T}}) (k : nat) :
  @UniformLegacy.hg_uniformb T E k =
  @Hypergraph.foundations.hypergraph.hg_uniformb T E k.
Proof.
by [].
Qed.

Lemma hg_turan_compat (S : finType) (F : {set {set S}}) (k n : nat) :
  @UniformLegacy.hg_turan S F k n =
  @Hypergraph.foundations.hypergraph.hg_turan S F k n.
Proof.
by [].
Qed.

Lemma k_forest_compat (T : finType) (E : {set {set T}}) (k : nat) :
  @U12UniformLegacy.k_forest T E k <->
  @Hypergraph.conjectures.U12.k_forest T E k.
Proof.
exact: iff_refl.
Qed.

Lemma k_tree_compat (T : finType) (E : {set {set T}}) (k : nat) :
  @U12UniformLegacy.k_tree T E k <->
  @Hypergraph.conjectures.U12.k_tree T E k.
Proof.
exact: iff_refl.
Qed.

Lemma critical_k_forest_compat (T : finType) (E : {set {set T}}) (k : nat) :
  @U12UniformLegacy.critical_k_forest T E k <->
  @Hypergraph.conjectures.U12.critical_k_forest T E k.
Proof.
exact: iff_refl.
Qed.

Lemma are_critical_k_forests_tight_statement_compat :
  U12UniformLegacy.are_critical_k_forests_tight_statement <->
  Hypergraph.conjectures.U12.are_critical_k_forests_tight_statement.
Proof.
exact: iff_refl.
Qed.

Lemma turans_problem_for_hypergraphs_statement_compat :
  U12UniformLegacy.turans_problem_for_hypergraphs_statement <->
  Hypergraph.conjectures.U12.turans_problem_for_hypergraphs_statement.
Proof.
exact: iff_refl.
Qed.

Lemma brown_erdos_sos_three_uniform_statement_compat :
  X104UniformLegacy.brown_erdos_sos_three_uniform_statement <->
  Hypergraph.conjectures.X104.brown_erdos_sos_three_uniform_statement.
Proof.
exact: iff_refl.
Qed.

Lemma three_uniform_degenerate_hypergraph_ramsey_linear_statement_compat :
  X108UniformLegacy.three_uniform_degenerate_hypergraph_ramsey_linear_statement <->
  Hypergraph.conjectures.X108.three_uniform_degenerate_hypergraph_ramsey_linear_statement.
Proof.
exact: iff_refl.
Qed.

Lemma conlon_fox_sudakov_three_uniform_ramsey_tower_statement_compat :
  X119UniformLegacy.conlon_fox_sudakov_three_uniform_ramsey_tower_statement <->
  Hypergraph.conjectures.X119.conlon_fox_sudakov_three_uniform_ramsey_tower_statement.
Proof.
exact: iff_refl.
Qed.

Lemma erdos_rado_sunflower_statement_compat :
  X137UniformLegacy.erdos_rado_sunflower_statement <->
  Hypergraph.conjectures.X137.erdos_rado_sunflower_statement.
Proof.
exact: iff_refl.
Qed.

Lemma x209_is_min_scaled_excess_compat (r k m x : nat) :
  @X209UniformLegacy.x209_is_min_scaled_excess r k m x <->
  @Hypergraph.conjectures.X209.x209_is_min_scaled_excess r k m x.
Proof.
exact: iff_refl.
Qed.

Lemma hypergraph_cut_excess_theta_sqrt_statement_compat :
  X209UniformLegacy.hypergraph_cut_excess_theta_sqrt_statement <->
  Hypergraph.conjectures.X209.hypergraph_cut_excess_theta_sqrt_statement.
Proof.
exact: iff_refl.
Qed.

Lemma hypergraph_cop_number_sqrt_n_over_k_statement_compat :
  X217UniformLegacy.hypergraph_cop_number_sqrt_n_over_k_statement <->
  Hypergraph.conjectures.X217.hypergraph_cop_number_sqrt_n_over_k_statement.
Proof.
exact: iff_refl.
Qed.

Lemma kpartite_hypergraph_turan_exponent_dmax_statement_compat :
  X225UniformLegacy.kpartite_hypergraph_turan_exponent_dmax_statement <->
  Hypergraph.conjectures.X225.kpartite_hypergraph_turan_exponent_dmax_statement.
Proof.
exact: iff_refl.
Qed.

Lemma latin_square_hypergraph_turan_exponent_statement_compat :
  X225UniformLegacy.latin_square_hypergraph_turan_exponent_statement <->
  Hypergraph.conjectures.X225.latin_square_hypergraph_turan_exponent_statement.
Proof.
exact: iff_refl.
Qed.

Lemma x6_extremal_no_k_matching_compat (n r k m : nat) :
  @X6UniformLegacy.x6_extremal_no_k_matching n r k m <->
  @Hypergraph.conjectures.X6.x6_extremal_no_k_matching n r k m.
Proof.
exact: iff_refl.
Qed.

Lemma critical_three_uniform_min_degree_seven_statement_compat :
  X6UniformLegacy.critical_three_uniform_min_degree_seven_statement <->
  Hypergraph.conjectures.X6.critical_three_uniform_min_degree_seven_statement.
Proof.
exact: iff_refl.
Qed.

Lemma erdos_matching_extremal_formula_statement_compat :
  X6UniformLegacy.erdos_matching_extremal_formula_statement <->
  Hypergraph.conjectures.X6.erdos_matching_extremal_formula_statement.
Proof.
exact: iff_refl.
Qed.

Lemma three_uniform_hypergraph_dense_small_configuration_statement_compat :
  X6UniformLegacy.three_uniform_hypergraph_dense_small_configuration_statement <->
  Hypergraph.conjectures.X6.three_uniform_hypergraph_dense_small_configuration_statement.
Proof.
exact: iff_refl.
Qed.

Lemma xe1_extremal_no_complete_uniform_compat (n r q m : nat) :
  @XE1UniformLegacy.xe1_extremal_no_complete_uniform n r q m <->
  @Hypergraph.conjectures.XE1.xe1_extremal_no_complete_uniform n r q m.
Proof.
exact: iff_refl.
Qed.

Lemma erdos_719_statement_compat :
  XE1UniformLegacy.erdos_719_statement <->
  Hypergraph.conjectures.XE1.erdos_719_statement.
Proof.
exact: iff_refl.
Qed.

Lemma erdos_836_statement_compat :
  XE1UniformLegacy.erdos_836_statement <->
  Hypergraph.conjectures.XE1.erdos_836_statement.
Proof.
exact: iff_refl.
Qed.

Lemma erdos_775_statement_compat :
  XE2UniformLegacy.erdos_775_statement <->
  Hypergraph.conjectures.XE2.erdos_775_statement.
Proof.
exact: iff_refl.
Qed.

Lemma erdos_832_statement_compat :
  XE2UniformLegacy.erdos_832_statement <->
  Hypergraph.conjectures.XE2.erdos_832_statement.
Proof.
exact: iff_refl.
Qed.

Lemma erdos_833_statement_compat :
  XE2UniformLegacy.erdos_833_statement <->
  Hypergraph.conjectures.XE2.erdos_833_statement.
Proof.
exact: iff_refl.
Qed.

Lemma x209_is_min_scaled_excess_original_compat (r k m x : nat) :
  @X209UniformOriginal.x209_is_min_scaled_excess r k m x <->
  @Hypergraph.conjectures.X209.x209_is_min_scaled_excess r k m x.
Proof.
have C := @CS.x209_scaled_excess_compat.
split=> -[T [E [uE cE sE min]]]; exists T, E; split=> //.
- exact: (proj1 (C _ _ _ _ _) sE).
- by move=> T' E' y uE' cE' sE'; exact: (min T' E' y uE' cE' (proj2 (C _ _ _ _ _) sE')).
- exact: (proj2 (C _ _ _ _ _) sE).
- by move=> T' E' y uE' cE' sE'; exact: (min T' E' y uE' cE' (proj1 (C _ _ _ _ _) sE')).
Qed.

Lemma hypergraph_cut_excess_theta_sqrt_statement_original_compat :
  X209UniformOriginal.hypergraph_cut_excess_theta_sqrt_statement <->
  Hypergraph.conjectures.X209.hypergraph_cut_excess_theta_sqrt_statement.
Proof.
split=> st r k r2 rk; have [excess [ex th]] := st r k r2 rk; exists excess; split=> // m.
- exact: (proj1 (x209_is_min_scaled_excess_original_compat _ _ _ _) (ex m)).
- exact: (proj2 (x209_is_min_scaled_excess_original_compat _ _ _ _) (ex m)).
Qed.

Lemma critical_three_uniform_min_degree_seven_statement_original_compat :
  X6UniformOriginal.critical_three_uniform_min_degree_seven_statement <->
  Hypergraph.conjectures.X6.critical_three_uniform_min_degree_seven_statement.
Proof.
exact: ID.critical_three_uniform_min_degree_seven_statement_compat.
Qed.

Lemma erdos_833_statement_original_compat :
  XE2UniformOriginal.erdos_833_statement <->
  Hypergraph.conjectures.XE2.erdos_833_statement.
Proof.
exact: ID.erdos_833_statement_compat.
Qed.

Lemma three_uniform_degenerate_hypergraph_ramsey_linear_statement_original_compat :
  X108UniformOriginal.three_uniform_degenerate_hypergraph_ramsey_linear_statement <->
  Hypergraph.conjectures.X108.three_uniform_degenerate_hypergraph_ramsey_linear_statement.
Proof.
exact: ID.three_uniform_degenerate_hypergraph_ramsey_linear_statement_compat.
Qed.

Lemma kpartite_hypergraph_turan_exponent_dmax_statement_original_compat :
  X225UniformOriginal.kpartite_hypergraph_turan_exponent_dmax_statement <->
  Hypergraph.conjectures.X225.kpartite_hypergraph_turan_exponent_dmax_statement.
Proof.
exact: ID.kpartite_hypergraph_turan_exponent_dmax_statement_compat.
Qed.

Print Assumptions k_uniform_compat.
Print Assumptions x104_uniform_compat.
Print Assumptions x108_uniform_compat.
Print Assumptions x119_uniform_compat.
Print Assumptions x137_uniform_compat.
Print Assumptions x209_uniform_compat.
Print Assumptions x6_uniform_compat.
Print Assumptions hg_uniform_compat.
Print Assumptions hg_uniformb_compat.
Print Assumptions hg_turan_compat.
Print Assumptions k_forest_compat.
Print Assumptions k_tree_compat.
Print Assumptions critical_k_forest_compat.
Print Assumptions are_critical_k_forests_tight_statement_compat.
Print Assumptions turans_problem_for_hypergraphs_statement_compat.
Print Assumptions brown_erdos_sos_three_uniform_statement_compat.
Print Assumptions three_uniform_degenerate_hypergraph_ramsey_linear_statement_compat.
Print Assumptions conlon_fox_sudakov_three_uniform_ramsey_tower_statement_compat.
Print Assumptions erdos_rado_sunflower_statement_compat.
Print Assumptions x209_is_min_scaled_excess_compat.
Print Assumptions hypergraph_cut_excess_theta_sqrt_statement_compat.
Print Assumptions hypergraph_cop_number_sqrt_n_over_k_statement_compat.
Print Assumptions kpartite_hypergraph_turan_exponent_dmax_statement_compat.
Print Assumptions latin_square_hypergraph_turan_exponent_statement_compat.
Print Assumptions x6_extremal_no_k_matching_compat.
Print Assumptions critical_three_uniform_min_degree_seven_statement_compat.
Print Assumptions erdos_matching_extremal_formula_statement_compat.
Print Assumptions three_uniform_hypergraph_dense_small_configuration_statement_compat.
Print Assumptions xe1_extremal_no_complete_uniform_compat.
Print Assumptions erdos_719_statement_compat.
Print Assumptions erdos_836_statement_compat.
Print Assumptions erdos_775_statement_compat.
Print Assumptions erdos_832_statement_compat.
Print Assumptions erdos_833_statement_compat.
Print Assumptions x209_is_min_scaled_excess_original_compat.
Print Assumptions hypergraph_cut_excess_theta_sqrt_statement_original_compat.
Print Assumptions critical_three_uniform_min_degree_seven_statement_original_compat.
Print Assumptions erdos_833_statement_original_compat.
Print Assumptions three_uniform_degenerate_hypergraph_ramsey_linear_statement_original_compat.
Print Assumptions kpartite_hypergraph_turan_exponent_dmax_statement_original_compat.
