(** * D6: matchings of a supplied hyperedge family, Hypergraph certificate

    Frozen at the D5 pin e14645d6fb6068c1a89862f60b82e958212f2422.  Every frozen text is byte-identical
    at the matching family baseline 9e030727db115917ae077ac07a8fc6aa68661f73, where
    meta/migration_reports/matching.spec.json binds it (semantic class hypergraph-edge-family).
    - [Legacy]: U12's [hg_matching] and X6's [x6_matching], verbatim.  Both sources now unfold to the
      public [Hypergraph.foundations.hypergraph_matchings.hg_matching], with the same finite carrier
      and [M] before [E].
    - [<Phase>MatchingLegacy]: the matching-number, no-k-matching and extremal chains (kept as chains)
      and the five complete current rows (U12 Ryser, X6 Lovasz deletion and its trade-off, X6 #1020,
      X73).  These current copies keep the unrelated live D1 uniformity, D2 partiteness and A10
      regularity aliases.
    - [<Phase>MatchingOriginal]: the complete original extremal chain and the five complete Originals,
      reached through the aliases [PU]/[UH]/[ID] (no Import): the actual raw D2 partite sources, D1's
      raw [x6_uniform] and A10's raw [X73Legacy.hyperdegree_regular].
    Older partial snapshots (A10 X73Legacy, D2 U12/X6/X73 rows and the X73 Original, D1 X6 extremal
    chain and #1020 row) stay as they are; the spec records them and points to these rows. *)
From GTBase Require Import base.
Require Hypergraph.foundations.hypergraph_matchings.
Require Hypergraph.conjectures.U12 Hypergraph.conjectures.X6 Hypergraph.conjectures.X73.
Require Hypergraph.migration.partite_uniform Hypergraph.migration.uniform_hypergraph.
Require Hypergraph.migration.incidence_degree.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module PU := Hypergraph.migration.partite_uniform.
Module UH := Hypergraph.migration.uniform_hypergraph.
Module ID := Hypergraph.migration.incidence_degree.

Module Legacy.

Definition hg_matching (T : finType) (M E : {set {set T}}) : Prop :=
  M \subset E /\
  {in M &, forall e f : {set T}, e != f -> [disjoint e & f]}.

Definition x6_matching (T : finType) (M E : {set {set T}}) : Prop :=
  M \subset E /\
  {in M &, forall e f : {set T}, e != f -> [disjoint e & f]}.

End Legacy.

Module U12MatchingLegacy.
Import Hypergraph.conjectures.U12.

Definition is_matching_number (T : finType) (E : {set {set T}}) (nu : nat) : Prop :=
  (exists M : {set {set T}}, Legacy.hg_matching M E /\ #|M| = nu) /\
  (forall M : {set {set T}}, Legacy.hg_matching M E -> #|M| <= nu).

Definition rysers_statement : Prop :=
  forall (r : nat) (T : finType) (part : T -> 'I_r) (E : {set {set T}})
         (nu tau : nat),
    1 < r ->
    r_partite_uniform part E ->
    U12MatchingLegacy.is_matching_number E nu ->
    is_cover_number E tau ->
    tau <= (r - 1) * nu.

End U12MatchingLegacy.

Module X6MatchingLegacy.
Import Hypergraph.conjectures.X6.

Definition x6_matching_number (T : finType) (E : {set {set T}}) (nu : nat) : Prop :=
  (exists M : {set {set T}}, Legacy.x6_matching M E /\ #|M| = nu) /\
  (forall M : {set {set T}}, Legacy.x6_matching M E -> #|M| <= nu).

Definition x6_no_k_matching (T : finType) (E : {set {set T}}) (k : nat) : Prop :=
  forall M : {set {set T}}, Legacy.x6_matching M E -> #|M| < k.

Definition x6_extremal_no_k_matching (n r k m : nat) : Prop :=
  (exists (T : finType) (E : {set {set T}}),
     [/\ #|T| = n, x6_uniform E r, #|E| = m & X6MatchingLegacy.x6_no_k_matching E k]) /\
  forall m' : nat,
    (exists (T : finType) (E : {set {set T}}),
       [/\ #|T| = n, x6_uniform E r, #|E| = m' & X6MatchingLegacy.x6_no_k_matching E k]) ->
    m' <= m.

Definition lovasz_r_partite_matching_deletion_statement : Prop :=
  forall (r : nat) (T : finType) (part : T -> 'I_r) (E : {set {set T}})
         (nu : nat),
    1 < r ->
    E != set0 ->
    x6_r_partite_uniform part E ->
    X6MatchingLegacy.x6_matching_number E nu ->
    exists X : {set T}, #|X| = r - 1 /\
      exists nu' : nat,
        X6MatchingLegacy.x6_matching_number (x6_delete_vertices E X) nu' /\ nu' < nu.

Definition r_partite_matching_deletion_tradeoff_statement : Prop :=
  forall (r : nat) (T : finType) (part : T -> 'I_r) (E : {set {set T}})
         (nu : nat),
    1 < r ->
    E != set0 ->
    x6_r_partite_uniform part E ->
    X6MatchingLegacy.x6_matching_number E nu ->
    exists (k : nat) (X : {set T}),
      1 <= k /\ k <= r - 1 /\
      #|X| = k * (r - 1) /\
      exists nu' : nat,
        X6MatchingLegacy.x6_matching_number (x6_delete_vertices E X) nu' /\ nu' + k <= nu.

Definition erdos_matching_extremal_formula_statement : Prop :=
  forall n r k m : nat,
    3 <= r -> 1 <= k ->
    r * k - 1 <= n ->
    X6MatchingLegacy.x6_extremal_no_k_matching n r k m ->
    m = maxn 'C(r * k - 1, r) ('C(n, r) - 'C(n - k + 1, r)).

End X6MatchingLegacy.

Module X73MatchingLegacy.
Import Hypergraph.conjectures.X6 Hypergraph.conjectures.X73.

Definition regular_tripartite_hypergraph_matching_lower_bound_statement : Prop :=
  forall (d n : nat) (T : finType) (part : T -> 'I_3) (E : {set {set T}}),
    1 <= d ->
    x73_balanced_tripartite part n ->
    @x6_r_partite_uniform T 3 part E ->
    x73_regular E d ->
    exists M : {set {set T}},
      Legacy.x6_matching M E /\ ((d.-1 * n) %/ d <= #|M|).

End X73MatchingLegacy.

Module U12MatchingOriginal.
Import Hypergraph.conjectures.U12.

Definition rysers_statement : Prop :=
  forall (r : nat) (T : finType) (part : T -> 'I_r) (E : {set {set T}})
         (nu tau : nat),
    1 < r ->
    PU.PartiteLegacy.r_partite_uniform part E ->
    U12MatchingLegacy.is_matching_number E nu ->
    is_cover_number E tau ->
    tau <= (r - 1) * nu.

End U12MatchingOriginal.

Module X6MatchingOriginal.
Import Hypergraph.conjectures.X6.

Definition x6_extremal_no_k_matching (n r k m : nat) : Prop :=
  (exists (T : finType) (E : {set {set T}}),
     [/\ #|T| = n, UH.UniformLegacy.x6_uniform E r, #|E| = m & X6MatchingLegacy.x6_no_k_matching E k]) /\
  forall m' : nat,
    (exists (T : finType) (E : {set {set T}}),
       [/\ #|T| = n, UH.UniformLegacy.x6_uniform E r, #|E| = m' & X6MatchingLegacy.x6_no_k_matching E k]) ->
    m' <= m.

Definition lovasz_r_partite_matching_deletion_statement : Prop :=
  forall (r : nat) (T : finType) (part : T -> 'I_r) (E : {set {set T}})
         (nu : nat),
    1 < r ->
    E != set0 ->
    PU.PartiteLegacy.x6_r_partite_uniform part E ->
    X6MatchingLegacy.x6_matching_number E nu ->
    exists X : {set T}, #|X| = r - 1 /\
      exists nu' : nat,
        X6MatchingLegacy.x6_matching_number (x6_delete_vertices E X) nu' /\ nu' < nu.

Definition r_partite_matching_deletion_tradeoff_statement : Prop :=
  forall (r : nat) (T : finType) (part : T -> 'I_r) (E : {set {set T}})
         (nu : nat),
    1 < r ->
    E != set0 ->
    PU.PartiteLegacy.x6_r_partite_uniform part E ->
    X6MatchingLegacy.x6_matching_number E nu ->
    exists (k : nat) (X : {set T}),
      1 <= k /\ k <= r - 1 /\
      #|X| = k * (r - 1) /\
      exists nu' : nat,
        X6MatchingLegacy.x6_matching_number (x6_delete_vertices E X) nu' /\ nu' + k <= nu.

Definition erdos_matching_extremal_formula_statement : Prop :=
  forall n r k m : nat,
    3 <= r -> 1 <= k ->
    r * k - 1 <= n ->
    X6MatchingOriginal.x6_extremal_no_k_matching n r k m ->
    m = maxn 'C(r * k - 1, r) ('C(n, r) - 'C(n - k + 1, r)).

End X6MatchingOriginal.

Module X73MatchingOriginal.
Import Hypergraph.conjectures.X6 Hypergraph.conjectures.X73.

Definition regular_tripartite_hypergraph_matching_lower_bound_statement : Prop :=
  forall (d n : nat) (T : finType) (part : T -> 'I_3) (E : {set {set T}}),
    1 <= d ->
    x73_balanced_tripartite part n ->
    @PU.PartiteLegacy.x6_r_partite_uniform T 3 part E ->
    ID.X73Legacy.hyperdegree_regular E d ->
    exists M : {set {set T}},
      Legacy.x6_matching M E /\ ((d.-1 * n) %/ d <= #|M|).

End X73MatchingOriginal.

(** Every frozen copy has the same body as its live counterpart once the live aliases (this family's
    [hg_matching], D1 uniformity, D2 partiteness, A10 degree) are unfolded: all seventeen bridges are
    conversions. *)

Lemma hg_matching_compat (T : finType) (M E : {set {set T}}) :
  @Legacy.hg_matching T M E <->
  @Hypergraph.conjectures.U12.hg_matching T M E.
Proof. exact: iff_refl. Qed.

Lemma x6_matching_compat (T : finType) (M E : {set {set T}}) :
  @Legacy.x6_matching T M E <->
  @Hypergraph.conjectures.X6.x6_matching T M E.
Proof. exact: iff_refl. Qed.

Lemma is_matching_number_compat (T : finType) (E : {set {set T}}) (nu : nat) :
  @U12MatchingLegacy.is_matching_number T E nu <->
  @Hypergraph.conjectures.U12.is_matching_number T E nu.
Proof. exact: iff_refl. Qed.

Lemma x6_matching_number_compat (T : finType) (E : {set {set T}}) (nu : nat) :
  @X6MatchingLegacy.x6_matching_number T E nu <->
  @Hypergraph.conjectures.X6.x6_matching_number T E nu.
Proof. exact: iff_refl. Qed.

Lemma x6_no_k_matching_compat (T : finType) (E : {set {set T}}) (k : nat) :
  @X6MatchingLegacy.x6_no_k_matching T E k <->
  @Hypergraph.conjectures.X6.x6_no_k_matching T E k.
Proof. exact: iff_refl. Qed.

Lemma x6_extremal_no_k_matching_compat (n r k m : nat) :
  @X6MatchingLegacy.x6_extremal_no_k_matching n r k m <->
  @Hypergraph.conjectures.X6.x6_extremal_no_k_matching n r k m.
Proof. exact: iff_refl. Qed.

Lemma rysers_statement_compat :
  U12MatchingLegacy.rysers_statement <->
  Hypergraph.conjectures.U12.rysers_statement.
Proof. exact: iff_refl. Qed.

Lemma lovasz_r_partite_matching_deletion_statement_compat :
  X6MatchingLegacy.lovasz_r_partite_matching_deletion_statement <->
  Hypergraph.conjectures.X6.lovasz_r_partite_matching_deletion_statement.
Proof. exact: iff_refl. Qed.

Lemma r_partite_matching_deletion_tradeoff_statement_compat :
  X6MatchingLegacy.r_partite_matching_deletion_tradeoff_statement <->
  Hypergraph.conjectures.X6.r_partite_matching_deletion_tradeoff_statement.
Proof. exact: iff_refl. Qed.

Lemma erdos_matching_extremal_formula_statement_compat :
  X6MatchingLegacy.erdos_matching_extremal_formula_statement <->
  Hypergraph.conjectures.X6.erdos_matching_extremal_formula_statement.
Proof. exact: iff_refl. Qed.

Lemma regular_tripartite_hypergraph_matching_lower_bound_statement_compat :
  X73MatchingLegacy.regular_tripartite_hypergraph_matching_lower_bound_statement <->
  Hypergraph.conjectures.X73.regular_tripartite_hypergraph_matching_lower_bound_statement.
Proof. exact: iff_refl. Qed.

Lemma x6_extremal_no_k_matching_original_compat (n r k m : nat) :
  @X6MatchingOriginal.x6_extremal_no_k_matching n r k m <->
  @Hypergraph.conjectures.X6.x6_extremal_no_k_matching n r k m.
Proof. exact: iff_refl. Qed.

Lemma rysers_statement_original_compat :
  U12MatchingOriginal.rysers_statement <->
  Hypergraph.conjectures.U12.rysers_statement.
Proof. exact: iff_refl. Qed.

Lemma lovasz_r_partite_matching_deletion_statement_original_compat :
  X6MatchingOriginal.lovasz_r_partite_matching_deletion_statement <->
  Hypergraph.conjectures.X6.lovasz_r_partite_matching_deletion_statement.
Proof. exact: iff_refl. Qed.

Lemma r_partite_matching_deletion_tradeoff_statement_original_compat :
  X6MatchingOriginal.r_partite_matching_deletion_tradeoff_statement <->
  Hypergraph.conjectures.X6.r_partite_matching_deletion_tradeoff_statement.
Proof. exact: iff_refl. Qed.

Lemma erdos_matching_extremal_formula_statement_original_compat :
  X6MatchingOriginal.erdos_matching_extremal_formula_statement <->
  Hypergraph.conjectures.X6.erdos_matching_extremal_formula_statement.
Proof. exact: iff_refl. Qed.

Lemma regular_tripartite_hypergraph_matching_lower_bound_statement_original_compat :
  X73MatchingOriginal.regular_tripartite_hypergraph_matching_lower_bound_statement <->
  Hypergraph.conjectures.X73.regular_tripartite_hypergraph_matching_lower_bound_statement.
Proof. exact: iff_refl. Qed.
