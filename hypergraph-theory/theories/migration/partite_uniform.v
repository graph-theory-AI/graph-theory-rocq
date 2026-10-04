(** * D2: supplied-partition uniform hypergraphs, Hypergraph certificate

    Frozen at the D1 pin e53098e84635d8612e34e5d239fd13fe5afa9fb8 (mathematical baseline
    C25 3be65eed7084abfae36dee74f7117b598325bc4c); bindings in
    meta/migration_reports/partite_uniform.spec.json.
    - [PartiteLegacy]: U12's [r_partite_uniform], X6's [x6_r_partite_uniform] and the public
      Section-bound [hg_partite_uniform], verbatim.  The two local sources now unfold to the
      unchanged public [Hypergraph.foundations.hypergraph.hg_partite_uniform], with the same
      supplied map [part : T -> 'I_r] and family [E].
    - [<Phase>PartiteLegacy]: the six complete current rows (U12 Ryser, X6 Lovasz deletion and
      its trade-off, X72, X73, X225 #01), each in a module importing only the conjecture files
      its source imports.  These current copies keep unrelated live aliases: X73's A10
      regularity and X225's D1 uniformity/Turan maximum and A10 [hg_dmax].
    - [<Phase>PartiteOriginal]: the two complete A10+D1+D2 Originals, reached through the
      aliases [ID]/[UH] (no Import): X73 over the raw partite copy and A10's actual
      [ID.X73Legacy.hyperdegree_regular]; X225 #01 over the raw partite copy, D1's actual
      [UH.UniformLegacy.hg_uniform] and [UH.UniformLegacy.hg_turan], and A10's actual
      [ID.FoundationLegacy.dmax] (its opaque [degenerate_ex] witness is reused, not replaced).
    Older snapshots (A10 X73Legacy/X225Legacy, D1 X225UniformLegacy/X225UniformOriginal) stay
    as they are; the spec records them and points to these Originals. *)
From GTBase Require Import base.
Require Hypergraph.foundations.hypergraph.
Require Hypergraph.conjectures.U12 Hypergraph.conjectures.X6 Hypergraph.conjectures.X72.
Require Hypergraph.conjectures.X73 Hypergraph.conjectures.X225.
Require Hypergraph.migration.incidence_degree Hypergraph.migration.uniform_hypergraph.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module ID := Hypergraph.migration.incidence_degree.
Module UH := Hypergraph.migration.uniform_hypergraph.

Module PartiteLegacy.

Definition r_partite_uniform (T : finType) (r : nat) (part : T -> 'I_r)
  (E : {set {set T}}) : Prop :=
  forall e : {set T}, e \in E ->
    forall j : 'I_r, #|[set v in e | part v == j]| = 1.

Definition x6_r_partite_uniform
    (T : finType) (r : nat) (part : T -> 'I_r) (E : {set {set T}}) : Prop :=
  forall e : {set T}, e \in E ->
    forall j : 'I_r, #|[set v in e | part v == j]| = 1.

Section Hypergraph.
Variable T : finType.
Implicit Types (E : {set {set T}}) (e S : {set T}) (v : T).

Definition hg_partite_uniform (k : nat) (part : T -> 'I_k) E : Prop :=
  forall e, e \in E -> forall j : 'I_k, #|[set v in e | part v == j]| = 1.

End Hypergraph.

End PartiteLegacy.

Module U12PartiteLegacy.
Import Hypergraph.conjectures.U12.

Definition rysers_statement : Prop :=
  forall (r : nat) (T : finType) (part : T -> 'I_r) (E : {set {set T}})
         (nu tau : nat),
    1 < r ->
    PartiteLegacy.r_partite_uniform part E ->
    is_matching_number E nu ->
    is_cover_number E tau ->
    tau <= (r - 1) * nu.

End U12PartiteLegacy.

Module X6PartiteLegacy.
Import Hypergraph.conjectures.X6.

Definition lovasz_r_partite_matching_deletion_statement : Prop :=
  forall (r : nat) (T : finType) (part : T -> 'I_r) (E : {set {set T}})
         (nu : nat),
    1 < r ->
    E != set0 ->
    PartiteLegacy.x6_r_partite_uniform part E ->
    x6_matching_number E nu ->
    exists X : {set T}, #|X| = r - 1 /\
      exists nu' : nat,
        x6_matching_number (x6_delete_vertices E X) nu' /\ nu' < nu.

Definition r_partite_matching_deletion_tradeoff_statement : Prop :=
  forall (r : nat) (T : finType) (part : T -> 'I_r) (E : {set {set T}})
         (nu : nat),
    1 < r ->
    E != set0 ->
    PartiteLegacy.x6_r_partite_uniform part E ->
    x6_matching_number E nu ->
    exists (k : nat) (X : {set T}),
      1 <= k /\ k <= r - 1 /\
      #|X| = k * (r - 1) /\
      exists nu' : nat,
        x6_matching_number (x6_delete_vertices E X) nu' /\ nu' + k <= nu.

End X6PartiteLegacy.

Module X72PartiteLegacy.
Import Hypergraph.conjectures.X6 Hypergraph.conjectures.X72.

Definition ryser_intersecting_partite_cover_gap_statement : Prop :=
  exists K : nat,
    forall r : nat,
      1 <= r ->
      exists (T : finType) (part : T -> 'I_r) (E : {set {set T}}) (tau : nat),
        [/\ E != set0,
            @PartiteLegacy.x6_r_partite_uniform T r part E,
            x72_intersecting E,
            x72_transversal_number E tau
          & r <= tau + K].

End X72PartiteLegacy.

Module X73PartiteLegacy.
Import Hypergraph.conjectures.X6 Hypergraph.conjectures.X73.

Definition regular_tripartite_hypergraph_matching_lower_bound_statement : Prop :=
  forall (d n : nat) (T : finType) (part : T -> 'I_3) (E : {set {set T}}),
    1 <= d ->
    x73_balanced_tripartite part n ->
    @PartiteLegacy.x6_r_partite_uniform T 3 part E ->
    x73_regular E d ->
    exists M : {set {set T}},
      x6_matching M E /\ ((d.-1 * n) %/ d <= #|M|).

End X73PartiteLegacy.

Module X225PartiteLegacy.
Import Hypergraph.conjectures.X225.

Definition kpartite_hypergraph_turan_exponent_dmax_statement : Prop :=
  forall k : nat,
    2 <= k ->
    exists ck : nat,
      0 < ck /\
      forall (S : finType) (F : {set {set S}}) (part : S -> 'I_k),
        F != set0 ->
        hg_uniform F k ->
        PartiteLegacy.hg_partite_uniform part F ->
        exists K : nat,
          0 < K /\
          eventually (fun n =>
            (hg_turan F k n) ^ (hg_dmax F k) * n ^ ck <= K * n ^ (k * hg_dmax F k)).

End X225PartiteLegacy.

Module X73PartiteOriginal.
Import Hypergraph.conjectures.X6 Hypergraph.conjectures.X73.

Definition regular_tripartite_hypergraph_matching_lower_bound_statement : Prop :=
  forall (d n : nat) (T : finType) (part : T -> 'I_3) (E : {set {set T}}),
    1 <= d ->
    x73_balanced_tripartite part n ->
    @PartiteLegacy.x6_r_partite_uniform T 3 part E ->
    ID.X73Legacy.hyperdegree_regular E d ->
    exists M : {set {set T}},
      x6_matching M E /\ ((d.-1 * n) %/ d <= #|M|).

End X73PartiteOriginal.

Module X225PartiteOriginal.
Import Hypergraph.conjectures.X225.

Definition kpartite_hypergraph_turan_exponent_dmax_statement : Prop :=
  forall k : nat,
    2 <= k ->
    exists ck : nat,
      0 < ck /\
      forall (S : finType) (F : {set {set S}}) (part : S -> 'I_k),
        F != set0 ->
        UH.UniformLegacy.hg_uniform F k ->
        PartiteLegacy.hg_partite_uniform part F ->
        exists K : nat,
          0 < K /\
          eventually (fun n =>
            (UH.UniformLegacy.hg_turan F k n) ^ (ID.FoundationLegacy.dmax F k) * n ^ ck <=
              K * n ^ (k * ID.FoundationLegacy.dmax F k)).

End X225PartiteOriginal.

(** ** Sources: the raw copies convert to the live aliases of the unchanged public predicate *)

Lemma r_partite_uniform_compat (T : finType) (r : nat) (part : T -> 'I_r) (E : {set {set T}}) :
  @PartiteLegacy.r_partite_uniform T r part E <->
  @Hypergraph.conjectures.U12.r_partite_uniform T r part E.
Proof. exact: iff_refl. Qed.

Lemma x6_r_partite_uniform_compat (T : finType) (r : nat) (part : T -> 'I_r) (E : {set {set T}}) :
  @PartiteLegacy.x6_r_partite_uniform T r part E <->
  @Hypergraph.conjectures.X6.x6_r_partite_uniform T r part E.
Proof. exact: iff_refl. Qed.

Lemma hg_partite_uniform_compat (T : finType) (k : nat) (part : T -> 'I_k) (E : {set {set T}}) :
  @PartiteLegacy.hg_partite_uniform T k part E <->
  @Hypergraph.foundations.hypergraph.hg_partite_uniform T k part E.
Proof. exact: iff_refl. Qed.

(** ** The six complete current rows (unrelated live aliases kept, see the module headers) *)

Lemma rysers_statement_compat :
  U12PartiteLegacy.rysers_statement <->
  Hypergraph.conjectures.U12.rysers_statement.
Proof. exact: iff_refl. Qed.

Lemma lovasz_r_partite_matching_deletion_statement_compat :
  X6PartiteLegacy.lovasz_r_partite_matching_deletion_statement <->
  Hypergraph.conjectures.X6.lovasz_r_partite_matching_deletion_statement.
Proof. exact: iff_refl. Qed.

Lemma r_partite_matching_deletion_tradeoff_statement_compat :
  X6PartiteLegacy.r_partite_matching_deletion_tradeoff_statement <->
  Hypergraph.conjectures.X6.r_partite_matching_deletion_tradeoff_statement.
Proof. exact: iff_refl. Qed.

Lemma ryser_intersecting_partite_cover_gap_statement_compat :
  X72PartiteLegacy.ryser_intersecting_partite_cover_gap_statement <->
  Hypergraph.conjectures.X72.ryser_intersecting_partite_cover_gap_statement.
Proof. exact: iff_refl. Qed.

Lemma regular_tripartite_hypergraph_matching_lower_bound_statement_compat :
  X73PartiteLegacy.regular_tripartite_hypergraph_matching_lower_bound_statement <->
  Hypergraph.conjectures.X73.regular_tripartite_hypergraph_matching_lower_bound_statement.
Proof. exact: iff_refl. Qed.

Lemma kpartite_hypergraph_turan_exponent_dmax_statement_compat :
  X225PartiteLegacy.kpartite_hypergraph_turan_exponent_dmax_statement <->
  Hypergraph.conjectures.X225.kpartite_hypergraph_turan_exponent_dmax_statement.
Proof. exact: iff_refl. Qed.

(** ** The two complete A10+D1+D2 Originals.  Each converts to the earlier whole-row iff it extends
    (A10 X73; D1 X225 #01), whose proof is reused unchanged: the raw partite copy and the live
    alias unfold to the same body. *)

Lemma regular_tripartite_hypergraph_matching_lower_bound_statement_original_compat :
  X73PartiteOriginal.regular_tripartite_hypergraph_matching_lower_bound_statement <->
  Hypergraph.conjectures.X73.regular_tripartite_hypergraph_matching_lower_bound_statement.
Proof. exact: ID.regular_tripartite_hypergraph_matching_lower_bound_statement_compat. Qed.

Lemma kpartite_hypergraph_turan_exponent_dmax_statement_original_compat :
  X225PartiteOriginal.kpartite_hypergraph_turan_exponent_dmax_statement <->
  Hypergraph.conjectures.X225.kpartite_hypergraph_turan_exponent_dmax_statement.
Proof. exact: UH.kpartite_hypergraph_turan_exponent_dmax_statement_original_compat. Qed.
