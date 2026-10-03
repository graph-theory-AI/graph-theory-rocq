(** * Digraph.migration.degree_balance — frozen directed Eulerian (degree-balance) helpers of X221,
    colouring_variants and two_extremal (library migration B16, axiom-free replacement of the rejected 6dba7ed)

    Family [degree-balance] (meta/library_primitives/degree-balance.json).  [Legacy] freezes,
    verbatim as they stood at the B16 baseline 2981122, the directed "Eulerian" helpers migrated here:
    X221's [x221_eulerian] ([forall v, outdeg v = indeg v] over [classic_core.indeg]),
    colouring_variants' Boolean [eulerian] ([[forall v, indeg v == outdeg v]] over its file-local
    in-degree, frozen as [cv_eulerian]) and two_extremal's [Eulerian] ([forall v, indeg v = outdeg v]
    over [classic_core.indeg]).  Each in-degree is qualified so that the frozen bodies resolve exactly
    as their sources did; all unfold to the comprehension [#|[set u | u --> v]|], the public
    [Digraph.foundations.degree_balance.indeg].  The live helpers now unfold to [balanced D] (X221,
    two_extremal) and [balancedb D] (colouring_variants): colouring_variants and two_extremal convert,
    X221 is the reversed equation, certified by the proved [balanced_revE].  No connectivity,
    looplessness, inhabitance or tour premise is added.

    [X221Legacy] freezes the chain [eulerian_avoidable] and the corpus row on the orientations of
    the 4-cycle; [ColouringVariantsLegacy] the corpus row on majority 3-colourings of Eulerian
    digraphs; [TwoExtremalLegacy] the complete derived row [H6_no_full_cover] (every guard in its
    order); [TwoExtremalHajosLegacy] the Section-parametric constraint [realises_Eulerian] (same
    [Variable realises], so the discharged type takes the relation explicitly); [TwoExtremalGlueLegacy],
    [GlueEulSubtypeLegacy] and [GeneralisedWheelLegacy] the three concrete realisation relations
    [realises_W], [realises_E], [realises_gw] over the frozen helper, and the two whole non-selected
    Conjecture 9.2 encodings [conj_9_2_glued], [conj_9_2_glued_e] over their frozen relations
    ([conj_9_2_concrete] and [in_H2_concrete] are unchanged parameterised public helpers).
    reals_growth's [eulerian] and its two non-corpus EC-log rows are NOT migrated: the file and its
    grounding stay byte-identical to the baseline, and the registry classifies them as a deferred
    legacy-axiom defect (their statements inherit four classical-reals axioms).  No migration snapshot
    referenced these declarations, so per-row copies are complete.  Hashes and substitutions:
    meta/migration_reports/degree_balance.md. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_fingroup all_algebra.
From Digraph Require Import prelude interop_graph_theory digraph oriented tournament.
From Digraph Require Import dipath order strong classic_core dichromatic omegabar.
From Digraph Require Import heroes heroes_dichotomy unvd twinwidth twinwidth_ordered.
From Digraph Require Import two_extremal two_extremal_hajos two_extremal_glue generalised_wheel.
From Digraph Require Import glue_eul_subtype chi_bounded sad.
From GTBase Require Import asymptotics.
From Digraph.foundations Require Import degree_balance.
From Digraph.conjectures Require Import X221 colouring_variants.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module Legacy.

Definition x221_eulerian (D : diGraphType) : Prop :=
  forall v : D, outdeg v = classic_core.indeg v.

Definition cv_eulerian (D : diGraphType) : bool :=
  [forall v : D, colouring_variants.indeg v == outdeg v].

Definition Eulerian (D : diGraphType) : Prop :=
  forall v : D, classic_core.indeg v = outdeg v.

End Legacy.

Module X221Legacy.

Definition eulerian_avoidable (F : diGraphType) : Prop :=
  exists d : nat -> nat,
    forall (k : nat) (D : diGraphType),
      Legacy.x221_eulerian D -> (forall v : D, (d k <= outdeg v)%N) ->
      exists f : D -> {set D},
        (forall v : outsel f, (k <= outdeg v)%N)
        /\ ~ contains_subdigraph F (outsel f).

Definition orientation_C4_eulerian_avoidable_statement : Prop :=
  forall b : 'Z_4 -> bool, eulerian_avoidable (x221_c4or b).

End X221Legacy.

Module ColouringVariantsLegacy.

Definition majority_3col_eulerian_statement : Prop :=
  forall D : diGraphType, Legacy.cv_eulerian D ->
    exists col : D -> 'I_3, majority_col col.

End ColouringVariantsLegacy.

Module TwoExtremalLegacy.

Definition H6_no_full_cover : Prop :=
  forall (D : diGraphType) (llD : loopless D),
    (0 < #|D|)%N -> strongb D -> Legacy.Eulerian D ->
    arc_conn D = 2 ->
    three_connected_sg (underlyingG llD) ->
    ~ connected [set: digonG llD] ->
    dicolorableb D 2.

End TwoExtremalLegacy.

Module TwoExtremalHajosLegacy.

Section RealisesConstraints.
Variable realises : ptree -> diGraphType -> Prop.

Definition realises_Eulerian : Prop :=
  forall (t : ptree) (D : diGraphType), realises t D -> Legacy.Eulerian D.

End RealisesConstraints.

End TwoExtremalHajosLegacy.

Module TwoExtremalGlueLegacy.

Definition realises_W (t : ptree) (D : diGraphType) : Prop :=
  exists llD : loopless D,
    [/\ (forall u v : D, ~~ ((u --> v) && (v --> u))),
        Legacy.Eulerian D
      & is_forest [set: digonG llD]].

Definition conj_9_2_glued : Prop := conj_9_2_concrete TwoExtremalGlueLegacy.realises_W.

End TwoExtremalGlueLegacy.

Module GlueEulSubtypeLegacy.

Definition realises_E (t : ptree) (D : diGraphType) : Prop :=
  exists llD : loopless D,
    [/\ (forall u v : D, ~~ ((u --> v) && (v --> u))),
        Legacy.Eulerian D
      & is_forest [set: digonG llD]].

Definition conj_9_2_glued_e : Prop := conj_9_2_concrete GlueEulSubtypeLegacy.realises_E.

End GlueEulSubtypeLegacy.

Module GeneralisedWheelLegacy.

Definition realises_gw (t : ptree) (D : diGraphType) : Prop :=
  [/\ loopless D,
      Legacy.Eulerian D
    & forall llD : loopless D, is_forest [set: digonG llD]].

End GeneralisedWheelLegacy.

(** ** Certificates *)

(** The reversed equation (X221): the proved view [balanced_revE], not a conversion. *)
Lemma x221_eulerian_compat (D : diGraphType) : Legacy.x221_eulerian D <-> x221_eulerian D.
Proof. exact: balanced_revE. Qed.

(** The Boolean form (colouring_variants): the body of [balancedb], by conversion. *)
Lemma cv_eulerian_compat (D : diGraphType) :
  Legacy.cv_eulerian D = Digraph.conjectures.colouring_variants.eulerian D.
Proof. by []. Qed.

(** The uppercase helper (two_extremal): the equation of [balanced] itself, by conversion
    ([classic_core.indeg v = #|Nin v|] unfolds to the public [indeg v]). *)
Lemma Eulerian_compat (D : diGraphType) :
  Legacy.Eulerian D <-> Digraph.conjectures.two_extremal.Eulerian D.
Proof. exact: iff_refl. Qed.

Lemma x221_eulerian_avoidable_compat (F : diGraphType) :
  X221Legacy.eulerian_avoidable F <-> x221_eulerian_avoidable F.
Proof.
split=> -[d h]; exists d => k D eD dk; apply: (h k D) => //; move: eD; exact/x221_eulerian_compat.
Qed.

(** arxiv:2510.11311#04 (unchanged). *)
Lemma orientation_C4_eulerian_avoidable_statement_compat :
  X221Legacy.orientation_C4_eulerian_avoidable_statement <-> orientation_C4_eulerian_avoidable_statement.
Proof. by split=> h b; apply/x221_eulerian_avoidable_compat. Qed.

(** arxiv:1608.03040#04 (unchanged). *)
Lemma majority_3col_eulerian_statement_compat :
  ColouringVariantsLegacy.majority_3col_eulerian_statement <-> majority_3col_eulerian_statement.
Proof. exact: iff_refl. Qed.

(** derived:drv_twoext_h6 (unchanged): the complete row, every guard in its order. *)
Lemma H6_no_full_cover_compat :
  TwoExtremalLegacy.H6_no_full_cover <-> Digraph.conjectures.two_extremal.H6_no_full_cover.
Proof. exact: iff_refl. Qed.

(** The Section-parametric constraint, at every realisation relation. *)
Lemma realises_Eulerian_compat (realises : ptree -> diGraphType -> Prop) :
  TwoExtremalHajosLegacy.realises_Eulerian realises <->
  Digraph.conjectures.two_extremal_hajos.realises_Eulerian realises.
Proof. exact: iff_refl. Qed.

(** The three concrete realisation relations, at every tree and digraph. *)
Lemma realises_W_compat (t : ptree) (D : diGraphType) :
  TwoExtremalGlueLegacy.realises_W t D <-> Digraph.conjectures.two_extremal_glue.realises_W t D.
Proof. exact: iff_refl. Qed.

Lemma realises_E_compat (t : ptree) (D : diGraphType) :
  GlueEulSubtypeLegacy.realises_E t D <-> Digraph.conjectures.glue_eul_subtype.realises_E t D.
Proof. exact: iff_refl. Qed.

Lemma realises_gw_compat (t : ptree) (D : diGraphType) :
  GeneralisedWheelLegacy.realises_gw t D <-> Digraph.conjectures.generalised_wheel.realises_gw t D.
Proof. exact: iff_refl. Qed.

(** The two whole non-selected Conjecture 9.2 encodings (no manifest row), complete. *)
Lemma conj_9_2_glued_compat :
  TwoExtremalGlueLegacy.conj_9_2_glued <-> Digraph.conjectures.two_extremal_glue.conj_9_2_glued.
Proof. exact: iff_refl. Qed.

Lemma conj_9_2_glued_e_compat :
  GlueEulSubtypeLegacy.conj_9_2_glued_e <-> Digraph.conjectures.glue_eul_subtype.conj_9_2_glued_e.
Proof. exact: iff_refl. Qed.

Print Assumptions x221_eulerian_compat.
Print Assumptions cv_eulerian_compat.
Print Assumptions Eulerian_compat.
Print Assumptions orientation_C4_eulerian_avoidable_statement_compat.
Print Assumptions majority_3col_eulerian_statement_compat.
Print Assumptions H6_no_full_cover_compat.
Print Assumptions realises_Eulerian_compat.
Print Assumptions realises_W_compat.
Print Assumptions realises_E_compat.
Print Assumptions realises_gw_compat.
Print Assumptions conj_9_2_glued_compat.
Print Assumptions conj_9_2_glued_e_compat.
