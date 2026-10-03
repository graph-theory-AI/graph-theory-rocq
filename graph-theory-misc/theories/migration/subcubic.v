(** A14 subcubic (misc): the frozen X14 pointwise and X114 maximum-degree subcubic bounds, X102's multiclaw and
    line-graph chains, the three rows and their complete rows.  Baseline, hashes and exact substitutions are recorded in
    meta/migration_reports/subcubic.spec.json.
    - [Legacy]: X14's pointwise bound converts to [GTBase.base.subcubic]; X114's [Delta H <= 3] equals it by the
      unconditional finite-maximum bridge [subcubicP] (the empty graph included).
    - [X14Legacy], [X114Legacy], [X102Legacy]: the rows (and X102's two chains) over the frozen bounds; every other
      helper stays live there.
    - [X14Original], [X114Original], [X102Original]: the complete rows.  X14 composes C1's frozen pre-M1 matching;
      X114 composes B3's frozen induced-subdivision problem; X102 composes C13's complete tree-alpha class (over A1's
      frozen induced-freeness) and M1's frozen raw line graph with freshly frozen multiclaw and line-graph chains.
      Earlier families' modules are aliased, not imported; each bridge reuses the earlier certificate. *)
From Corelib Require Import Setoid Morphisms.
From GTBase Require Import base.
From GTMisc.conjectures Require Import X14 X114 X102.
From GTMisc.migration Require matching consecutive_in_path simple_edges bag_decompositions.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Earlier families' certificate modules, aliased without Import: their module names coincide
    with this file's. *)
Module C1 := GTMisc.migration.matching.
Module B3 := GTMisc.migration.consecutive_in_path.
Module M1 := GTMisc.migration.simple_edges.
Module C13 := GTMisc.migration.bag_decompositions.

Module Legacy.

Definition x14_subcubic (G : sgraph) : Prop :=
  forall v : G, #|N(v)| <= 3.

Definition x114_subcubic (H : sgraph) : Prop := Delta H <= 3.

End Legacy.

Module X14Legacy.

Definition subcubic_matching_lower_bound_statement : Prop :=
  forall G : sgraph,
    0 < #|G| ->
    Legacy.x14_subcubic G ->
    exists M : {set {set G}},
      @x14_matching G M /\
      9 * #|M| >= 3 * #|G| + x14_degree_two_count G.

End X14Legacy.

Module X114Legacy.

Definition subcubic_induced_subdivision_np_complete_statement : Prop :=
  exists H : sgraph,
    Legacy.x114_subcubic H /\ x114_np_complete (x114_hisc_problem H).

End X114Legacy.

Module X102Legacy.

Definition x102_subdivided_multiclaw (G : sgraph) : Prop :=
  is_forest [set: G] /\
  Legacy.x14_subcubic G /\
  forall S : {set G},
    connected S ->
    #|[set v in S | 2 < #|N(v) :&: S|]| <= 1.

Definition x102_line_graph_of_subdivided_multiclaw (G : sgraph) : Prop :=
  exists H : sgraph, X102Legacy.x102_subdivided_multiclaw H /\ x102_line_graph_of H G.

Definition bounded_tree_independence_forbidden_family_statement : Prop :=
  forall (I : finType) (F : I -> sgraph),
    x102_free_class_tree_alpha_bounded F <->
    exists i1 i2 i3 : I,
      x102_complete_bipartite_graph (F i1) /\
      X102Legacy.x102_subdivided_multiclaw (F i2) /\
      X102Legacy.x102_line_graph_of_subdivided_multiclaw (F i3).

End X102Legacy.

Module X14Original.

Definition subcubic_matching_lower_bound_statement : Prop :=
  forall G : sgraph,
    0 < #|G| ->
    Legacy.x14_subcubic G ->
    exists M : {set {set G}},
      @C1.Legacy.x14_matching G M /\
      9 * #|M| >= 3 * #|G| + x14_degree_two_count G.

End X14Original.

Module X114Original.

Definition subcubic_induced_subdivision_np_complete_statement : Prop :=
  exists H : sgraph,
    Legacy.x114_subcubic H /\ x114_np_complete (B3.X114Legacy.hisc_problem H).

End X114Original.

Module X102Original.

Definition x102_subdivided_multiclaw (G : sgraph) : Prop :=
  is_forest [set: G] /\
  Legacy.x14_subcubic G /\
  forall S : {set G},
    connected S ->
    #|[set v in S | 2 < #|N(v) :&: S|]| <= 1.

Definition x102_line_graph_of_subdivided_multiclaw (G : sgraph) : Prop :=
  exists H : sgraph, X102Original.x102_subdivided_multiclaw H /\ M1.X102Legacy.line_graph_of H G.

Definition bounded_tree_independence_forbidden_family_statement : Prop :=
  forall (I : finType) (F : I -> sgraph),
    C13.X102Original.x102_free_class_tree_alpha_bounded F <->
    exists i1 i2 i3 : I,
      x102_complete_bipartite_graph (F i1) /\
      X102Original.x102_subdivided_multiclaw (F i2) /\
      X102Original.x102_line_graph_of_subdivided_multiclaw (F i3).

End X102Original.

Lemma x14_subcubic_compat (G : sgraph) :
  Legacy.x14_subcubic G <->
  x14_subcubic G.
Proof. exact: iff_refl. Qed.

(** Not a conversion: the maximum-degree bound against the pointwise one ([subcubicP], unconditional,
    including the empty graph). *)
Lemma x114_subcubic_compat (H : sgraph) :
  Legacy.x114_subcubic H <->
  x114_subcubic H.
Proof. exact: (iff_sym (subcubicP H)). Qed.

Lemma subcubic_matching_lower_bound_statement_compat :
  X14Legacy.subcubic_matching_lower_bound_statement <->
  subcubic_matching_lower_bound_statement.
Proof. exact: iff_refl. Qed.

Lemma subcubic_induced_subdivision_np_complete_statement_compat :
  X114Legacy.subcubic_induced_subdivision_np_complete_statement <->
  subcubic_induced_subdivision_np_complete_statement.
Proof. rewrite /X114Legacy.subcubic_induced_subdivision_np_complete_statement /subcubic_induced_subdivision_np_complete_statement; setoid_rewrite x114_subcubic_compat; reflexivity. Qed.

Lemma x102_subdivided_multiclaw_compat (G : sgraph) :
  X102Legacy.x102_subdivided_multiclaw G <->
  x102_subdivided_multiclaw G.
Proof. exact: iff_refl. Qed.

Lemma x102_line_graph_of_subdivided_multiclaw_compat (G : sgraph) :
  X102Legacy.x102_line_graph_of_subdivided_multiclaw G <->
  x102_line_graph_of_subdivided_multiclaw G.
Proof. exact: iff_refl. Qed.

Lemma bounded_tree_independence_forbidden_family_statement_compat :
  X102Legacy.bounded_tree_independence_forbidden_family_statement <->
  bounded_tree_independence_forbidden_family_statement.
Proof. exact: iff_refl. Qed.

Lemma subcubic_matching_lower_bound_statement_original_compat :
  X14Original.subcubic_matching_lower_bound_statement <->
  subcubic_matching_lower_bound_statement.
Proof. exact: C1.subcubic_matching_lower_bound_statement_compat. Qed.

Lemma subcubic_induced_subdivision_np_complete_statement_original_compat :
  X114Original.subcubic_induced_subdivision_np_complete_statement <->
  subcubic_induced_subdivision_np_complete_statement.
Proof. rewrite /X114Original.subcubic_induced_subdivision_np_complete_statement; setoid_rewrite x114_subcubic_compat; exact: B3.subcubic_induced_subdivision_np_complete_statement_compat. Qed.

Lemma x102_subdivided_multiclaw_original_compat (G : sgraph) :
  X102Original.x102_subdivided_multiclaw G <->
  x102_subdivided_multiclaw G.
Proof. exact: iff_refl. Qed.

Lemma x102_line_graph_of_subdivided_multiclaw_original_compat (G : sgraph) :
  X102Original.x102_line_graph_of_subdivided_multiclaw G <->
  x102_line_graph_of_subdivided_multiclaw G.
Proof. exact: M1.x102_line_graph_of_subdivided_multiclaw_compat. Qed.

Lemma bounded_tree_independence_forbidden_family_statement_original_compat :
  X102Original.bounded_tree_independence_forbidden_family_statement <->
  bounded_tree_independence_forbidden_family_statement.
Proof. exact: C13.bounded_tree_independence_forbidden_family_statement_original_compat. Qed.
