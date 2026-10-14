(** * Reconstruction.migration.kelly_public_boundary — certificates of kelly's public boundary (D2)

    Since D2, Reconstruction.foundations.kelly imports no conjecture module: its deck vocabulary is
    Reconstruction.foundations.decks (D1), its edge-deleted card is GTBase.common's [del_edge_set G [set e]] (A4), and
    its line graph is GTBase.simple_line_graphs's [simple_line_graph] (A25), written [sline_graph] through a kelly-local
    parsing-only abbreviation.  U11's [same_deck], [same_edge_deck], [vdel_card], [sdel_edge] and [sline_graph] are
    transparent aliases of exactly these, so nothing changes in meaning; this file proves it in the kernel against the
    PRE-D2 types, written below with FULLY QUALIFIED U11 names exactly as kelly's declarations had them before D2
    (baseline: the deletion-decks candidate 546e7121).
    - [pre_d2_whitney_line_inversion_premise] is the pre-D2 premise (byte-identical text in kelly, with the U11
      provider of [same_edge_deck] and [sline_graph] spelled out); [whitney_line_inversion_premise_pre_d2] proves it
      EQUAL to the live premise.
    - For each of kelly's 33 declarations, [pre_d2_<name>_type] is its complete pre-D2 type (section variables
      discharged, all binders explicit), and [<name>_pre_d2] ascribes the live constant to it: the kernel checks that
      the live type converts to the old one.  13 of them were restated in kelly (the 11 over [del_edge_set] and the
      two Greenwell theorems, whose corpus-statement names are spelled out as the propositions they unfold to, every
      guard and the conditional reconstruction / Whitney hypotheses in place); the other 20 have unchanged text.
    The definitions here are certificates over pre-D2 types, placed at top level; they are not frozen copies of a
    migrated source and are not re-exported. *)

From GraphTheory Require Import preliminaries bij digraph sgraph.
From GTBase Require Import base common simple_line_graphs.
Require Reconstruction.conjectures.U11 Reconstruction.foundations.kelly Reconstruction.conjectures.implications_U11.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** The Whitney premise: the pre-D2 text with its U11 providers, equal to the live premise *)

Definition pre_d2_whitney_line_inversion_premise : Prop :=
  forall G H : sgraph, (4 <= #|E(G)|)%N -> Reconstruction.conjectures.U11.same_edge_deck G H ->
    inhabited (Reconstruction.conjectures.U11.sline_graph G ≃ Reconstruction.conjectures.U11.sline_graph H) ->
    inhabited (G ≃ H).

Lemma whitney_line_inversion_premise_pre_d2 :
  pre_d2_whitney_line_inversion_premise = Reconstruction.foundations.kelly.whitney_line_inversion_premise.
Proof. exact: erefl. Qed.

(** ** Complete pre-D2 types of kelly's 33 declarations, and the live constants ascribed to them *)

(** #1 [sdel_adjE] (restated over [del_edge_set]). *)
Definition pre_d2_sdel_adjE_type : Prop :=
  forall (G : sgraph) (e : {set G}) (x y : G),
    @edge_rel (@Reconstruction.conjectures.U11.sdel_edge G e) x y = (x -- y) && ([set x; y] != e).
Definition sdel_adjE_pre_d2 : pre_d2_sdel_adjE_type := @Reconstruction.foundations.kelly.sdel_adjE.

(** #2 [sline_adjE]. *)
Definition pre_d2_sline_adjE_type : Prop :=
  forall (G : sgraph) (a b : Reconstruction.conjectures.U11.sline_graph G),
    a -- b = (val a != val b) && (val a :&: val b != set0).
Definition sline_adjE_pre_d2 : pre_d2_sline_adjE_type := @Reconstruction.foundations.kelly.sline_adjE.

(** #3 [card_sline_graph]. *)
Definition pre_d2_card_sline_graph_type : Prop :=
  forall G : sgraph, #|Reconstruction.conjectures.U11.sline_graph G| = #|E(G)|.
Definition card_sline_graph_pre_d2 : pre_d2_card_sline_graph_type :=
  @Reconstruction.foundations.kelly.card_sline_graph.

(** #4 [in_edge_set_sdel] (restated). *)
Definition pre_d2_in_edge_set_sdel_type : Prop :=
  forall (G : sgraph) (e f : {set G}),
    (f \in E(@Reconstruction.conjectures.U11.sdel_edge G e)) = (f \in E(G)) && (f != e).
Definition in_edge_set_sdel_pre_d2 : pre_d2_in_edge_set_sdel_type :=
  @Reconstruction.foundations.kelly.in_edge_set_sdel.

(** #5 [edge_set_sdel] (restated). *)
Definition pre_d2_edge_set_sdel_type : Prop :=
  forall (G : sgraph) (e : {set G}), E(@Reconstruction.conjectures.U11.sdel_edge G e) = E(G) :\ e.
Definition edge_set_sdel_pre_d2 : pre_d2_edge_set_sdel_type := @Reconstruction.foundations.kelly.edge_set_sdel.

(** #6 [imsetI_inj] (never depended on U11). *)
Definition pre_d2_imsetI_inj_type : Prop :=
  forall (aT rT : finType) (f : aT -> rT),
    injective f -> forall A B : {set aT}, f @: (A :&: B) = f @: A :&: f @: B.
Definition imsetI_inj_pre_d2 : pre_d2_imsetI_inj_type := @Reconstruction.foundations.kelly.imsetI_inj.

(** #7–#16, Section [LineDiso] (variables [G H : sgraph], [h : diso G H]). *)
Definition pre_d2_diso_imset_edge_type : Prop :=
  forall (G H : sgraph) (h : diso G H) (f : {set G}), f \in E(G) -> h @: f \in E(H).
Definition diso_imset_edge_pre_d2 : pre_d2_diso_imset_edge_type :=
  @Reconstruction.foundations.kelly.diso_imset_edge.

Definition pre_d2_diso_imset_edge'_type : Prop :=
  forall (G H : sgraph) (h : diso G H) (f : {set H}), f \in E(H) -> h^-1 @: f \in E(G).
Definition diso_imset_edge'_pre_d2 : pre_d2_diso_imset_edge'_type :=
  @Reconstruction.foundations.kelly.diso_imset_edge'.

Definition pre_d2_imset_bijK_type : Prop :=
  forall (G H : sgraph) (h : diso G H) (A : {set G}), h^-1 @: (h @: A) = A.
Definition imset_bijK_pre_d2 : pre_d2_imset_bijK_type := @Reconstruction.foundations.kelly.imset_bijK.

Definition pre_d2_imset_bijK'_type : Prop :=
  forall (G H : sgraph) (h : diso G H) (A : {set H}), h @: (h^-1 @: A) = A.
Definition imset_bijK'_pre_d2 : pre_d2_imset_bijK'_type := @Reconstruction.foundations.kelly.imset_bijK'.

Definition pre_d2_sldf_type : Type :=
  forall (G H : sgraph) (h : diso G H),
    Reconstruction.conjectures.U11.sline_graph G -> Reconstruction.conjectures.U11.sline_graph H.
Definition sldf_pre_d2 : pre_d2_sldf_type := @Reconstruction.foundations.kelly.sldf.

Definition pre_d2_sldb_type : Type :=
  forall (G H : sgraph) (h : diso G H),
    Reconstruction.conjectures.U11.sline_graph H -> Reconstruction.conjectures.U11.sline_graph G.
Definition sldb_pre_d2 : pre_d2_sldb_type := @Reconstruction.foundations.kelly.sldb.

Definition pre_d2_sldfK_type : Prop :=
  forall (G H : sgraph) (h : diso G H),
    cancel (@Reconstruction.foundations.kelly.sldf G H h) (@Reconstruction.foundations.kelly.sldb G H h).
Definition sldfK_pre_d2 : pre_d2_sldfK_type := @Reconstruction.foundations.kelly.sldfK.

Definition pre_d2_sldbK_type : Prop :=
  forall (G H : sgraph) (h : diso G H),
    cancel (@Reconstruction.foundations.kelly.sldb G H h) (@Reconstruction.foundations.kelly.sldf G H h).
Definition sldbK_pre_d2 : pre_d2_sldbK_type := @Reconstruction.foundations.kelly.sldbK.

Definition pre_d2_sldf_mono_type : Prop :=
  forall (G H : sgraph) (h : diso G H),
    monomorphism_2 (@Reconstruction.foundations.kelly.sldf G H h)
      (fun a b : Reconstruction.conjectures.U11.sline_graph G => a -- b)
      (fun a b : Reconstruction.conjectures.U11.sline_graph H => a -- b).
Definition sldf_mono_pre_d2 : pre_d2_sldf_mono_type := @Reconstruction.foundations.kelly.sldf_mono.

Definition pre_d2_sline_diso_type : Type :=
  forall G H : sgraph,
    G ≃ H -> Reconstruction.conjectures.U11.sline_graph G ≃ Reconstruction.conjectures.U11.sline_graph H.
Definition sline_diso_pre_d2 : pre_d2_sline_diso_type := @Reconstruction.foundations.kelly.sline_diso.

(** #17–#27, Section [LineCard] (variables [G : sgraph], [e0 : sline_graph G]); #17–#23 and #27 restated. *)
Definition pre_d2_lcf_proof_type : Prop :=
  forall (G : sgraph) (e0 : Reconstruction.conjectures.U11.sline_graph G)
         (x : @Reconstruction.conjectures.U11.vdel_card (Reconstruction.conjectures.U11.sline_graph G) e0),
    val (val x) \in E(@Reconstruction.conjectures.U11.sdel_edge G (val e0)).
Definition lcf_proof_pre_d2 : pre_d2_lcf_proof_type := @Reconstruction.foundations.kelly.lcf_proof.

Definition pre_d2_lcf_type : Type :=
  forall (G : sgraph) (e0 : Reconstruction.conjectures.U11.sline_graph G),
    @Reconstruction.conjectures.U11.vdel_card (Reconstruction.conjectures.U11.sline_graph G) e0 ->
    Reconstruction.conjectures.U11.sline_graph (@Reconstruction.conjectures.U11.sdel_edge G (val e0)).
Definition lcf_pre_d2 : pre_d2_lcf_type := @Reconstruction.foundations.kelly.lcf.

Definition pre_d2_lcb_in_type : Prop :=
  forall (G : sgraph) (e0 : Reconstruction.conjectures.U11.sline_graph G)
         (f : Reconstruction.conjectures.U11.sline_graph (@Reconstruction.conjectures.U11.sdel_edge G (val e0))),
    ((val f : {set G}) \in E(G)) && ((val f : {set G}) != val e0).
Definition lcb_in_pre_d2 : pre_d2_lcb_in_type := @Reconstruction.foundations.kelly.lcb_in.

Definition pre_d2_lcb_proof1_type : Prop :=
  forall (G : sgraph) (e0 : Reconstruction.conjectures.U11.sline_graph G)
         (f : Reconstruction.conjectures.U11.sline_graph (@Reconstruction.conjectures.U11.sdel_edge G (val e0))),
    val f \in E(G).
Definition lcb_proof1_pre_d2 : pre_d2_lcb_proof1_type := @Reconstruction.foundations.kelly.lcb_proof1.

Definition pre_d2_lcb0_type : Type :=
  forall (G : sgraph) (e0 : Reconstruction.conjectures.U11.sline_graph G),
    Reconstruction.conjectures.U11.sline_graph (@Reconstruction.conjectures.U11.sdel_edge G (val e0)) ->
    Reconstruction.conjectures.U11.sline_graph G.
Definition lcb0_pre_d2 : pre_d2_lcb0_type := @Reconstruction.foundations.kelly.lcb0.

Definition pre_d2_lcb_proof2_type : Prop :=
  forall (G : sgraph) (e0 : Reconstruction.conjectures.U11.sline_graph G)
         (f : Reconstruction.conjectures.U11.sline_graph (@Reconstruction.conjectures.U11.sdel_edge G (val e0))),
    @Reconstruction.foundations.kelly.lcb0 G e0 f
      \in [set u : Reconstruction.conjectures.U11.sline_graph G | u != e0].
Definition lcb_proof2_pre_d2 : pre_d2_lcb_proof2_type := @Reconstruction.foundations.kelly.lcb_proof2.

Definition pre_d2_lcb_type : Type :=
  forall (G : sgraph) (e0 : Reconstruction.conjectures.U11.sline_graph G),
    Reconstruction.conjectures.U11.sline_graph (@Reconstruction.conjectures.U11.sdel_edge G (val e0)) ->
    @Reconstruction.conjectures.U11.vdel_card (Reconstruction.conjectures.U11.sline_graph G) e0.
Definition lcb_pre_d2 : pre_d2_lcb_type := @Reconstruction.foundations.kelly.lcb.

Definition pre_d2_lcfK_type : Prop :=
  forall (G : sgraph) (e0 : Reconstruction.conjectures.U11.sline_graph G),
    cancel (@Reconstruction.foundations.kelly.lcf G e0) (@Reconstruction.foundations.kelly.lcb G e0).
Definition lcfK_pre_d2 : pre_d2_lcfK_type := @Reconstruction.foundations.kelly.lcfK.

Definition pre_d2_lcbK_type : Prop :=
  forall (G : sgraph) (e0 : Reconstruction.conjectures.U11.sline_graph G),
    cancel (@Reconstruction.foundations.kelly.lcb G e0) (@Reconstruction.foundations.kelly.lcf G e0).
Definition lcbK_pre_d2 : pre_d2_lcbK_type := @Reconstruction.foundations.kelly.lcbK.

Definition pre_d2_lcf_mono_type : Prop :=
  forall (G : sgraph) (e0 : Reconstruction.conjectures.U11.sline_graph G),
    monomorphism_2 (@Reconstruction.foundations.kelly.lcf G e0)
      (fun x y : @Reconstruction.conjectures.U11.vdel_card (Reconstruction.conjectures.U11.sline_graph G) e0 => x -- y)
      (fun x y : Reconstruction.conjectures.U11.sline_graph (@Reconstruction.conjectures.U11.sdel_edge G (val e0)) => x -- y).
Definition lcf_mono_pre_d2 : pre_d2_lcf_mono_type := @Reconstruction.foundations.kelly.lcf_mono.

Definition pre_d2_vdel_card_sline_type : Type :=
  forall (G : sgraph) (e0 : Reconstruction.conjectures.U11.sline_graph G),
    @Reconstruction.conjectures.U11.vdel_card (Reconstruction.conjectures.U11.sline_graph G) e0 ≃
    Reconstruction.conjectures.U11.sline_graph (@Reconstruction.conjectures.U11.sdel_edge G (val e0)).
Definition vdel_card_sline_pre_d2 : pre_d2_vdel_card_sline_type :=
  @Reconstruction.foundations.kelly.vdel_card_sline.

(** #28–#30. *)
Definition pre_d2_same_edge_deck_line_type : Prop :=
  forall G H : sgraph,
    Reconstruction.conjectures.U11.same_edge_deck G H ->
    Reconstruction.conjectures.U11.same_deck
      (Reconstruction.conjectures.U11.sline_graph G) (Reconstruction.conjectures.U11.sline_graph H).
Definition same_edge_deck_line_pre_d2 : pre_d2_same_edge_deck_line_type :=
  @Reconstruction.foundations.kelly.same_edge_deck_line.

Definition pre_d2_same_edge_deck_card_edge_type : Prop :=
  forall G H : sgraph, Reconstruction.conjectures.U11.same_edge_deck G H -> #|E(G)| = #|E(H)|.
Definition same_edge_deck_card_edge_pre_d2 : pre_d2_same_edge_deck_card_edge_type :=
  @Reconstruction.foundations.kelly.same_edge_deck_card_edge.

Definition pre_d2_same_edge_deck_card_vertex_type : Prop :=
  forall G H : sgraph, (0 < #|E(G)|)%N -> Reconstruction.conjectures.U11.same_edge_deck G H -> #|G| = #|H|.
Definition same_edge_deck_card_vertex_pre_d2 : pre_d2_same_edge_deck_card_vertex_type :=
  @Reconstruction.foundations.kelly.same_edge_deck_card_vertex.

(** #31 [reconstruction_line_diso] (restated: the corpus statement name spelled out as the proposition it unfolds to). *)
Definition pre_d2_reconstruction_line_diso_type : Prop :=
  Reconstruction.conjectures.U11.reconstruction_statement ->
  forall G H : sgraph, (3 <= #|E(G)|)%N -> Reconstruction.conjectures.U11.same_edge_deck G H ->
    inhabited (Reconstruction.conjectures.U11.sline_graph G ≃ Reconstruction.conjectures.U11.sline_graph H).
Definition reconstruction_line_diso_pre_d2 : pre_d2_reconstruction_line_diso_type :=
  @Reconstruction.foundations.kelly.reconstruction_line_diso.

(** #32 [whitney_line_inversion_premise]: a Prop, the same constant; its type and value. *)
Definition pre_d2_whitney_line_inversion_premise_type : Type := Prop.
Definition whitney_line_inversion_premise_value_pre_d2 : pre_d2_whitney_line_inversion_premise_type :=
  Reconstruction.foundations.kelly.whitney_line_inversion_premise.

(** #33 [whitney_reconstruction_edge_reconstruction] (restated likewise; still conditional on both hypotheses). *)
Definition pre_d2_whitney_reconstruction_edge_reconstruction_type : Prop :=
  pre_d2_whitney_line_inversion_premise ->
  Reconstruction.conjectures.U11.reconstruction_statement ->
  Reconstruction.conjectures.U11.edge_reconstruction_statement.
Definition whitney_reconstruction_edge_reconstruction_pre_d2 :
  pre_d2_whitney_reconstruction_edge_reconstruction_type :=
  @Reconstruction.foundations.kelly.whitney_reconstruction_edge_reconstruction.

(** The downstream consumer keeps its exact pre-D2 statement: Greenwell's implication over the non-corpus external
    statement, the corpus [reconstruction_statement] and [edge_reconstruction_statement]. *)
Definition pre_d2_reconstruction_implies_edge_reconstruction_type : Prop :=
  Reconstruction.conjectures.implications_U11.external_whitney_line_inversion_statement ->
  Reconstruction.conjectures.U11.reconstruction_statement ->
  Reconstruction.conjectures.U11.edge_reconstruction_statement.
Definition reconstruction_implies_edge_reconstruction_pre_d2 :
  pre_d2_reconstruction_implies_edge_reconstruction_type :=
  @Reconstruction.conjectures.implications_U11.reconstruction_implies_edge_reconstruction.

Print Assumptions whitney_line_inversion_premise_pre_d2.
Print Assumptions sdel_adjE_pre_d2.
Print Assumptions in_edge_set_sdel_pre_d2.
Print Assumptions edge_set_sdel_pre_d2.
Print Assumptions lcf_proof_pre_d2.
Print Assumptions lcf_pre_d2.
Print Assumptions lcb_in_pre_d2.
Print Assumptions lcb_proof1_pre_d2.
Print Assumptions lcb0_pre_d2.
Print Assumptions lcb_proof2_pre_d2.
Print Assumptions lcb_pre_d2.
Print Assumptions vdel_card_sline_pre_d2.
Print Assumptions reconstruction_line_diso_pre_d2.
Print Assumptions whitney_reconstruction_edge_reconstruction_pre_d2.
Print Assumptions reconstruction_implies_edge_reconstruction_pre_d2.
