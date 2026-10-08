(** * Reconstruction.migration.deletion_decks — deletion-decks certificates (D1)

    Family [deletion-decks] (meta/library_primitives/deletion-decks.json).  U11's five deck definitions [vdel_card],
    [same_deck], [reconstructible], [same_edge_deck] and [edge_reconstructible] are, since this migration, transparent
    aliases of Reconstruction.foundations.decks (the same bodies; the edge card [sdel_edge G e] is A4's alias of
    [del_edge_set G [set e]], the decks card).  Baseline: the accepted coordinator 3bdfdae (tree ade432af), which
    contains A4 (5ec0f33) and A25 with the C19 composition (ff7bd3b).

    - [Legacy] freezes the five verbatim at the baseline, references between frozen copies qualified [Legacy.];
      [Legacy.same_edge_deck] applies the live [sdel_edge] (A4's alias) as the baseline text does.
    - [U11Legacy] freezes the two corpus rows: [reconstruction_statement] (three-vertex guards on BOTH graphs, kept
      although the bijection forces equal orders) and [edge_reconstruction_statement] (the four-edge guard on [G] only).
    - [KellyLegacy] / [ImplicationsU11Legacy] freeze Kelly's Whitney inversion premise and the non-corpus external
      statement, both with the four-edge guard AND the same-edge-deck hypothesis; both stay explicit conditional
      premises, neither is proved; [sline_graph] is applied live (A25's alias).
    Every certificate below is a kernel conversion.

    Deepest Originals: the vertex row's chain ([induced], [bijective], [≃], all upstream) is unchanged since U11's
    creation 3b2638f and no earlier family froze it, so [U11Legacy.reconstruction_statement] is already its deepest
    original.  The edge row's is A4's raw [A4.U11Legacy.edge_reconstruction_statement] (9e03072), certified against
    the live row by A4's [edge_reconstruction_statement_compat]; the two Whitney rows' are A25's
    [A25.KellyOriginal] / [A25.ImplicationsU11Original] (A4's raw edge deck and A25's raw line graph), certified by
    A25's [*_original_compat]; they are restated here, unchanged, against the live (now aliased) rows.  The A4 and A25
    modules are aliased without Import; their files are not changed. *)

From GraphTheory Require Import bij.
From GTBase Require Import base simple_line_graphs.
From Reconstruction Require Import conjectures.U11 foundations.kelly conjectures.implications_U11.
From Reconstruction Require foundations.decks.
From Reconstruction.migration Require sdel_edge simple_line_graphs.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** A4's and A25's certificate modules, aliased without Import: their module names coincide with this file's. *)
Module A4 := Reconstruction.migration.sdel_edge.
Module A25 := Reconstruction.migration.simple_line_graphs.

Module Legacy.

Definition vdel_card (G : sgraph) (v : G) : sgraph := induced [set u : G | u != v].

Definition same_edge_deck (G H : sgraph) : Prop :=
  exists f : {e : {set G} | e \in E(G)} -> {e : {set H} | e \in E(H)},
    bijective f /\
    forall e : {e : {set G} | e \in E(G)},
      inhabited (@sdel_edge G (val e) ≃ @sdel_edge H (val (f e))).

Definition edge_reconstructible (G : sgraph) : Prop :=
  forall H : sgraph, Legacy.same_edge_deck G H -> inhabited (G ≃ H).

Definition same_deck (G H : sgraph) : Prop :=
  exists f : G -> H,
    bijective f /\
    forall v : G, inhabited (@Legacy.vdel_card G v ≃ @Legacy.vdel_card H (f v)).

Definition reconstructible (G : sgraph) : Prop :=
  forall H : sgraph, Legacy.same_deck G H -> inhabited (G ≃ H).

End Legacy.

Module U11Legacy.

Definition edge_reconstruction_statement : Prop :=
  forall G : sgraph, (4 <= #|E(G)|)%N -> Legacy.edge_reconstructible G.

Definition reconstruction_statement : Prop :=
  forall G H : sgraph,
    (3 <= #|G|)%N -> (3 <= #|H|)%N -> Legacy.same_deck G H -> inhabited (G ≃ H).

End U11Legacy.

Module KellyLegacy.

Definition whitney_line_inversion_premise : Prop :=
  forall G H : sgraph, (4 <= #|E(G)|)%N -> Legacy.same_edge_deck G H ->
    inhabited (sline_graph G ≃ sline_graph H) -> inhabited (G ≃ H).

End KellyLegacy.

Module ImplicationsU11Legacy.

Definition external_whitney_line_inversion_statement : Prop :=
  forall G H : sgraph, (4 <= #|E(G)|)%N -> Legacy.same_edge_deck G H ->
    inhabited (sline_graph G ≃ sline_graph H) -> inhabited (G ≃ H).

End ImplicationsU11Legacy.

(** ** Certificates: frozen = live, by conversion *)

Lemma vdel_card_compat (G : sgraph) (v : G) : Legacy.vdel_card v = vdel_card v.
Proof. by []. Qed.

Lemma same_deck_compat (G H : sgraph) : Legacy.same_deck G H <-> same_deck G H.
Proof. exact: iff_refl. Qed.

Lemma reconstructible_compat (G : sgraph) : Legacy.reconstructible G <-> reconstructible G.
Proof. exact: iff_refl. Qed.

Lemma same_edge_deck_compat (G H : sgraph) : Legacy.same_edge_deck G H <-> same_edge_deck G H.
Proof. exact: iff_refl. Qed.

Lemma edge_reconstructible_compat (G : sgraph) :
  Legacy.edge_reconstructible G <-> edge_reconstructible G.
Proof. exact: iff_refl. Qed.

(** opg:reconstruction_conjecture (open, unchanged). *)
Lemma reconstruction_statement_compat :
  U11Legacy.reconstruction_statement <-> reconstruction_statement.
Proof. exact: iff_refl. Qed.

(** opg:edge_reconstruction_conjecture (open, unchanged). *)
Lemma edge_reconstruction_statement_compat :
  U11Legacy.edge_reconstruction_statement <-> edge_reconstruction_statement.
Proof. exact: iff_refl. Qed.

Lemma whitney_line_inversion_premise_compat :
  KellyLegacy.whitney_line_inversion_premise <->
  Reconstruction.foundations.kelly.whitney_line_inversion_premise.
Proof. exact: iff_refl. Qed.

Lemma external_whitney_line_inversion_statement_compat :
  ImplicationsU11Legacy.external_whitney_line_inversion_statement <->
  Reconstruction.conjectures.implications_U11.external_whitney_line_inversion_statement.
Proof. exact: iff_refl. Qed.

(** ** Deepest Originals, through the providers' own certificates (unchanged files) *)

(** The edge row against A4's raw edge deck (9e03072). *)
Lemma edge_reconstruction_statement_original_compat :
  A4.U11Legacy.edge_reconstruction_statement <-> edge_reconstruction_statement.
Proof. exact: A4.edge_reconstruction_statement_compat. Qed.

(** The two Whitney rows against A4's raw edge deck and A25's raw line graph (9e03072). *)
Lemma whitney_line_inversion_premise_original_compat :
  A25.KellyOriginal.whitney_line_inversion_premise <->
  Reconstruction.foundations.kelly.whitney_line_inversion_premise.
Proof. exact: A25.whitney_line_inversion_premise_original_compat. Qed.

Lemma external_whitney_line_inversion_statement_original_compat :
  A25.ImplicationsU11Original.external_whitney_line_inversion_statement <->
  Reconstruction.conjectures.implications_U11.external_whitney_line_inversion_statement.
Proof. exact: A25.external_whitney_line_inversion_statement_original_compat. Qed.

(** ** The U11 names and the complete current rows in the canonical vocabulary *)

Lemma vdel_card_canonical (G : sgraph) (v : G) : vdel_card v = decks.vdel_card v.
Proof. by []. Qed.

Lemma same_deck_canonical (G H : sgraph) : same_deck G H <-> decks.same_deck G H.
Proof. exact: iff_refl. Qed.

Lemma reconstructible_canonical (G : sgraph) : reconstructible G <-> decks.reconstructible G.
Proof. exact: iff_refl. Qed.

Lemma same_edge_deck_canonical (G H : sgraph) : same_edge_deck G H <-> decks.same_edge_deck G H.
Proof. exact: iff_refl. Qed.

Lemma edge_reconstructible_canonical (G : sgraph) :
  edge_reconstructible G <-> decks.edge_reconstructible G.
Proof. exact: iff_refl. Qed.

Lemma reconstruction_statement_canonical :
  reconstruction_statement <->
  forall G H : sgraph,
    (3 <= #|G|)%N -> (3 <= #|H|)%N -> decks.same_deck G H -> inhabited (G ≃ H).
Proof. exact: iff_refl. Qed.

Lemma edge_reconstruction_statement_canonical :
  edge_reconstruction_statement <->
  forall G : sgraph, (4 <= #|E(G)|)%N -> decks.edge_reconstructible G.
Proof. exact: iff_refl. Qed.

(** The Whitney rows with the canonical decks and line graph ([simple_line_graph], A25's canonical). *)
Lemma whitney_line_inversion_premise_canonical :
  Reconstruction.foundations.kelly.whitney_line_inversion_premise <->
  forall G H : sgraph, (4 <= #|E(G)|)%N -> decks.same_edge_deck G H ->
    inhabited (simple_line_graph G ≃ simple_line_graph H) -> inhabited (G ≃ H).
Proof. exact: iff_refl. Qed.

Lemma external_whitney_line_inversion_statement_canonical :
  Reconstruction.conjectures.implications_U11.external_whitney_line_inversion_statement <->
  forall G H : sgraph, (4 <= #|E(G)|)%N -> decks.same_edge_deck G H ->
    inhabited (simple_line_graph G ≃ simple_line_graph H) -> inhabited (G ≃ H).
Proof. exact: iff_refl. Qed.

Print Assumptions vdel_card_compat.
Print Assumptions same_deck_compat.
Print Assumptions reconstructible_compat.
Print Assumptions same_edge_deck_compat.
Print Assumptions edge_reconstructible_compat.
Print Assumptions reconstruction_statement_compat.
Print Assumptions edge_reconstruction_statement_compat.
Print Assumptions whitney_line_inversion_premise_compat.
Print Assumptions external_whitney_line_inversion_statement_compat.
Print Assumptions edge_reconstruction_statement_original_compat.
Print Assumptions whitney_line_inversion_premise_original_compat.
Print Assumptions external_whitney_line_inversion_statement_original_compat.
Print Assumptions vdel_card_canonical.
Print Assumptions same_deck_canonical.
Print Assumptions reconstructible_canonical.
Print Assumptions same_edge_deck_canonical.
Print Assumptions edge_reconstructible_canonical.
Print Assumptions reconstruction_statement_canonical.
Print Assumptions edge_reconstruction_statement_canonical.
Print Assumptions whitney_line_inversion_premise_canonical.
Print Assumptions external_whitney_line_inversion_statement_canonical.
