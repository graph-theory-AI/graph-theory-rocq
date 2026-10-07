(** A25 simple line graphs (reconstruction): U11's iterable line operation -- Section [SLine], its relation, two
    constructor proofs and graph -- frozen at the A24 baseline 897a7d3 with the three complete Props over it, and the
    two complete Whitney Originals at A4's baseline 9e03072.  Baseline, hashes and exact substitutions are recorded in
    meta/migration_reports/simple_line_graphs.spec.json.
    - [Legacy], [ProofsLegacy], [GraphLegacy]: the Section in dependency order, each in a verbatim copy of its
      scaffolding [Variable G : sgraph], so the discharged arguments are the original's; references to earlier frozen
      names are module-qualified ([sline_rel] -> [(@Legacy.sline_rel G)], the same term once the Section is closed).
    - [U11Legacy]: Graham's tree-reconstruction row (both tree guards, equal orders of [iter i] for every [i : nat],
      zero included, then isomorphism).
    - [KellyLegacy], [ImplicationsU11Legacy]: Kelly's Whitney inversion premise and the explicitly non-corpus external
      statement, both with the four-edge guard and the same-edge-deck hypothesis; both stay explicit conditional
      premises, neither is proved.
    - [KellyOriginal], [ImplicationsU11Original] (texts at 9e03072): the same two Props over the frozen line
      construction and A4's frozen raw edge deck (its [sde_rel], two proofs, [sdel_edge] and [same_edge_deck]); A4's
      module is aliased, not imported.
    The frozen relation is convertible to GTBase.simple_line_graphs's; the frozen graph differs from
    [simple_line_graph] only in its opaque proof fields, so the two are related by the identity isomorphism, which
    [simple_line_graph_diso] propagates to every iterate. *)
From GraphTheory Require Import bij.
From GTBase Require Import base simple_line_graphs.
From Reconstruction Require Import conjectures.U11 foundations.kelly conjectures.implications_U11.
From Reconstruction.migration Require sdel_edge.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** A4's certificate module, aliased without Import: its module names coincide with this file's. *)
Module A4 := Reconstruction.migration.sdel_edge.

Module Legacy.

Section SLine.
Variable G : sgraph.
Definition sline_rel : rel {e : {set G} | e \in E(G)} :=
  fun e1 e2 => (val e1 != val e2) && (val e1 :&: val e2 != set0).
End SLine.

End Legacy.

Module ProofsLegacy.

Section SLine.
Variable G : sgraph.
Lemma sline_sym : symmetric (@Legacy.sline_rel G).
Proof. by move=> e1 e2; rewrite /Legacy.sline_rel eq_sym setIC. Qed.
Lemma sline_irrefl : irreflexive (@Legacy.sline_rel G).
Proof. by move=> e; rewrite /Legacy.sline_rel eqxx. Qed.
End SLine.

End ProofsLegacy.

Module GraphLegacy.

Section SLine.
Variable G : sgraph.
Definition sline_graph : sgraph := SGraph (@ProofsLegacy.sline_sym G) (@ProofsLegacy.sline_irrefl G).
End SLine.

End GraphLegacy.

Module U11Legacy.

Definition grahams_conjecture_on_tree_reconstruction_statement : Prop :=
  forall T1 T2 : sgraph,
    is_tree [set: T1] -> is_tree [set: T2] ->
    (forall i : nat, #|iter i GraphLegacy.sline_graph T1| = #|iter i GraphLegacy.sline_graph T2|) ->
    inhabited (T1 ≃ T2).

End U11Legacy.

Module KellyLegacy.

Definition whitney_line_inversion_premise : Prop :=
  forall G H : sgraph, (4 <= #|E(G)|)%N -> same_edge_deck G H ->
    inhabited (GraphLegacy.sline_graph G ≃ GraphLegacy.sline_graph H) -> inhabited (G ≃ H).

End KellyLegacy.

Module ImplicationsU11Legacy.

Definition external_whitney_line_inversion_statement : Prop :=
  forall G H : sgraph, (4 <= #|E(G)|)%N -> same_edge_deck G H ->
    inhabited (GraphLegacy.sline_graph G ≃ GraphLegacy.sline_graph H) -> inhabited (G ≃ H).

End ImplicationsU11Legacy.

Module KellyOriginal.

Definition whitney_line_inversion_premise : Prop :=
  forall G H : sgraph, (4 <= #|E(G)|)%N -> A4.U11Legacy.same_edge_deck G H ->
    inhabited (GraphLegacy.sline_graph G ≃ GraphLegacy.sline_graph H) -> inhabited (G ≃ H).

End KellyOriginal.

Module ImplicationsU11Original.

Definition external_whitney_line_inversion_statement : Prop :=
  forall G H : sgraph, (4 <= #|E(G)|)%N -> A4.U11Legacy.same_edge_deck G H ->
    inhabited (GraphLegacy.sline_graph G ≃ GraphLegacy.sline_graph H) -> inhabited (G ≃ H).

End ImplicationsU11Original.

(** The Section: the relation is the public one by conversion; the constructor proofs and the graphs are related by
    the identity isomorphism, never by an equation between proof fields. *)
Lemma sline_rel_compat (G : sgraph) (e f : {e : {set G} | e \in E(G)}) :
  @Legacy.sline_rel G e f = @Reconstruction.conjectures.U11.sline_rel G e f.
Proof.
by [].
Qed.

Lemma sline_proofs_compat (G : sgraph) :
  SGraph (@ProofsLegacy.sline_sym G) (@ProofsLegacy.sline_irrefl G) ≃ SGraph (@Reconstruction.conjectures.U11.sline_sym G) (@Reconstruction.conjectures.U11.sline_irrefl G).
Proof. by apply: eq_diso => e f. Qed.

Lemma sline_graph_compat (G : sgraph) :
  @edge_rel (GraphLegacy.sline_graph G) =2 @edge_rel (Reconstruction.conjectures.U11.sline_graph G).
Proof.
by [].
Qed.

Lemma sline_graph_diso (G : sgraph) : GraphLegacy.sline_graph G ≃ Reconstruction.conjectures.U11.sline_graph G.
Proof. by rewrite /GraphLegacy.sline_graph /Reconstruction.conjectures.U11.sline_graph /simple_line_graph; apply: eq_diso => e f. Qed.

(** Every iterate, zero included: the identity isomorphisms composed through the functoriality of the line graph. *)
Lemma iter_sline_graph_diso (i : nat) (G : sgraph) : iter i GraphLegacy.sline_graph G ≃ iter i Reconstruction.conjectures.U11.sline_graph G.
Proof.
elim: i => [|i h]; first exact: diso_id.
exact: diso_comp (sline_graph_diso _) (simple_line_graph_diso h).
Qed.

Lemma iter_sline_graph_card_compat (i : nat) (G : sgraph) :
  #|iter i GraphLegacy.sline_graph G| = #|iter i Reconstruction.conjectures.U11.sline_graph G|.
Proof. exact: card_bij (diso_v (iter_sline_graph_diso i G)). Qed.

(** Graham's row: the whole order sequence is the same for every [i : nat]. *)
Lemma grahams_conjecture_on_tree_reconstruction_statement_compat :
  U11Legacy.grahams_conjecture_on_tree_reconstruction_statement <->
  Reconstruction.conjectures.U11.grahams_conjecture_on_tree_reconstruction_statement.
Proof.
split=> st T1 T2 t1 t2 orders; apply: (st T1 T2 t1 t2) => i.
- by rewrite !iter_sline_graph_card_compat; exact: orders.
- by rewrite -!iter_sline_graph_card_compat; exact: orders.
Qed.

(** The Whitney Props: the same edge deck, the line isomorphism composed with the identity isomorphisms. *)
Lemma whitney_line_inversion_premise_compat :
  KellyLegacy.whitney_line_inversion_premise <->
  Reconstruction.foundations.kelly.whitney_line_inversion_premise.
Proof.
split=> W G H mG deck [k]; apply: (W G H mG deck); constructor.
- exact: diso_comp (diso_comp (sline_graph_diso G) k) (diso_sym (sline_graph_diso H)).
- exact: diso_comp (diso_comp (diso_sym (sline_graph_diso G)) k) (sline_graph_diso H).
Qed.

Lemma external_whitney_line_inversion_statement_compat :
  ImplicationsU11Legacy.external_whitney_line_inversion_statement <->
  Reconstruction.conjectures.implications_U11.external_whitney_line_inversion_statement.
Proof.
split=> W G H mG deck [k]; apply: (W G H mG deck); constructor.
- exact: diso_comp (diso_comp (sline_graph_diso G) k) (diso_sym (sline_graph_diso H)).
- exact: diso_comp (diso_comp (diso_sym (sline_graph_diso G)) k) (sline_graph_diso H).
Qed.

(** The complete A4+A25 Originals: the frozen line construction against the live one, then A4's certificates for
    the raw edge deck (the same edge-index bijection, card isomorphisms composed). *)
Lemma whitney_line_inversion_premise_original_compat :
  KellyOriginal.whitney_line_inversion_premise <->
  Reconstruction.foundations.kelly.whitney_line_inversion_premise.
Proof.
apply: (iff_trans _ A4.whitney_line_inversion_premise_compat).
split=> W G H mG deck [k]; apply: (W G H mG deck); constructor.
- exact: diso_comp (diso_comp (sline_graph_diso G) k) (diso_sym (sline_graph_diso H)).
- exact: diso_comp (diso_comp (diso_sym (sline_graph_diso G)) k) (sline_graph_diso H).
Qed.

Lemma external_whitney_line_inversion_statement_original_compat :
  ImplicationsU11Original.external_whitney_line_inversion_statement <->
  Reconstruction.conjectures.implications_U11.external_whitney_line_inversion_statement.
Proof.
apply: (iff_trans _ A4.external_whitney_line_inversion_statement_compat).
split=> W G H mG deck [k]; apply: (W G H mG deck); constructor.
- exact: diso_comp (diso_comp (sline_graph_diso G) k) (diso_sym (sline_graph_diso H)).
- exact: diso_comp (diso_comp (diso_sym (sline_graph_diso G)) k) (sline_graph_diso H).
Qed.
