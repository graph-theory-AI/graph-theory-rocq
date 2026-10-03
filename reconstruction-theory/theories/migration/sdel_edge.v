(** * Reconstruction.migration.sdel_edge -- frozen U11 single-edge deletion certificates

    Batch A, family A4 (U11's cross-name single-edge deletion [sde_rel],
    [sdel_edge]), the reconstruction companion of A3.  U11's Section [DelEdge]
    is frozen as it stood at 9e03072 (unchanged through dde0199), in
    dependency-ordered modules: [Legacy] holds the relation
    [(x -- y) && ([set x; y] != e)], [ProofsLegacy] the full [sde_sym]/[sde_irrefl]
    proofs and [GraphLegacy] the [SGraph] built from them.  Each sits in a verbatim
    copy of the Section scaffolding [Variables (G : sgraph) (e : {set G})], so the
    discharged arguments are the original's, and references to the earlier frozen
    names are module-qualified ([sde_rel] -> [(Legacy.sde_rel e)], the same term
    once the Section is closed).  [U11Legacy] freezes the affected chain
    [same_edge_deck] -> [edge_reconstructible] -> [edge_reconstruction_statement];
    [KellyLegacy] freezes [whitney_line_inversion_premise] and
    [ImplicationsU11Legacy] the non-corpus [external_whitney_line_inversion_statement],
    both with the four-edge guard AND the same-edge-deck hypothesis.

    The live helpers now unfold to [del_es_rel G [set e]] and
    [del_edge_set G [set e]].  For every vertex set [e], valid edge or not, the
    frozen and live adjacencies agree pointwise ([sde_rel_compat]), so the
    identity is an isomorphism of the cards ([sdel_edge_diso]).
    [same_edge_deck_compat] keeps the SAME edge-index bijection and composes each
    card isomorphism with these identity isomorphisms, so every card keeps its
    multiplicity.  The external theorem and Greenwell's implication stay
    conditional: [legacy_reconstruction_implies_edge_reconstruction] only
    transports the existing implication to the frozen encodings.

    No earlier migration snapshot references this U11 chain.  The regeneration
    spec is meta/migration_reports/sdel_edge.spec.json. *)

From GTBase Require Import base.
From Reconstruction Require Import conjectures.U11 foundations.kelly.
From Reconstruction Require Import conjectures.implications_U11.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Legacy.

Section DelEdge.
Variables (G : sgraph) (e : {set G}).
Definition sde_rel : rel G := fun x y => (x -- y) && ([set x; y] != e).
End DelEdge.

End Legacy.

Module ProofsLegacy.

Section DelEdge.
Variables (G : sgraph) (e : {set G}).
Lemma sde_sym : symmetric (Legacy.sde_rel e).
Proof. by move=> x y; rewrite /Legacy.sde_rel sg_sym setUC. Qed.
Lemma sde_irrefl : irreflexive (Legacy.sde_rel e).
Proof. by move=> x; rewrite /Legacy.sde_rel sg_irrefl. Qed.
End DelEdge.

End ProofsLegacy.

Module GraphLegacy.

Section DelEdge.
Variables (G : sgraph) (e : {set G}).
Definition sdel_edge : sgraph := SGraph (ProofsLegacy.sde_sym e) (ProofsLegacy.sde_irrefl e).
End DelEdge.

End GraphLegacy.

(** ** Helper certificates *)

(** Unconditional: [e] need not be an edge, nor a two-element set. *)
Lemma sde_rel_compat (G : sgraph) (e : {set G}) :
  @Legacy.sde_rel G e =2 @sde_rel G e.
Proof. by move=> x y; rewrite /Legacy.sde_rel /sde_rel /del_es_rel /= inE. Qed.

Lemma sdel_edge_compat (G : sgraph) (e : {set G}) :
  @edge_rel (@GraphLegacy.sdel_edge G e) =2 @edge_rel (@sdel_edge G e).
Proof. by move=> x y; exact: (@sde_rel_compat G e x y). Qed.

Lemma sdel_edge_diso (G : sgraph) (e : {set G}) :
  @GraphLegacy.sdel_edge G e ≃ @sdel_edge G e.
Proof.
rewrite /GraphLegacy.sdel_edge; apply: del_edge_set_eq_diso => x y.
exact: (@sde_rel_compat G e x y).
Qed.

(** Graph-construction certificate: the [SGraph] built from the frozen symmetry and
    irreflexivity proofs is isomorphic, through the identity, to the one built from
    the retained live lemmas.  It relates the two constructions; it does not equate
    the opaque proof terms. *)
Lemma sdel_edge_proofs_compat (G : sgraph) (e : {set G}) :
  SGraph (@ProofsLegacy.sde_sym G e) (@ProofsLegacy.sde_irrefl G e) ≃
  SGraph (@sde_sym G e) (@sde_irrefl G e).
Proof. by apply: eq_diso => x y; exact: (@sde_rel_compat G e x y). Qed.

(** ** U11 row 2: edge reconstruction *)

Module U11Legacy.

Definition same_edge_deck (G H : sgraph) : Prop :=
  exists f : {e : {set G} | e \in E(G)} -> {e : {set H} | e \in E(H)},
    bijective f /\
    forall e : {e : {set G} | e \in E(G)},
      inhabited (@GraphLegacy.sdel_edge G (val e) ≃ @GraphLegacy.sdel_edge H (val (f e))).

Definition edge_reconstructible (G : sgraph) : Prop :=
  forall H : sgraph, U11Legacy.same_edge_deck G H -> inhabited (G ≃ H).

Definition edge_reconstruction_statement : Prop :=
  forall G : sgraph, (4 <= #|E(G)|)%N -> U11Legacy.edge_reconstructible G.

End U11Legacy.

(** The same bijection [f] of edge indices; each card isomorphism is composed with
    the identity isomorphisms of its two cards. *)
Lemma same_edge_deck_compat (G H : sgraph) :
  U11Legacy.same_edge_deck G H <-> same_edge_deck G H.
Proof.
split=> -[f [bij_f cards]]; exists f; split=> // e; case: (cards e) => k; constructor.
- exact: diso_comp (diso_comp (diso_sym (@sdel_edge_diso G (val e))) k)
                   (@sdel_edge_diso H (val (f e))).
- exact: diso_comp (diso_comp (@sdel_edge_diso G (val e)) k)
                   (diso_sym (@sdel_edge_diso H (val (f e)))).
Qed.

Lemma edge_reconstructible_compat (G : sgraph) :
  U11Legacy.edge_reconstructible G <-> edge_reconstructible G.
Proof.
split=> rec H deck; apply: rec.
- exact: (proj2 (same_edge_deck_compat G H) deck).
- exact: (proj1 (same_edge_deck_compat G H) deck).
Qed.

(** opg:edge_reconstruction_conjecture (open, unchanged). *)
Lemma edge_reconstruction_statement_compat :
  U11Legacy.edge_reconstruction_statement <-> edge_reconstruction_statement.
Proof.
split=> st G mG.
- exact: (proj1 (edge_reconstructible_compat G) (st G mG)).
- exact: (proj2 (edge_reconstructible_compat G) (st G mG)).
Qed.

(** ** The line-graph inversion premise of Greenwell's reduction *)

Module KellyLegacy.

Definition whitney_line_inversion_premise : Prop :=
  forall G H : sgraph, (4 <= #|E(G)|)%N -> U11Legacy.same_edge_deck G H ->
    inhabited (sline_graph G ≃ sline_graph H) -> inhabited (G ≃ H).

End KellyLegacy.

Lemma whitney_line_inversion_premise_compat :
  KellyLegacy.whitney_line_inversion_premise <-> whitney_line_inversion_premise.
Proof.
split=> W G H mG deck; apply: W mG _.
- exact: (proj2 (same_edge_deck_compat G H) deck).
- exact: (proj1 (same_edge_deck_compat G H) deck).
Qed.

Module ImplicationsU11Legacy.

Definition external_whitney_line_inversion_statement : Prop :=
  forall G H : sgraph, (4 <= #|E(G)|)%N -> U11Legacy.same_edge_deck G H ->
    inhabited (sline_graph G ≃ sline_graph H) -> inhabited (G ≃ H).

End ImplicationsU11Legacy.

(** Non-corpus external theorem (Whitney 1932 with Greenwell's bookkeeping),
    registered in meta/external_theorems.json; unchanged and still unproved. *)
Lemma external_whitney_line_inversion_statement_compat :
  ImplicationsU11Legacy.external_whitney_line_inversion_statement <->
  external_whitney_line_inversion_statement.
Proof.
split=> W G H mG deck; apply: W mG _.
- exact: (proj2 (same_edge_deck_compat G H) deck).
- exact: (proj1 (same_edge_deck_compat G H) deck).
Qed.

(** Greenwell's conditional implication, on the frozen encodings: the same
    external hypothesis, the unchanged [reconstruction_statement], no new
    assumption. *)
Lemma legacy_reconstruction_implies_edge_reconstruction :
  ImplicationsU11Legacy.external_whitney_line_inversion_statement ->
  reconstruction_statement -> U11Legacy.edge_reconstruction_statement.
Proof.
move=> /external_whitney_line_inversion_statement_compat W RC.
exact: (proj2 edge_reconstruction_statement_compat
          (reconstruction_implies_edge_reconstruction W RC)).
Qed.

Print Assumptions sde_rel_compat.
Print Assumptions sdel_edge_compat.
Print Assumptions sdel_edge_diso.
Print Assumptions sdel_edge_proofs_compat.
Print Assumptions same_edge_deck_compat.
Print Assumptions edge_reconstructible_compat.
Print Assumptions edge_reconstruction_statement_compat.
Print Assumptions whitney_line_inversion_premise_compat.
Print Assumptions external_whitney_line_inversion_statement_compat.
Print Assumptions legacy_reconstruction_implies_edge_reconstruction.
