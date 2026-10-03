(** * Reconstruction.conjectures.grounding_U11 — grounding lemmas for U11.

    SIMPLE, Qed-closed sanity results validating the NEW primitives introduced
    in [U11.v] (the reconstruction vocabulary: Seidel switch, simple-graph edge
    deletion, simple-graph line operation, vertex-deleted card, and the three
    deck-equality predicates).  For each new definition we record a SATISFIABLE
    witness and at least one textbook identity.  These are statement-VALIDATION
    lemmas, NOT the (open) conjectures themselves.

    Two tiny concrete carriers are used for the simple-graph witnesses:
      - [En n] : the edgeless ("empty") graph on ['I_n];
      - [Kn n] : the complete graph on ['I_n]. *)

From GTBase Require Import base.
From Reconstruction.conjectures Require Import U11.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ============================================================================
    Tiny concrete carriers.
    ========================================================================== *)

Section EmptyGraph.
Variable n : nat.
Definition En_rel : rel 'I_n := fun _ _ => false.
Lemma En_sym : symmetric En_rel. Proof. by []. Qed.
Lemma En_irr : irreflexive En_rel. Proof. by []. Qed.
Definition En : sgraph := SGraph En_sym En_irr.
End EmptyGraph.

Lemma En_edge (n : nat) (x y : En n) : (x -- y) = false.
Proof. by []. Qed.

Section CompleteGraph.
Variable n : nat.
Definition Kn_rel : rel 'I_n := fun x y => x != y.
Lemma Kn_sym : symmetric Kn_rel. Proof. by move=> x y; rewrite /Kn_rel eq_sym. Qed.
Lemma Kn_irr : irreflexive Kn_rel. Proof. by move=> x; rewrite /Kn_rel eqxx. Qed.
Definition Kn : sgraph := SGraph Kn_sym Kn_irr.
End CompleteGraph.

Lemma Kn_edge (n : nat) (x y : Kn n) : (x -- y) = (x != y).
Proof. by []. Qed.

Definition v0 : Kn 3 := @Ordinal 3 0 isT.

Definition u0 : En 2 := @Ordinal 2 0 isT.
Definition u1 : En 2 := @Ordinal 2 1 isT.
Lemma u0n1 : u0 != u1. Proof. by rewrite -val_eqE. Qed.

(** ============================================================================
    [vertex_switch] / [switch_vertex] — the Seidel switch.
    ========================================================================== *)

(** identity (adjacency law): an edge of the Seidel switch is exactly the
    original edge toggled by whether its endpoints cross [S]. *)
Lemma vertex_switch_edge (G : sgraph) (S : {set G}) (x y : vertex_switch S) :
  (x -- y) = (@sedge G x y) (+) ((x \in S) (+) (y \in S)).
Proof. by []. Qed.

(** identity: switching w.r.t. the FULL vertex set fixes the graph (both
    endpoints cross [S], the two toggles cancel). *)
Lemma vertex_switch_setT (G : sgraph) (x y : G) :
  @sedge (vertex_switch [set: G]) x y = @sedge G x y.
Proof. by rewrite (vertex_switch_edge (G:=G)) !in_setT addbb addbF. Qed.

(** identity: the Seidel switch is an INVOLUTION — switching twice w.r.t. the
    same vertex set restores every adjacency. *)
Lemma vertex_switch_involution (G : sgraph) (S : {set G}) (x y : G) :
  @sedge (@vertex_switch (vertex_switch S) S) x y = @sedge G x y.
Proof.
by rewrite (vertex_switch_edge (G:=vertex_switch S)) (vertex_switch_edge (G:=G))
           -addbA addbb addbF.
Qed.

(** witness: switching at a vertex of the EDGELESS graph CREATES an edge —
    [u0] and [u1] become adjacent in [switch_vertex (En 2) u0]. *)
Lemma switch_vertex_creates_edge :
  (u0 : @switch_vertex (En 2) u0) -- u1.
Proof.
by rewrite /switch_vertex (vertex_switch_edge (G:=En 2)) En_edge
           !inE eqxx eq_sym (negbTE u0n1).
Qed.

(** ============================================================================
    [sdel_edge] — simple-graph edge deletion.
    ========================================================================== *)

(** identity (subgraph law): every adjacency surviving an edge deletion was an
    adjacency of the original graph. *)
Lemma sdel_edge_sub (G : sgraph) (e : {set G}) (x y : sdel_edge e) :
  x -- y -> @sedge G x y.
Proof. by move=> /andP[]. Qed.

(** identity: deleting the empty "edge" [set0] changes nothing (a real edge has
    a nonempty endpoint set, so it is never equal to [set0]). *)
Lemma sdel_edge_set0 (G : sgraph) (x y : G) :
  @sedge (sdel_edge (set0 : {set G})) x y = @sedge G x y.
Proof.
have h : [set x; y] != set0 by apply/set0Pn; exists x; rewrite !inE eqxx.
change ((x -- y) && ([set x; y] \notin [set set0]) = x -- y).
by rewrite inE h andbT.
Qed.

(** witness: the deleted edge is genuinely gone — its two endpoints are no
    longer adjacent in [sdel_edge G [set x; y]]. *)
Lemma sdel_edge_removes (G : sgraph) (x y : G) :
  @sedge (sdel_edge [set x; y]) x y = false.
Proof.
change ((x -- y) && ([set x; y] \notin [set [set x; y]]) = false).
by rewrite inE eqxx andbF.
Qed.

(** ----------------------------------------------------------------------------
    TECHNIQUE #3 — independent re-encoding of [sdel_edge] via base's [del_edges].

    [sdel_edge e] (U11) removes the SINGLE adjacency whose endpoint set EQUALS
    [e] (per-pair test [[set x; y] != e]).  base's independently-authored
    [del_edges A] (GraphTheory.core.sgraph, re-exported by GTBase.base) removes
    EVERY adjacency whose endpoint set is a SUBSET of the vertex set [A]
    (per-pair test [~~ ([set x; y] \subset A)]):

        del_edges_rel A := [rel x y | x -- y && ~~ ([set x; y] \subset A)]
        del_edges A      := SGraph del_edges_sym del_edges_irrefl.

    These are two structurally different edge-deletion schemes
    (equality-of-endpoint-set vs subset-of-a-vertex-set).  On a genuine edge
    [e ∈ E(G)] they coincide, and the bridge is the real 2-set combinatorial
    fact [edges_eqn_sub] (two DISTINCT edges are never [\subset]-related, proved
    in base by [cards2]/[pred2P] case analysis) — NOT reflexivity.  A bug in
    [sde_rel] (a flipped test, [:&:] for the endpoint test, or a reversed subset
    direction) breaks the equivalences below against the independent [del_edges].

    Core: on a genuine edge, the two deletion RELATIONS agree pointwise. *)
Lemma sde_del_edges_rel (G : sgraph) (e : {set G}) :
  e \in E(G) -> sde_rel e =2 del_edges_rel e.
Proof.
move=> He x y; rewrite /sde_rel /del_es_rel /del_edges_rel /= inE.
case: (boolP (x -- y)) => xy; last by [].
have He2 : [set x; y] \in E(G) by rewrite in_edges.
apply/idP/idP => [neq | nsub].
  exact: edges_eqn_sub He2 He neq.
by apply: contraNneq nsub => ->; exact: subxx.
Qed.

(** The [<->] at adjacency level: a pair [x, y] survives U11's [sdel_edge e]
    iff it survives base's [del_edges e], whenever [e] is a genuine edge. *)
Lemma sde_del_edges_adj (G : sgraph) (e : {set G}) (x y : G) :
  e \in E(G) ->
  (@sedge (sdel_edge e) x y <-> @sedge (del_edges e) x y).
Proof.
by move=> He; change (sde_rel e x y <-> @sedge (del_edges e) x y);
  rewrite (sde_del_edges_rel He).
Qed.

(** Whole-graph faithfulness: on a genuine edge, U11's [sdel_edge e] and base's
    [del_edges e] are the SAME simple graph (isomorphic via the identity vertex
    map) — two independently authored formalizations of "delete the edge [e]"
    provably agree. *)
Lemma sdel_edge_diso_del_edges (G : sgraph) (e : {set G}) :
  e \in E(G) -> diso (sdel_edge e) (del_edges e).
Proof. by move=> He; apply: eq_diso; apply: sde_del_edges_rel He. Qed.

(** ============================================================================
    [sline_graph] — simple-graph line operation.
    ========================================================================== *)

(** identity (the Row-3 depth-1 fact): the line graph has one vertex per edge of
    [G], so [|V(L(G))| = |E(G)|]. *)
Lemma card_sline_graph (G : sgraph) : #|sline_graph G| = #|E(G)|.
Proof. by rewrite card_sig; apply: eq_card => e; rewrite inE. Qed.

(** identity: connecting the statement to [iter] — one line step counts edges. *)
Lemma card_iter1_sline (G : sgraph) : #|iter 1 sline_graph G| = #|E(G)|.
Proof. exact: card_sline_graph. Qed.

(** identity (adjacency law): line-graph-adjacent edges are distinct and share
    an endpoint (their endpoint sets meet). *)
Lemma sline_adj (G : sgraph) (e1 e2 : sline_graph G) :
  e1 -- e2 -> (val e1 != val e2) /\ (val e1 :&: val e2 != set0).
Proof. by rewrite /= /sline_rel => /andP[]. Qed.

(** witness: the line graph of an edgeless graph is empty (no edges, no
    line-vertices). *)
Lemma card_sline_En : #|sline_graph (En 2)| = 0.
Proof.
rewrite card_sline_graph; apply/eqP; rewrite cards_eq0.
apply/eqP/setP => e; rewrite !inE.
by apply/negbTE/negP => /edgesP[x [y [_]]]; rewrite En_edge.
Qed.

(** ============================================================================
    [vdel_card] — vertex-deleted card [G − v].
    ========================================================================== *)

(** identity: deleting one vertex drops the vertex count by exactly one. *)
Lemma card_vdel_card (G : sgraph) (v : G) : #|vdel_card v| = #|G|.-1.
Proof.
rewrite /vdel_card card_sig -(cardsC1 v); apply: eq_card => u.
by rewrite !inE.
Qed.

(** witness: a vertex-deleted card of [Kn 3] has two vertices. *)
Lemma card_vdel_Kn3 : #|vdel_card v0| = 2.
Proof. by rewrite card_vdel_card card_ord. Qed.

(** ============================================================================
    Deck-equality predicates (reconstruction-specific).
    ========================================================================== *)

(** witness / reflexivity: every graph has the SAME switching deck as itself
    (identity bijection + reflexive isomorphism), so the hypothesis of
    [switching_reconstructible] is satisfiable (non-vacuous). *)
Lemma same_switching_deck_refl (G : sgraph) : same_switching_deck G G.
Proof.
by exists id; split; [exact: preliminaries.id_bij | move=> v; exact: (inhabits diso_id)].
Qed.

(** witness / reflexivity for the edge deck. *)
Lemma same_edge_deck_refl (G : sgraph) : same_edge_deck G G.
Proof.
by exists id; split; [exact: preliminaries.id_bij | move=> e; exact: (inhabits diso_id)].
Qed.

(** witness / reflexivity for the vertex deck. *)
Lemma same_deck_refl (G : sgraph) : same_deck G G.
Proof.
by exists id; split; [exact: preliminaries.id_bij | move=> v; exact: (inhabits diso_id)].
Qed.

(** identity: "same deck" forces equal vertex counts (the index bijection is a
    bijection of vertex sets). *)
Lemma same_deck_card (G H : sgraph) : same_deck G H -> #|G| = #|H|.
Proof. by case=> f [bf _]; exact: bij_eq_card bf. Qed.

(** identity: "same edge deck" forces equal edge counts. *)
Lemma same_edge_deck_card (G H : sgraph) :
  same_edge_deck G H -> #|E(G)| = #|E(H)|.
Proof.
case=> f [bf _].
have h := bij_eq_card bf; rewrite !card_sig in h.
rewrite (eq_card (B := [pred e | e \in E(G)])); last by move=> e; rewrite inE.
rewrite [#|E(H)|](eq_card (B := [pred e | e \in E(H)])); last by move=> e; rewrite inE.
exact: h.
Qed.

(** identity: a reconstructible graph is reconstructed by ITSELF (the conclusion
    holds reflexively). *)
Lemma reconstructible_self (G : sgraph) :
  reconstructible G -> inhabited (G ≃ G).
Proof. by move=> _; exact: (inhabits diso_id). Qed.

(** ============================================================================
    [is_tree] / [is_forest] — the tree hypothesis (Row 3 Graham, Row 4 Ulam).
    ========================================================================== *)

(** witness / satisfiability: the single-vertex graph [sunit] IS a tree, so the
    [is_tree [set: T]] hypothesis of Graham's tree-reconstruction problem is not
    vacuously empty. *)
Lemma is_tree_sunit : is_tree [set: sunit].
Proof.
split; first exact: unit_forest.
have -> : [set: sunit] = [set (tt : sunit)]
  by apply/setP => x; case: x; rewrite !inE eqxx.
exact: connected1.
Qed.

(** guard-has-teeth: the triangle [Kn 3] is NOT a forest (hence not a tree), so
    the [is_forest]/[is_tree] guard genuinely bites (library lemma [forest3]:
    a forest on >= 3 vertices has a non-adjacent pair, but [Kn 3] is complete). *)
Lemma not_forest_Kn3 : ~ is_forest [set: Kn 3].
Proof.
move=> Hf.
have card3 : (3 <= #|Kn 3|)%N by rewrite card_ord.
have [x [y [xy nadj]]] := forest3 Hf card3.
by rewrite Kn_edge xy in nadj.
Qed.
