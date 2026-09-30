(** * Reconstruction.foundations.kelly — the deck machinery behind Greenwell's
      theorem (vertex reconstruction ==> edge reconstruction).

    GOAL.  Close the U11 edge

        reconstruction_statement  ==>  edge_reconstruction_statement

    (Greenwell, Proc. AMS 30 (1971) 431-433) on the EXACT encodings of
    [conjectures.U11], with no added hypothesis on either endpoint.

    WHICH ROUTE.  Two routes exist in the literature.

    (a) Kelly-style COUNTING: recover the vertex deck of [G] from its edge deck
        by counting subgraphs (Kelly's lemma / Nash-Williams' lemma).  On the
        U11 encodings this needs counting of subgraphs up to isomorphism and a
        Mobius inversion over isomorphism classes of graphs on [#|G| - 1]
        vertices — neither of which the [inhabited (_ ≃ _)] / [same_deck]
        vocabulary of U11 supports without a large amount of new machinery.

        (The corpus sketch of the relation gc:e055 names this counting route:
        "the vertex deck can then be recovered by counting arguments".)

    (b) The LINE-GRAPH route, which is the one Greenwell actually takes and the
        one the U11 vocabulary is shaped for: [conjectures.U11] already ships
        [sline_graph : sgraph -> sgraph] whose VERTEX TYPE is literally the
        index type [{e : {set G} | e \in E(G)}] of [same_edge_deck].  Deleting
        the vertex [e] from [sline_graph G] is the same thing as taking the line
        graph of the card [sdel_edge G e]:

            vdel_card (sline_graph G) e  ≃  sline_graph (sdel_edge G e)

        so the edge deck of [G] IS the vertex deck of [sline_graph G].  Hence
        [same_edge_deck G H -> same_deck (sline_graph G) (sline_graph H)], and
        the Reconstruction Conjecture (applied to [sline_graph G], which has
        [#|E(G)| >= 4 >= 3] vertices) yields [sline_graph G ≃ sline_graph H].
        What remains is the INVERSION of the line-graph operation: Whitney's
        theorem (1932) says that two CONNECTED graphs with isomorphic line
        graphs are isomorphic unless they are [K_3] and [K_{1,3}], and the
        four-edge guard of [edge_reconstruction_statement] is there precisely to
        rule that exception out.

    WHAT IS PROVED HERE.  Everything on route (b) except Whitney's theorem:

      - [in_edge_set_sdel] : [E(sdel_edge G e) = E(G) :\ e], pointwise;
      - [card_sline_graph] : [#|sline_graph G| = #|E(G)|];
      - [sline_diso]       : [sline_graph] is functorial on isomorphisms;
      - [vdel_card_sline]  : [vdel_card (sline_graph G) e ≃
                              sline_graph (sdel_edge G (val e))];
      - [same_edge_deck_line] : the edge deck of [G] is the vertex deck of
                              [sline_graph G] (the heart of the reduction);
      - [reconstruction_line_diso] : [reconstruction_statement] gives
                              [sline_graph G ≃ sline_graph H] from
                              [same_edge_deck G H] whenever [3 <= #|E(G)|];
      - [whitney_reconstruction_edge_reconstruction] :
                              [whitney_line_inversion_premise ->
                               reconstruction_statement ->
                               edge_reconstruction_statement].

    WHAT IS MISSING.  [whitney_line_inversion_premise] itself: the line-graph
    inversion step, i.e. Whitney's theorem (H. Whitney, Amer. J. Math. 54 (1932)
    150-168) together with the isolated-vertex bookkeeping of Greenwell's
    argument.  It is literature, not an extra assumption on the endpoints, but
    its Rocq proof (Krausz clique partitions of [L(G)], the
    star-versus-triangle analysis, then a component-by-component argument) is a
    development of its own and is not formalized here; it is kept as an explicit
    premise, so that no [Axiom] / [Admitted] enters the file.

    TWO TRAPS the premise must respect, both on graphs the U11 statements do
    quantify over (isolated vertices are allowed, and [sline_graph] is blind to
    them):

      - the four-edge guard is indispensable: [K_3 + K_1] and [K_{1,3}] have
        four vertices, three edges, the SAME edge deck (every card is
        [P_3 + K_1]) and the same line graph [K_3], yet are not isomorphic;
      - the premise may NOT be weakened to "[L(G) ≃ L(H)] and [#|G| = #|H|] and
        [4 <= #|E(G)|] force [G ≃ H]": that reading of Whitney's theorem is
        FALSE, because an isolated vertex pays for a [K_3]-versus-[K_{1,3}]
        exchange — [K_3 + K_1 + K_2] and [K_{1,3} + K_2] both have six
        vertices and four edges, both have line graph [K_3 + K_1], and they are
        not isomorphic.  Their edge decks DIFFER (deleting the [K_2] edge leaves
        [K_3 + 3 K_1] on one side, [K_{1,3} + 2 K_1] on the other), which is why
        the premise below keeps [same_edge_deck G H] as a hypothesis: Greenwell
        uses the deck, not merely the order, to rule the exception out.  (The order
        equality is then not worth stating: [same_edge_deck_card_vertex] derives
        it.)

    Nothing from [conjectures.U11] is redefined; this file only reasons about
    [sdel_edge], [sline_graph], [vdel_card], [same_edge_deck], [same_deck].
    [card_sline_graph] restates a depth-1 fact that [conjectures.grounding_U11]
    also records (a grounding file is a sanity-check layer, so a foundations
    file does not import it); the adjacency laws are stated here as EQUATIONS
    ([sdel_adjE], [sline_adjE]) rather than the one-way implications of the
    grounding file, whence the [E] suffix. *)

From GTBase Require Export base.
From GTBase Require Import common.
From GraphTheory Require Import preliminaries bij digraph sgraph.
From Reconstruction Require Import conjectures.U11.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ============================================================================
    1.  Adjacency and edge sets of the U11 constructions.
    ========================================================================== *)

(** Adjacency in [sdel_edge G e] is [G]-adjacency minus the single edge [e].
    Both sides live on the vertex type of [G] ([sdel_edge] keeps the
    vertices). *)
Lemma sdel_adjE (G : sgraph) (e : {set G}) (x y : G) :
  @edge_rel (@sdel_edge G e) x y = (x -- y) && ([set x; y] != e).
Proof. by []. Qed.

(** Adjacency in [sline_graph G]: distinct edges whose endpoint sets meet. *)
Lemma sline_adjE (G : sgraph) (a b : sline_graph G) :
  a -- b = (val a != val b) && (val a :&: val b != set0).
Proof. by []. Qed.

(** [sline_graph G] has one vertex per edge of [G]. *)
Lemma card_sline_graph (G : sgraph) : #|sline_graph G| = #|E(G)|.
Proof. by rewrite card_sig. Qed.

(** The edge set of the card [G - e] is [E(G)] minus [e] (and nothing else is
    lost): the one rewrite that identifies the two index types. *)
Lemma in_edge_set_sdel (G : sgraph) (e f : {set G}) :
  (f \in E(@sdel_edge G e)) = (f \in E(G)) && (f != e).
Proof.
apply/idP/idP.
- rewrite (in_sg_edge_set (G := @sdel_edge G e)) => /existsP[x /existsP[y]].
  rewrite sdel_adjE -andbA => /and3P[xy nef /eqP Ef]; rewrite Ef nef andbT.
  rewrite (in_sg_edge_set (G := G)); apply/existsP; exists x; apply/existsP.
  by exists y; rewrite xy eqxx.
- case/andP => /edgesP[x [y] [Ef xy]] nef.
  rewrite (in_sg_edge_set (G := @sdel_edge G e)); apply/existsP; exists x.
  apply/existsP; exists y; rewrite sdel_adjE xy /=.
  by rewrite -Ef nef eqxx.
Qed.

Lemma edge_set_sdel (G : sgraph) (e : {set G}) :
  E(@sdel_edge G e) = E(G) :\ e.
Proof.
suff H : forall f : {set G}, (f \in E(@sdel_edge G e)) = (f \in E(G) :\ e).
  by apply/setP => f; exact: H f.
by move=> f; rewrite in_edge_set_sdel in_setD1 andbC.
Qed.

(** ============================================================================
    2.  [sline_graph] is functorial on isomorphisms.
    ========================================================================== *)

(** [imsetI] for a globally injective map, in rewrite-ready form. *)
Lemma imsetI_inj (aT rT : finType) (f : aT -> rT) :
  injective f ->
  forall A B : {set aT}, f @: (A :&: B) = f @: A :&: f @: B.
Proof. by move=> inj_f A B; apply: imsetI => x y _ _; exact: (inj_f x y). Qed.

Section LineDiso.
Variables (G H : sgraph).
Variable h : diso G H.

Lemma diso_imset_edge (f : {set G}) : f \in E(G) -> h @: f \in E(H).
Proof.
case/edgesP => x [y] [-> xy]; rewrite imsetU1 imset_set1 in_edges.
by rewrite (edge_diso h).
Qed.

Lemma diso_imset_edge' (f : {set H}) : f \in E(H) -> h^-1 @: f \in E(G).
Proof.
case/edgesP => x [y] [-> xy]; rewrite imsetU1 imset_set1 in_edges.
by rewrite (edge_diso' h).
Qed.

Lemma imset_bijK (A : {set G}) : h^-1 @: (h @: A) = A.
Proof.
apply/setP => x; apply/idP/idP.
- by case/imsetP => y /imsetP[z zA ->] ->; rewrite bijK.
- by move=> xA; rewrite -(bijK h x); exact: imset_f _ (imset_f _ xA).
Qed.

Lemma imset_bijK' (A : {set H}) : h @: (h^-1 @: A) = A.
Proof.
apply/setP => x; apply/idP/idP.
- by case/imsetP => y /imsetP[z zA ->] ->; rewrite bijK'.
- by move=> xA; rewrite -(bijK' h x); exact: imset_f _ (imset_f _ xA).
Qed.

Definition sldf (a : sline_graph G) : sline_graph H :=
  Sub (h @: val a) (diso_imset_edge (valP a)).

Definition sldb (a : sline_graph H) : sline_graph G :=
  Sub (h^-1 @: val a) (diso_imset_edge' (valP a)).

Lemma sldfK : cancel sldf sldb.
Proof. by move=> a; apply: val_inj; rewrite /= imset_bijK. Qed.

Lemma sldbK : cancel sldb sldf.
Proof. by move=> a; apply: val_inj; rewrite /= imset_bijK'. Qed.

Lemma sldf_mono : {mono sldf : a b / a -- b}.
Proof.
have inj_h : injective h := @bij_injective _ _ (diso_v h).
move=> a b; rewrite !sline_adjE /= -(imsetI_inj inj_h).
by rewrite (inj_eq (imset_inj inj_h)) imset_eq0.
Qed.

End LineDiso.

Lemma sline_diso (G H : sgraph) : G ≃ H -> sline_graph G ≃ sline_graph H.
Proof. move=> h; exact: Diso' (@sldfK _ _ h) (@sldbK _ _ h) (@sldf_mono _ _ h). Qed.

(** ============================================================================
    3.  Deleting a vertex of [sline_graph G] = the line graph of a card.
    ========================================================================== *)

Section LineCard.
Variables (G : sgraph) (e0 : sline_graph G).

Lemma lcf_proof (x : @vdel_card (sline_graph G) e0) :
  val (val x) \in E(@sdel_edge G (val e0)).
Proof.
rewrite in_edge_set_sdel (valP (val x)) val_eqE /=.
by move: (valP x); rewrite inE.
Qed.

Definition lcf (x : @vdel_card (sline_graph G) e0) :
    sline_graph (@sdel_edge G (val e0)) := Sub (val (val x)) (lcf_proof x).

Lemma lcb_in (f : sline_graph (@sdel_edge G (val e0))) :
  ((val f : {set G}) \in E(G)) && ((val f : {set G}) != val e0).
Proof.
have H : (val f : {set G}) \in E(@sdel_edge G (val e0)) := valP f.
by rewrite in_edge_set_sdel in H.
Qed.

Lemma lcb_proof1 (f : sline_graph (@sdel_edge G (val e0))) : val f \in E(G).
Proof. by case/andP: (lcb_in f). Qed.

Definition lcb0 (f : sline_graph (@sdel_edge G (val e0))) : sline_graph G :=
  Sub (val f) (lcb_proof1 f).

Lemma lcb_proof2 (f : sline_graph (@sdel_edge G (val e0))) :
  lcb0 f \in [set u : sline_graph G | u != e0].
Proof. by rewrite inE -val_eqE /=; case/andP: (lcb_in f). Qed.

Definition lcb (f : sline_graph (@sdel_edge G (val e0))) :
    @vdel_card (sline_graph G) e0 := Sub (lcb0 f) (lcb_proof2 f).

Lemma lcfK : cancel lcf lcb.
Proof. by move=> x; apply: val_inj; apply: val_inj. Qed.

Lemma lcbK : cancel lcb lcf.
Proof. by move=> f; apply: val_inj. Qed.

Lemma lcf_mono : {mono lcf : x y / x -- y}.
Proof. by []. Qed.

Lemma vdel_card_sline :
  @vdel_card (sline_graph G) e0 ≃ sline_graph (@sdel_edge G (val e0)).
Proof. exact: Diso' lcfK lcbK lcf_mono. Qed.

End LineCard.

(** ============================================================================
    4.  The edge deck of [G] IS the vertex deck of [sline_graph G].
    ========================================================================== *)

Lemma same_edge_deck_line (G H : sgraph) :
  same_edge_deck G H -> same_deck (sline_graph G) (sline_graph H).
Proof.
case=> f [bij_f Hf]; exists f; split=> // e.
case: (Hf e) => k; constructor.
apply: diso_comp (vdel_card_sline e) _.
apply: diso_comp (sline_diso k) _.
exact: diso_sym (vdel_card_sline (f e)).
Qed.

Lemma same_edge_deck_card_edge (G H : sgraph) :
  same_edge_deck G H -> #|E(G)| = #|E(H)|.
Proof.
case=> f [bij_f _]; rewrite -!card_sline_graph; exact: bij_card_eq bij_f.
Qed.

(** With at least one edge, the edge deck already pins the vertex count down:
    an isomorphism of cards is a bijection of the (unchanged) vertex types. *)
Lemma same_edge_deck_card_vertex (G H : sgraph) :
  (0 < #|E(G)|)%N -> same_edge_deck G H -> #|G| = #|H|.
Proof.
move=> mG [f [_ Hf]].
have /set0Pn[e ee] : E(G) != set0 by rewrite -card_gt0.
by case: (Hf (Sub e ee)) => k; exact: bij_card_eq (bij_bijective (diso_v k)).
Qed.

(** ============================================================================
    5.  Greenwell's reduction.
    ========================================================================== *)

(** The Reconstruction Conjecture, applied to the line graphs, turns equality of
    edge decks into an isomorphism of line graphs. *)
Theorem reconstruction_line_diso :
  reconstruction_statement ->
  forall G H : sgraph, (3 <= #|E(G)|)%N -> same_edge_deck G H ->
    inhabited (sline_graph G ≃ sline_graph H).
Proof.
move=> RC G H mG dGH; apply: RC; last exact: same_edge_deck_line.
- by rewrite card_sline_graph.
- by rewrite card_sline_graph -(same_edge_deck_card_edge dGH).
Qed.

(** The line-graph INVERSION step of Greenwell's proof, in exactly the form the
    reduction needs: between two graphs with at least four edges and the same
    edge deck, an isomorphism of line graphs comes from an isomorphism of the
    graphs.  This is Whitney's theorem (H. Whitney, "Congruent graphs and the
    connectivity of graphs", Amer. J. Math. 54 (1932) 150-168: two CONNECTED
    graphs with isomorphic line graphs are isomorphic unless they are [K_3] and
    [K_{1,3}]) plus the isolated-vertex bookkeeping of Greenwell's argument; see
    the two traps recorded in the header for why neither the four-edge guard nor
    the [same_edge_deck] hypothesis may be dropped.  NOT proved here: it is kept
    as an explicit premise, never an [Axiom]. *)
Definition whitney_line_inversion_premise : Prop :=
  forall G H : sgraph, (4 <= #|E(G)|)%N -> same_edge_deck G H ->
    inhabited (sline_graph G ≃ sline_graph H) -> inhabited (G ≃ H).

(** Greenwell's theorem, modulo that one inversion step: the Reconstruction
    Conjecture implies the Edge Reconstruction Conjecture. *)
Theorem whitney_reconstruction_edge_reconstruction :
  whitney_line_inversion_premise ->
  reconstruction_statement -> edge_reconstruction_statement.
Proof.
move=> W RC G mG H dGH; apply: W; [exact: mG | exact: dGH |].
apply: (reconstruction_line_diso RC); last exact: dGH.
by apply: leq_trans mG.
Qed.
