(** * Reconstruction.conjectures.implications_U11 — milestone U11 edge spine.

    Implication / refutation EDGES among the four U11 terminal statements of
    [conjectures.U11]:

      (R1) switching_reconstruction_statement                       (Stanley)
      (R2) edge_reconstruction_statement                            (Harary)
      (R3) grahams_conjecture_on_tree_reconstruction_statement      (Graham)
      (R4) reconstruction_statement                                 (Kelly–Ulam)

    Each edge is a RELATIVE theorem [Theorem <A>_implies_<B> : A -> B] meant to
    be [Qed]-closed WITHOUT resolving either endpoint conjecture.  Per the edge
    policy (OPG_FULL_FORMALIZATION_PLAN.md §6) only 'verified-literature' edges
    that carry exact endpoint formulations + citation are scheduled as real
    theorems; 'candidate' edges are recorded as annotation-only until they have
    been re-derived through the [Qed] gate.

    FINDINGS for U11 (see the per-edge analysis below):

    * The ONLY genuine inter-conjecture implication in the reconstruction
      literature among these four nodes is

          reconstruction_statement  ==>  edge_reconstruction_statement

      (Greenwell 1971: the Vertex Reconstruction Conjecture implies the Edge
      Reconstruction Conjecture).  It is NOT a thin logical entailment between
      the two [Prop]s: Greenwell's proof runs the vertex deck of the LINE graph
      and then inverts the line-graph operation by Whitney's theorem.
      [foundations.kelly] now carries that whole argument on the exact U11
      encodings, [Qed]-closed and axiom-free, leaving the line-graph inversion
      step (Whitney 1932 + Greenwell's bookkeeping) as its single explicit,
      cited hypothesis
      ([external_whitney_line_inversion_statement] below, and
      [reconstruction_implies_edge_reconstruction]).  Until that external is
      registered in [meta/external_theorems.json] (which would make the edge
      [status=conditional]) the edge stays a CANDIDATE: what is missing is a
      Rocq proof of Whitney's theorem, nothing about the two endpoints.

    * The other pairs carry NO known literature implication and therefore NO
      edge is asserted:
        - switching reconstruction (R1, a Seidel-switching-class problem) is
          independent of vertex/edge reconstruction — no implication is known in
          either direction; asserting one would be unfounded.
        - Graham's tree problem (R3) is an independent open problem about the
          iterated-line-graph order sequence of trees; it has no known
          implication to or from R1/R2/R4.

    * NO refuted-direction edge applies here: none of the FALSE/withdrawn edges
      listed in the policy (Reed=>Borodin–Kostochka, list-total=>Behzad,
      list-Hadwiger=>Hadwiger, Caccetta–Häggkvist=>Seymour) involves a U11 node.

    Consequently this file schedules ZERO verified theorems, ONE candidate
    annotation and ONE [Qed]-closed conditional theorem for that candidate.  It
    compiles green and is axiom-free. *)

From Reconstruction Require Export conjectures.U11.
From Reconstruction Require Import conjectures.X21.
From Reconstruction Require Import foundations.kelly.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ----------------------------------------------------------------------------
    EDGE 1 (CANDIDATE).  Vertex reconstruction ==> edge reconstruction.

    Exact endpoints (as formalized in [conjectures.U11]):
      from : reconstruction_statement
             [forall G H, 3 <= #|G| -> 3 <= #|H| -> same_deck G H ->
              inhabited (G ≃ H)]
      to   : edge_reconstruction_statement
             [forall G, 4 <= #|E(G)| -> edge_reconstructible G]

    Citation: D. L. Greenwell, "Reconstruction of graphs", Proc. Amer. Math.
    Soc. 30 (1971) 431–433; see also Bondy, "A graph reconstructor's manual"
    (1991), and Lauri–Scapellato, "Topics in Graph Automorphisms and
    Reconstruction".

    HOW FAR IT IS REDUCED (all of it in [foundations.kelly], all [Qed]-closed
    and "Closed under the global context"):

      - deleting the vertex [e] from [sline_graph G] IS taking the line graph of
        the card [sdel_edge G e] ([kelly.vdel_card_sline]), so the EDGE deck of
        [G] is literally the VERTEX deck of [sline_graph G]:
        [same_edge_deck G H -> same_deck (sline_graph G) (sline_graph H)]
        ([kelly.same_edge_deck_line]);
      - [#|sline_graph G| = #|E(G)|] ([kelly.card_sline_graph]), so the
        three-vertex guard of [reconstruction_statement] is met as soon as [G]
        has three edges, and [reconstruction_statement] yields
        [inhabited (sline_graph G ≃ sline_graph H)]
        ([kelly.reconstruction_line_diso]);
      - a card [sdel_edge G e] keeps the vertices of [G], so [same_edge_deck]
        already forces [#|G| = #|H|] ([kelly.same_edge_deck_card_vertex]).

    WHAT IS LEFT is the INVERSION of the line-graph operation: Whitney's theorem
    (1932) plus the isolated-vertex bookkeeping of Greenwell's argument, carried
    below as the single explicit hypothesis
    [external_whitney_line_inversion_statement] of the [Qed]-closed
    [reconstruction_implies_edge_reconstruction].

    Two traps that premise must respect (the U11 statements quantify over graphs
    WITH isolated vertices, which a line graph cannot see):
      - the four-edge guard is indispensable: [K_3 + K_1] and [K_{1,3}] have
        four vertices, three edges, the SAME edge deck (every card is
        [P_3 + K_1]) and the same line graph [K_3], yet are not isomorphic;
      - the premise may NOT be weakened to "[sline_graph G ≃ sline_graph H] and
        [#|G| = #|H|] and [4 <= #|E(G)|] force [G ≃ H]": that reading of
        Whitney's theorem is FALSE, since an isolated vertex pays for a
        [K_3]-versus-[K_{1,3}] exchange — [K_3 + K_1 + K_2] and [K_{1,3} + K_2]
        both have six vertices and four edges, both have line graph
        [K_3 + K_1], and they are not isomorphic.  Their edge DECKS differ
        (deleting the [K_2] edge leaves [K_3 + 3 K_1] against
        [K_{1,3} + 2 K_1]), which is why the premise keeps [same_edge_deck G H]:
        Greenwell rules the exception out with the deck, not with the order
        alone.  (The order equality is then redundant —
        [kelly.same_edge_deck_card_vertex] derives it.)

    The edge therefore stays a CANDIDATE.  It can be re-declared
    [status=conditional external="external_whitney_line_inversion_statement"
    proof=reconstruction_implies_edge_reconstruction] once that external is
    registered in [meta/external_theorems.json] with [kind=theorem] (a file
    outside this package) — noting that the registered claim must cover both
    cited ingredients, Whitney 1932 and Greenwell's 1971 bookkeeping, since the
    Prop bundles them.

    (*@EDGE from=reconstruction_statement to=edge_reconstruction_statement kind=implies status=conditional proof=reconstruction_implies_edge_reconstruction external="external_whitney_line_inversion_statement" cite="gc:e055" note="CONDITIONAL (wave E9 + second reader R1, 2026-09-24): Greenwell 1971 via the edge deck of G = vertex deck of the line graph (kelly.v: same_edge_deck_line, reconstruction_line_diso), conditional on the line-graph inversion external (Whitney 1932 componentwise + Kelly-lemma triangle count for >= 4 edges + isolated-vertex bookkeeping, Hemminger 1969 / Greenwell 1971). The naive Whitney premise without the edge deck is FALSE (K3+K1+K2 vs K1,3+K2)." *)
    -------------------------------------------------------------------------- *)

(** External theorem: H. Whitney, "Congruent graphs and the connectivity of
    graphs", American Journal of Mathematics 54 (1932) 150-168,
    https://doi.org/10.2307/2371086, with the isolated-vertex bookkeeping of
    D. L. Greenwell, "Reconstruction of graphs", Proc. Amer. Math. Soc. 30
    (1971) 431-433.
    Claim: Whitney's theorem says that two CONNECTED graphs with isomorphic line
    graphs are isomorphic, with the single exception of the pair [K_3] /
    [K_{1,3}]; Greenwell's four-edge hypothesis is what rules that exception
    out, and his argument also settles the isolated vertices, which a line graph
    cannot see.  The Prop below states exactly the instance his proof needs, on
    the [sline_graph] of [conjectures.U11]: if [G] has at least four edges, if
    [G] and [H] have the same edge deck, and if [sline_graph G] and
    [sline_graph H] are isomorphic, then [G] and [H] are isomorphic.  The edge
    deck (not merely the order [#|G| = #|H|], which it implies) is part of the
    hypothesis because the order-only reading is FALSE: [K_3 + K_1 + K_2] and
    [K_{1,3} + K_2] have six vertices and four edges each, both have line graph
    [K_3 + K_1], and they are not isomorphic (their edge decks do differ).  This
    Prop is definitionally [kelly.whitney_line_inversion_premise] of
    [foundations.kelly], spelled out here so that the hypothesis of the
    conditional edge is readable in the edge's own file.
    Not formalized here. *)
Definition external_whitney_line_inversion_statement : Prop :=
  forall G H : sgraph, (4 <= #|E(G)|)%N -> same_edge_deck G H ->
    inhabited (sline_graph G ≃ sline_graph H) -> inhabited (G ≃ H).

(** Greenwell's implication, [Qed]-closed on the exact U11 endpoints, with the
    line-graph inversion step as its only (cited, external) hypothesis. *)
Theorem reconstruction_implies_edge_reconstruction :
  external_whitney_line_inversion_statement ->
  reconstruction_statement -> edge_reconstruction_statement.
Proof. exact: whitney_reconstruction_edge_reconstruction. Qed.

(** ** Wave-V vocabulary equivalence (2026-09-24) ************************

    meta/STATEMENT_IMPROVEMENTS.md (section "## reconstruction-theory",
    "### Other") records that the deck vocabulary is defined TWICE in this
    package: [vdel_card] / [same_deck] / [reconstructible] (U11.v, the
    [ell = n-1] case, indexed by VERTICES) and [x21_l_deck_index] /
    [x21_same_l_deck] / [x21_l_reconstructible] (X21.v, indexed by the
    [ell]-element VERTEX SUBSETS).  The ledger names
    [same_deck G H <-> x21_same_l_deck G H #|G|.-1] as the obligation to
    discharge before either family is rewritten in terms of the other.

    It is proved below, under the two hypotheses the identification needs:

      - [0 < #|G|] -- for [#|G| = 0] the X21 side is NOT equivalent.  At
        [ell = #|G|.-1 = 0] the index type [{S : {set K} | #|S| == 0}] is the
        singleton [{set0}] for EVERY [K], so [x21_same_l_deck G H 0] holds for
        every [H] whatsoever, whereas [same_deck G H] still forces a vertex
        bijection [G -> H].  The same collapse happens at [#|G| = 1].  (For
        [2 <= #|G|] the cardinalities are in fact forced -- an [ell]-deck
        bijection needs [C(#|H|, #|G|-1) = #|G|] -- but that counting argument
        is not needed here and is not formalised.)
      - [#|H| = #|G|] -- exactly the hypothesis that [x21_l_reconstructible]
        already carries, so the bridge is directly usable on that side.

    The proof is the bijection [v |-> [set~ v]] between the vertices of a graph
    on [n] vertices and the vertex subsets of cardinality [n-1], transported
    through the deck bijection.  No statement body is changed. *)

Lemma pred_addn1 (n x : nat) : 0 < n -> n.-1 + x = n -> x = 1.
Proof. by move=> n0; rewrite -{2}(prednK n0) -addn1; exact: addnI. Qed.

Lemma vdel_card_setC1 (K : sgraph) (v : K) : vdel_card v = induced [set~ v].
Proof. by rewrite /vdel_card; congr induced; apply/setP => u; rewrite !inE. Qed.

Lemma same_deck_equiv_x21_same_l_deck (G H : sgraph) :
  0 < #|G| -> #|H| = #|G| ->
  (same_deck G H <-> x21_same_l_deck G H #|G|.-1).
Proof.
move=> G0 cardH.
have cG (v : G) : #|[set~ v]| == #|G|.-1 by rewrite cardsC1.
have cH (v : H) : #|[set~ v]| == #|G|.-1 by rewrite cardsC1 cardH.
pose dG (v : G) : x21_l_deck_index G #|G|.-1 := exist _ [set~ v] (cG v).
pose dH (v : H) : x21_l_deck_index H #|G|.-1 := exist _ [set~ v] (cH v).
have exG (S : x21_l_deck_index G #|G|.-1) : exists v : G, val S == [set~ v].
  have cardC : #|~: val S| = 1.
    by move: (cardsC (val S)); rewrite (eqP (valP S)); apply: pred_addn1.
  have /cards1P[v Hv] : #|~: val S| == 1 by rewrite cardC.
  by exists v; rewrite -Hv setCK.
have exH (T : x21_l_deck_index H #|G|.-1) : exists v : H, val T == [set~ v].
  have cardC : #|~: val T| = 1.
    by move: (cardsC (val T)); rewrite (eqP (valP T)) cardH; apply: pred_addn1.
  have /cards1P[v Hv] : #|~: val T| == 1 by rewrite cardC.
  by exists v; rewrite -Hv setCK.
have dGinj : injective dG.
  move=> v w /(congr1 val) /= /setP /(_ v); rewrite !inE eqxx /=.
  by move/esym/negbFE/eqP.
have dHinj : injective dH.
  move=> v w /(congr1 val) /= /setP /(_ v); rewrite !inE eqxx /=.
  by move/esym/negbFE/eqP.
pose iG (S : x21_l_deck_index G #|G|.-1) : G := xchoose (exG S).
pose iH (T : x21_l_deck_index H #|G|.-1) : H := xchoose (exH T).
have iGK : cancel dG iG.
  move=> v; symmetry; apply: dGinj; apply/val_inj => /=.
  exact: (eqP (xchooseP (exG (dG v)))).
have iHK : cancel dH iH.
  move=> v; symmetry; apply: dHinj; apply/val_inj => /=.
  exact: (eqP (xchooseP (exH (dH v)))).
have iGK' : cancel iG dG.
  by move=> S; apply/val_inj => /=; symmetry; exact: (eqP (xchooseP (exG S))).
have iHK' : cancel iH dH.
  by move=> T; apply/val_inj => /=; symmetry; exact: (eqP (xchooseP (exH T))).
split=> [[f [fbij fiso]]|[F [Fbij Fiso]]].
- case: fbij => g gf fg.
  exists (fun S => dH (f (iG S))); split.
    exists (fun T => dG (g (iH T))).
      by move=> S; rewrite iHK gf iGK'.
    by move=> T; rewrite iGK fg iHK'.
  move=> S; rewrite (eqP (xchooseP (exG S))).
  by move: (fiso (iG S)); rewrite !vdel_card_setC1.
- case: Fbij => Finv FF FF'.
  exists (fun v => iH (F (dG v))); split.
    exists (fun w => iG (Finv (dH w))).
      by move=> v; rewrite iHK' FF iGK.
    by move=> w; rewrite iGK' FF' iHK.
  move=> v; rewrite !vdel_card_setC1 -[[set~ iH (F (dG v))]](eqP (xchooseP (exH (F (dG v))))).
  by move: (Fiso (dG v)).
Qed.

Print Assumptions same_deck_equiv_x21_same_l_deck.
