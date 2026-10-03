(** * ClassicalLemmas.konig.line_colouring — König's line-colouring theorem

    A bipartite graph of maximum degree at most [D] has its edges partitioned
    into [D] matchings ([line_colouring]).  Everything is stated for an
    arbitrary set [F] of edges of [G] (with [edeg F v], the number of edges of
    [F] at [v], as the degree), which is what the induction on [D] needs: one
    peels off a matching covering every vertex of maximal degree.

    The two ingredients are
      - [Hall_sat]: a one-sided form of Hall's theorem — if the Hall condition
        holds for the subsets of a set [X] contained in one side, some matching
        covers [X] (the library's [Hall] saturates a whole side, so this is
        obtained by applying it to an induced subgraph);
      - [konig.paths2.merge_matching]: two matchings, one covering the
        max-degree vertices of each side, merge into a single matching. *)

(** ** Provenance, sources, and what corresponds to what

    HOW THIS FILE WAS OBTAINED.  It was written with Claude Code (Anthropic),
    model Claude Opus 5, on 15-16 September 2026, as one piece of the
    formalization of Conjecture 1.15 of arXiv:1611.03196 (the X15 milestone of
    packing-theory).  Rocq was driven interactively.  The rocq-mcp-evolve MCP
    server of the LLM4Rocq project,
    https://github.com/LLM4Rocq/rocq-mcp-evolve (Apache-2.0; the opam package
    still carries its former slug LLM4Rocq/rocq-tools), is used throughout this
    repository for that purpose and is gratefully acknowledged; for this file
    its cached project configuration predated the move of classical-lemmas into
    subdirectories, so goals were read instead from a small [rocq repl] harness
    and files recompiled with [rocq c].  Every error that recurred, together
    with the tactic that fixed it, is recorded in tactics-playbook.md at the
    root of the repository.  Nothing is admitted: [Print Assumptions] on the
    results of this file answers "Closed under the global context".

    ESTIMATED TOKEN COST FOR THIS FILE.  Claude Opus 5, 181k tokens, of which
    85k output.  Method: as in necklace/necklace.v — for every assistant
    message of the Claude Code session of 15-16 September 2026, input +
    cache-creation + output tokens (the tokens processed anew, excluding the
    cached conversation that is re-read at each turn), charged to the file the
    message's tool calls were acting on.  The whole X15 phase of that session
    totals 1.86M such tokens, 0.82M of them output, plus one context rebuild
    charged to no file.

    SOURCES.

      [AABCKLZ16]  R. Aharoni, N. Alon, E. Berger, M. Chudnovsky, D. Kotlar,
             M. Loebl, R. Ziv, "Fair representation by independent sets",
             arXiv:1611.03196.  Conjecture 1.15 is the target of this
             development; it is stated in
             packing-theory/theories/conjectures/X15.v.

      [LLM]  The proof sketch attacked here,
             https://github.com/graph-theory-AI/Graph-Theory-LLM-Proofs/blob/main/attacks/1611.03196__03/output.md
             (five steps: line colouring, Carathéodory, interpolation of two
             matchings, iterated interpolation, trimming), referenced from the
             comment on [bipartite_matching_underrepresentation_llm_statement]
             in X15.v.

      [K1916]  D. König, "Über Graphen und ihre Anwendung auf
             Determinantentheorie und Mengenlehre", Math. Ann. 77 (1916)
             453-465: the edges of a bipartite graph of maximum degree D can be
             coloured with D colours (chi' = Delta).  Proved here by the usual
             induction on D, peeling off one matching that covers every vertex
             of maximum degree.  Hall's theorem is imported from
             coq-graph-theory ([GraphTheory.connectivity.Hall]).

    WHAT CORRESPONDS TO WHAT.

      - [LLM] step 1, "by König's edge-colouring theorem E(G) is the disjoint
        union of Delta(G) matchings M_1, ..., M_Delta"
                                    -> [line_colouring], [line_colouring_E]
      - the matching peeled off at each step, covering every vertex of maximum
        degree on either side: Hall on an induced subgraph, twice, then the
        merge of konig/paths2.v
                                    -> [Hall_sat], [hall_count],
                                       [max_deg_matching]
 *)

From mathcomp Require Import all_boot.
From GraphTheory Require Import preliminaries digraph sgraph connectivity.
From ClassicalLemmas Require Import konig.paths2.
From GTBase Require Import incidence.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Edges at a vertex, and the graph with a prescribed edge set *)

Definition edeg (G : sgraph) (F : {set {set G}}) (v : G) : nat :=
  incidence_degree F v.

Lemma set2C (T : finType) (x y : T) : [set x; y] = [set y; x].
Proof. by apply/setP => z; rewrite !inE orbC. Qed.

Section SubEdges.
Variables (G : sgraph) (F : {set {set G}}).

Definition se_rel : rel G := [rel x y | (x != y) && ([set x; y] \in F)].

Lemma se_sym : symmetric se_rel.
Proof. by move=> x y; rewrite /se_rel /= eq_sym set2C. Qed.

Lemma se_irrefl : irreflexive se_rel.
Proof. by move=> x; rewrite /se_rel /= eqxx. Qed.

Definition sub_edges : sgraph := SGraph se_sym se_irrefl.

Lemma sub_edgesE (x y : sub_edges) : (x -- y) = (x != y) && ([set x; y] \in F).
Proof. by rewrite /edge_rel /= /se_rel. Qed.

Hypothesis subF : F \subset E(G).

Lemma edges_sub_edges : E(sub_edges) = F.
Proof.
apply/setP => e; apply/idP/idP.
  by case/edgesP => x [y [-> /andP[_ h]]].
move=> heF; have he : e \in E(G) by exact: (subsetP subF).
case/edgesP: (he) => x [y [hexy xy]].
apply/edgesP; exists x, y; split=> //.
by rewrite sub_edgesE -hexy heF andbT (sg_edgeNeq xy).
Qed.

Lemma opn_sub_edges (v : G) : #|N(sub_edges; v)| = edeg F v.
Proof.
have hinj : {in N(sub_edges; v) &, injective (fun w : G => [set v; w])}.
  move=> w1 w2 h1 _ /= h12; rewrite inE in h1.
  have : w1 \in [set v; w2] by rewrite -h12 set22.
  rewrite !inE => /orP[/eqP hw|/eqP//].
  by move: (sg_edgeNeq h1); rewrite hw eqxx.
rewrite -(card_in_imset hinj) /edeg; apply: eq_card => e; rewrite !inE.
apply/imsetP/idP.
  move=> [w hw ->]; rewrite inE sub_edgesE in hw.
  by move: hw => /andP[_ ->]; rewrite set21.
move=> /andP[heF hv]; have he : e \in E(G) by exact: (subsetP subF).
case/edgesP: (he) => x [y [hexy xy]].
move: hv; rewrite hexy !inE => /orP[/eqP hvx|/eqP hvy].
  exists y; last by rewrite hvx.
  by rewrite inE sub_edgesE hvx (sg_edgeNeq xy) /= -hexy heF.
exists x; last by rewrite hvy set2C.
by rewrite inE sub_edgesE hvy eq_sym (sg_edgeNeq xy) /= set2C -hexy heF.
Qed.

End SubEdges.

(** ** A one-sided Hall theorem

    The library's [Hall] saturates a whole side of the bipartition; we need to
    saturate only a subset [X] of one side, under the Hall condition for the
    subsets of [X].  Apply [Hall] to the subgraph induced by [X] together with
    the whole other side, and transport the matching back. *)

Section HallSat.
Variables (H : sgraph) (f : H -> bool) (X : {set H}).
Hypothesis bipf : forall x y : H, x -- y -> f x != f y.
Hypothesis Xtrue : forall v : H, v \in X -> f v.
Hypothesis hallX : forall S : {set H}, S \subset X -> #|S| <= #|NS(S)|.

Let S0 : {set H} := X :|: [set v | ~~ f v].
Let H' : sgraph := induced S0.

Lemma mem_S0 (v : H) : ~~ f v -> v \in S0.
Proof. by move=> h; rewrite !inE h orbT. Qed.

Lemma valE_H' (x : H') : val x \in S0.
Proof. exact: valP. Qed.

Lemma Hall_sat :
  exists M : {set {set H}},
    matching M /\ forall v : H, v \in X -> exists2 e, e \in M & v \in e.
Proof.
pose A : {set H'} := [set x : H' | f (val x)].
have bipA : bipartition A.
  move=> x y; rewrite induced_edge => hxy; rewrite !inE.
  by move: (bipf hxy); case: (f (val x)); case: (f (val y)).
have hallA : forall T : {set H'}, T \subset A -> #|T| <= #|NS(T)|.
  move=> T hT.
  have hsub : ((val : H' -> H) @: T) \subset X.
    apply/subsetP => u /imsetP[x hx ->].
    have hfx : f (val x) by move: (subsetP hT _ hx); rewrite inE.
    by move: (valE_H' x); rewrite !inE hfx orbF.
  have hcard : #|(val : H' -> H) @: T| = #|T| by apply: card_imset; exact: val_inj.
  have hcard2 : #|(val : H' -> H) @: NS(T)| = #|NS(T)|.
    by apply: card_imset; exact: val_inj.
  rewrite -hcard -hcard2.
  apply: leq_trans (hallX hsub) _.
  apply: subset_leq_card; apply/subsetP => w /bigcupP[u hu hw].
  rewrite in_opn in hw.
  have hfu : f u by apply: Xtrue; exact: (subsetP hsub _ hu).
  have hfw : ~~ f w by move: (bipf hw); rewrite hfu; case: (f w).
  have hwS : w \in S0 by exact: mem_S0.
  case/imsetP: hu => x hx hux.
  apply/imsetP; exists (Sub w hwS : H') => //.
  apply/bigcupP; exists x => //.
  by rewrite in_opn induced_edge /= -hux.
have [M' [mM' covA]] := Hall bipA hallA.
pose vmap := fun (e : {set H'}) => (val : H' -> H) @: e.
pose M : {set {set H}} := [set vmap e | e in M'].
have himset2 (x y : H') : (val : H' -> H) @: [set x; y] = [set val x; val y].
  by rewrite imsetU1 imset_set1.
exists M; split.
  split.
    move=> e /imsetP[e' he' ->].
    case: mM' => hsub _; case/edgesP: (hsub _ he') => x [y [-> hxy]].
    by rewrite /vmap himset2; apply/edgesP; exists (val x), (val y); rewrite -induced_edge.
  move=> e1 e2 /imsetP[f1 hf1 ->] /imsetP[f2 hf2 ->] w; rewrite /vmap.
  move=> /imsetP[x1 hx1 hw1] /imsetP[x2 hx2 hw2].
  have hx12 : x1 = x2 by apply: val_inj; rewrite -hw1 -hw2.
  by case: mM' => _ hu; rewrite (hu _ _ hf1 hf2 x1) // hx12.
move=> v hv.
have hvS : v \in S0 by rewrite !inE hv.
have hvA : (Sub v hvS : H') \in A by rewrite inE /= (Xtrue hv).
have /bigcupP[e he hve] := subsetP covA _ hvA.
exists ((val : H' -> H) @: e); first by apply/imsetP; exists e.
by apply/imsetP; exists (Sub v hvS : H').
Qed.

End HallSat.

(** ** The Hall condition at the vertices of maximal degree *)

Lemma hall_count (H : sgraph) (D : nat) (X S : {set H}) :
  0 < D -> (forall v : H, #|N(v)| <= D) ->
  (forall v : H, v \in X -> #|N(v)| = D) ->
  S \subset X -> #|S| <= #|NS(S)|.
Proof.
move=> D0 hmax hX hS.
suff h : D * #|S| <= D * #|NS(S)| by rewrite leq_pmul2l in h.
have e1 : \sum_(v in S) #|N(v)| = D * #|S|.
  rewrite (eq_bigr (fun _ => D)); first by rewrite sum_nat_const mulnC.
  by move=> v hv; apply: hX; exact: (subsetP hS).
rewrite -e1.
rewrite (eq_bigr (fun v : H => \sum_(w in N(v)) 1)); last first.
  by move=> v _; rewrite sum1_card.
rewrite (exchange_big_dep (fun w => w \in NS(S))); last first.
  by move=> v w hv hw; apply/bigcupP; exists v.
rewrite [D * #|NS(S)|]mulnC -[X in _ <= X]sum_nat_const.
apply: leq_sum => w hw.
rewrite sum1dep_card.
apply: leq_trans (hmax w); apply: subset_leq_card.
by apply/subsetP => v; rewrite !inE => /andP[_]; rewrite sgP.
Qed.

(** ** A matching covering every vertex of maximal degree *)

Section MaxDeg.
Variables (G : sgraph) (f : G -> bool) (F : {set {set G}}) (D : nat).
Hypothesis bipf : forall x y : G, x -- y -> f x != f y.
Hypothesis subF : F \subset E(G).
Hypothesis D0 : 0 < D.
Hypothesis hmax : forall v : G, edeg F v <= D.

Let H : sgraph := sub_edges F.

Lemma H_bipf (x y : H) : x -- y -> f x != f y.
Proof.
rewrite sub_edgesE => /andP[hne hF].
by apply: bipf; rewrite -in_edges; exact: (subsetP subF _ hF).
Qed.

Lemma H_deg (v : H) : #|N(H; v)| <= D.
Proof. by rewrite (opn_sub_edges subF). Qed.

Lemma matching_of_H (M : {set {set G}}) : @matching H M -> matching M /\ M \subset F.
Proof.
case=> h1 h2; split; last first.
  by apply/subsetP => e /h1; rewrite (edges_sub_edges subF).
split=> // e /h1; rewrite (edges_sub_edges subF) => he.
exact: (subsetP subF).
Qed.

Theorem max_deg_matching :
  exists M : {set {set G}},
    [/\ M \subset F, matching M &
        forall v : G, edeg F v = D -> exists2 e : {set G}, e \in M & v \in e].
Proof.
pose Xt : {set H} := [set v : H | f v && (edeg F v == D)].
pose Xf : {set H} := [set v : H | ~~ f v && (edeg F v == D)].
have hXt : forall v : H, v \in Xt -> #|N(H; v)| = D.
  by move=> v; rewrite inE (opn_sub_edges subF) => /andP[_ /eqP].
have hXf : forall v : H, v \in Xf -> #|N(H; v)| = D.
  by move=> v; rewrite inE (opn_sub_edges subF) => /andP[_ /eqP].
have hXt_f : forall v : H, v \in Xt -> f v by move=> v; rewrite inE => /andP[].
have hXf_f : forall v : H, v \in Xf -> ~~ f v by move=> v; rewrite inE => /andP[].
have hbipf' : forall x y : H, x -- y -> ~~ f x != ~~ f y.
  by move=> x y /H_bipf; case: (f x); case: (f y).
have [M1 [mM1 covM1]] :=
  @Hall_sat H f Xt H_bipf hXt_f (fun S hS => hall_count D0 H_deg hXt hS).
have [M2 [mM2 covM2]] :=
  @Hall_sat H (fun v : H => ~~ f v) Xf hbipf' hXf_f
    (fun S hS => hall_count D0 H_deg hXf hS).
have [hM hsub] := matching_of_H (@merge_matching H f H_bipf M1 M2 mM1 mM2).
exists (merge f M1 M2); split=> // v hv.
case: (boolP (f v)) => hfv.
  have hvXt : v \in Xt by rewrite inE hfv hv eqxx.
  have [e heM hve] := covM1 _ hvXt.
  exact: (@merge_cover_true H f H_bipf M1 M2 mM1 mM2 v e hfv heM hve).
have hvXf : v \in Xf by rewrite inE hfv hv eqxx.
have [e heM hve] := covM2 _ hvXf.
exact: (@merge_cover_false H f H_bipf M1 M2 mM1 mM2 v e hfv heM hve).
Qed.

End MaxDeg.

(** ** König's line-colouring theorem *)

Lemma matching0 (G : sgraph) : matching (set0 : {set {set G}}).
Proof. by split=> [e|e1 e2]; rewrite ?inE. Qed.

Lemma matching_sub (G : sgraph) (M M' : {set {set G}}) :
  M' \subset M -> matching M -> matching M'.
Proof.
move=> hs [h1 h2]; split=> [e /(subsetP hs)/h1//|].
move=> e1 e2 he1 he2 x hx1 hx2.
by apply: (h2 _ _ (subsetP hs _ he1) (subsetP hs _ he2) x).
Qed.

Lemma edeg_le1 (G : sgraph) (M : {set {set G}}) (v : G) :
  matching M -> edeg M v <= 1.
Proof.
case=> _ hu; rewrite /edeg; apply/card_le1_eqP => e1 e2.
by rewrite !inE => /andP[h1 hv1] /andP[h2 hv2]; exact: (hu _ _ h2 h1 v hv2 hv1).
Qed.

Lemma edeg_gt0 (G : sgraph) (F : {set {set G}}) (v : G) (e : {set G}) :
  e \in F -> v \in e -> 0 < edeg F v.
Proof.
by move=> heF hv; rewrite /edeg; apply/card_gt0P; exists e; rewrite !inE heF hv.
Qed.

Lemma edeg_eq1 (G : sgraph) (M : {set {set G}}) (v : G) (e : {set G}) :
  matching M -> e \in M -> v \in e -> edeg M v = 1.
Proof.
move=> hM heM hv; apply/eqP; rewrite eqn_leq (edeg_le1 v hM) /=.
exact: (edeg_gt0 heM hv).
Qed.

Lemma edeg_setD (G : sgraph) (F M : {set {set G}}) (v : G) :
  M \subset F -> edeg (F :\: M) v = edeg F v - edeg M v.
Proof.
move=> hs; rewrite /edeg /incidence_degree.
have hEq : [set e in F :\: M | v \in e] =
           [set e in F | v \in e] :\: [set e in M | v \in e].
  apply/setP => e; rewrite !inE.
  by case: (v \in e); rewrite ?andbF ?andbT //=; case: (e \in M); case: (e \in F).
rewrite hEq cardsD.
have -> : [set e in F | v \in e] :&: [set e in M | v \in e]
        = [set e in M | v \in e].
  apply/setIidPr; apply/subsetP => e.
  by rewrite !inE => /andP[hM ->]; rewrite (subsetP hs).
by [].
Qed.

Theorem line_colouring (G : sgraph) (f : G -> bool) :
  (forall x y : G, x -- y -> f x != f y) ->
  forall (D : nat) (F : {set {set G}}), F \subset E(G) ->
  (forall v : G, edeg F v <= D) ->
  exists col : {set G} -> nat,
    (forall e : {set G}, e \in F -> col e < D) /\
    (forall j : nat, matching [set e in F | col e == j]).
Proof.
move=> bipf; elim=> [|D IH] F subF hdeg.
  have hF0 : F = set0.
    apply/setP => e; rewrite inE; apply/negbTE/negP => heF.
    have he : e \in E(G) by exact: (subsetP subF).
    case/edgesP: he => x [y [hexy _]].
    have hx : x \in e by rewrite hexy !inE eqxx.
    by move: (hdeg x); rewrite leqn0 => /eqP h0; move: (edeg_gt0 heF hx); rewrite h0.
  exists (fun _ => 0); split=> [e|j]; first by rewrite hF0 inE.
  by rewrite hF0; apply: (matching_sub _ (matching0 G)); apply/subsetP => e; rewrite !inE.
have [M [hMF hM hMcov]] := @max_deg_matching G f F D.+1 bipf subF (ltn0Sn D) hdeg.
have subF' : (F :\: M) \subset E(G).
  by apply: subset_trans subF; apply/subsetP => e; rewrite inE => /andP[].
have hdeg' : forall v : G, edeg (F :\: M) v <= D.
  move=> v; rewrite (edeg_setD v hMF).
  case: (boolP (edeg M v == 0)) => [/eqP h0|hn0].
    have : edeg F v != D.+1.
      apply/negP => /eqP hD; have [e heM hve] := hMcov v hD.
      by move: h0; rewrite (edeg_eq1 hM heM hve).
    by rewrite h0 subn0; move: (hdeg v); rewrite leq_eqVlt => /orP[/eqP->|]; rewrite ?eqxx ?ltnS.
  have h1 : edeg M v = 1.
    by apply/eqP; rewrite eqn_leq (edeg_le1 v hM) lt0n hn0.
  have hv0 : 0 < edeg F v.
    move: hn0; rewrite /edeg -lt0n => /card_gt0P[e]; rewrite !inE => /andP[heM hve].
    by apply: (edeg_gt0 (subsetP hMF _ heM) hve).
  by rewrite h1 subn1 -ltnS prednK //; exact: hdeg.
have [col' [hbound hmatch]] := IH _ subF' hdeg'.
exists (fun e => if e \in M then D else col' e); split=> [e heF|j].
  case: (boolP (e \in M)) => heM //.
  by apply: ltnW; apply: hbound; rewrite inE heM heF.
case: (j =P D) => [->|hjD].
  have -> : [set e in F | (if e \in M then D else col' e) == D] = M.
    apply/setP => e; rewrite !inE; case: (boolP (e \in M)) => heM /=.
      by rewrite eqxx andbT (subsetP hMF).
    case: (boolP (e \in F)) => heF /=; last by [].
    by apply/negbTE; apply/negP => /eqP hcol; move: (hbound e); rewrite inE heM heF hcol ltnn => /(_ isT).
  exact: hM.
have -> : [set e in F | (if e \in M then D else col' e) == j] =
          [set e in F :\: M | col' e == j].
  apply/setP => e; rewrite !inE; case: (boolP (e \in M)) => heM /=.
    have /negbTE -> : D != j by apply/eqP => hDj; apply: hjD; rewrite hDj.
    by rewrite andbF.
  by [].
exact: hmatch.
Qed.

(** The form used downstream: the edges of a bipartite graph of maximum degree
    at most [D] are coloured with [D] colours, each colour class a matching. *)

Lemma edeg_E (G : sgraph) (v : G) : edeg E(G) v = #|N(v)|.
Proof.
rewrite -(opn_sub_edges (subxx E(G)) v); apply: eq_card => w.
rewrite !in_opn sub_edgesE (@in_edges G v w) !inE andb_idl // => hvw.
by rewrite (sg_edgeNeq hvw).
Qed.

Corollary line_colouring_E (G : sgraph) (f : G -> bool) (D : nat) :
  (forall x y : G, x -- y -> f x != f y) ->
  (forall v : G, #|N(v)| <= D) ->
  exists col : {set G} -> nat,
    (forall e : {set G}, e \in E(G) -> col e < D) /\
    (forall j : nat, matching [set e in E(G) | col e == j]).
Proof.
move=> bipf hdeg; apply: (line_colouring bipf (subxx _)) => v.
by rewrite edeg_E.
Qed.

Print Assumptions line_colouring.
Print Assumptions line_colouring_E.
