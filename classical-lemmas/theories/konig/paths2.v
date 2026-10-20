(** * ClassicalLemmas.konig.paths2 — the union of two matchings in a bipartite graph

    Two matchings [A] and [B] of a graph [G] with bipartition [f] meet every
    vertex at most once each, so the "share a vertex" relation on the symmetric
    difference [SS = (A \ B) u (B \ A)] has degree at most two.  Using the
    bipartition one can *orient* that relation: [nxt e] is the edge of the other
    matching that meets [e] at its [f]-true endpoint when [e in A \ B], at its
    [f]-false endpoint when [e in B \ A] ([set0] when there is none).  Then

      - [nxt] is injective where it is defined ([nxt_inj]), and
      - two distinct meeting edges are always related by [nxt] ([meetP]).

    So the components of the union are the chains of the partial injection
    [nxt]: paths and (even) cycles.  Two clients use this:

      - [konig.line_colouring] merges two matchings into one saturating all the
        max-degree vertices, by selecting along each chain the edges lying on
        the same side as the chain's last edge;
      - [Packing.foundations.fair_matching] linearises [SS] into a necklace, as the orbits of
        a permutation [sigma] extending [nxt]. *)

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

    ESTIMATED TOKEN COST FOR THIS FILE.  Claude Opus 5, 134k tokens, of which
    55k output.  Method: as in necklace/necklace.v — for every assistant
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

      No literature source: this file is infrastructure.  The fact that the
      union of two matchings is a disjoint union of paths and even cycles is
      folklore (it underlies both König's theorem and Berge's augmenting-path
      theorem); nothing comparable was available in coq-graph-theory or in this
      repository, and the orientation by the bipartition, which turns it into a
      partial injection, is what makes it usable in Rocq without any path
      combinatorics.

    WHAT CORRESPONDS TO WHAT.

      - "two matchings meet every vertex at most once each, so their union has
        degree at most two, and in a bipartite graph the two edges at a vertex
        can be oriented consistently"
                                    -> [nxt], [nxt_inj], [meetP]
      - "hence the union is a disjoint union of paths and even cycles"
                                    -> [sigma] (the closure of [nxt] to a
                                       permutation), [blocks], [bl],
                                       [mem_bl], [uniq_bl], [block_nth]
      - "one may pick from each component a matching covering all its
        degree-critical vertices" (used by konig/line_colouring.v)
                                    -> [sel], [Tsel], [Tsel_indep],
                                       [merge], [merge_matching],
                                       [merge_cover_true], [merge_cover_false]
 *)

From mathcomp Require Import all_boot.
From GraphTheory Require Import preliminaries digraph sgraph connectivity.
Set SsrOldRewriteGoalsOrder.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section TwoMatchings.
Variables (G : sgraph) (f : G -> bool).
Hypothesis bipf : forall x y : G, x -- y -> f x != f y.
Variables (A B : {set {set G}}).
Hypothesis mA : matching A.
Hypothesis mB : matching B.

Definition SA : {set {set G}} := A :\: B.
Definition SB : {set {set G}} := B :\: A.
Definition SS : {set {set G}} := SA :|: SB.

(** The endpoints of [e], as singletons, split by the bipartition. *)
Definition tvx (e : {set G}) : {set G} := [set x in e | f x].
Definition fvx (e : {set G}) : {set G} := [set x in e | ~~ f x].

Lemma edge_neq0 (e : {set G}) : e \in E(G) -> e != set0.
Proof.
case/edgesP => x [y [-> _]]; apply/eqP/eqP.
by apply/set0Pn; exists x; rewrite !inE eqxx.
Qed.

Lemma edge_side (e : {set G}) (u w : G) :
  e \in E(G) -> u \in e -> w \in e -> f u = f w -> u = w.
Proof.
case/edgesP => x [y [-> xy]]; rewrite !inE.
by move=> /orP[/eqP->|/eqP->] /orP[/eqP->|/eqP->] // hf; move: (bipf xy); rewrite hf eqxx.
Qed.

Lemma tvxE (e : {set G}) (v : G) : e \in E(G) -> v \in e -> f v -> tvx e = [set v].
Proof.
move=> he hv fv; apply/setP => z; rewrite !inE.
apply/idP/idP => [/andP[hz fz]|/eqP->]; last by rewrite hv fv.
by apply/eqP; apply: (edge_side he hz hv); rewrite fz fv.
Qed.

Lemma fvxE (e : {set G}) (v : G) : e \in E(G) -> v \in e -> ~~ f v -> fvx e = [set v].
Proof.
move=> he hv fv; apply/setP => z; rewrite !inE.
apply/idP/idP => [/andP[hz fz]|/eqP->]; last by rewrite hv fv.
by apply/eqP; apply: (edge_side he hz hv); rewrite (negbTE fz) (negbTE fv).
Qed.

Lemma tvx_neq0 (e : {set G}) : e \in E(G) -> tvx e != set0.
Proof.
move=> he; case/edgesP: (he) => x [y [hexy xy]].
have fxy : f x != f y by exact: bipf.
apply/set0Pn; case: (boolP (f x)) => fx.
  by exists x; rewrite !inE hexy !inE eqxx fx.
exists y; rewrite !inE hexy !inE eqxx orbT /=.
by move: fxy; rewrite (negbTE fx) => /eqP/nesym/eqP; case: (f y).
Qed.

Lemma fvx_neq0 (e : {set G}) : e \in E(G) -> fvx e != set0.
Proof.
move=> he; case/edgesP: (he) => x [y [hexy xy]].
have fxy : f x != f y by exact: bipf.
apply/set0Pn; case: (boolP (f x)) => fx.
  exists y; rewrite !inE hexy !inE eqxx orbT /=.
  by move: fxy; rewrite fx; case: (f y).
by exists x; rewrite !inE hexy !inE eqxx fx.
Qed.

Lemma tvx_mem (e : {set G}) (v : G) : v \in tvx e -> (v \in e) && f v.
Proof. by rewrite !inE. Qed.

Lemma fvx_mem (e : {set G}) (v : G) : v \in fvx e -> (v \in e) && ~~ f v.
Proof. by rewrite !inE. Qed.

Lemma SA_edge (e : {set G}) : e \in SA -> e \in E(G).
Proof. by rewrite !inE => /andP[_ he]; case: mA => hsub _; exact: hsub. Qed.

Lemma SB_edge (e : {set G}) : e \in SB -> e \in E(G).
Proof. by rewrite !inE => /andP[_ he]; case: mB => hsub _; exact: hsub. Qed.

Lemma SS_edge (e : {set G}) : e \in SS -> e \in E(G).
Proof. by rewrite inE => /orP[/SA_edge|/SB_edge]. Qed.

Lemma SSP (e : {set G}) : e \in SS -> (e \in SA) || (e \in SB).
Proof. by rewrite inE. Qed.

Lemma SA_A (e : {set G}) : e \in SA -> e \in A.
Proof. by rewrite inE => /andP[]. Qed.

Lemma SB_B (e : {set G}) : e \in SB -> e \in B.
Proof. by rewrite inE => /andP[]. Qed.

Lemma mem_SS_A (e : {set G}) : e \in SA -> e \in SS.
Proof. by move=> h; rewrite inE h. Qed.

Lemma mem_SS_B (e : {set G}) : e \in SB -> e \in SS.
Proof. by move=> h; rewrite inE h orbT. Qed.

Lemma SAB0 (e : {set G}) : e \in SA -> e \in SB -> False.
Proof. by rewrite !inE => /andP[h _] /andP[_ h']; rewrite h' in h. Qed.

(** The successor along the union. *)
Definition nxt (e : {set G}) : {set G} :=
  if e \in SA then odflt set0 [pick e' in SB | tvx e' == tvx e]
  else if e \in SB then odflt set0 [pick e' in SA | fvx e' == fvx e]
  else set0.

Lemma nxt_out (e : {set G}) : e \notin SS -> nxt e = set0.
Proof.
rewrite inE negb_or => /andP[hA hB].
by rewrite /nxt (negbTE hA) (negbTE hB).
Qed.

Lemma nxt_SA (e : {set G}) : e \in SA -> nxt e != set0 ->
  (nxt e \in SB) && (tvx (nxt e) == tvx e).
Proof.
move=> he; rewrite /nxt he; case: pickP => [e' /andP[h1 h2] _|_]; last by rewrite eqxx.
by rewrite h1 h2.
Qed.

Lemma nxt_SB (e : {set G}) : e \in SB -> nxt e != set0 ->
  (nxt e \in SA) && (fvx (nxt e) == fvx e).
Proof.
move=> he; have heA : e \notin SA by apply/negP => h; exact: (SAB0 h he).
rewrite /nxt (negbTE heA) he; case: pickP => [e' /andP[h1 h2] _|_]; last by rewrite eqxx.
by rewrite h1 h2.
Qed.

Lemma SS_neq0 (e : {set G}) : e \in SS -> e != set0.
Proof. by move=> /SS_edge/edge_neq0. Qed.

Lemma set0_notin_SS : (set0 : {set G}) \notin SS.
Proof. by apply/negP => /SS_neq0; rewrite eqxx. Qed.

Lemma nxt0 : nxt set0 = set0.
Proof. by apply: nxt_out; exact: set0_notin_SS. Qed.

Lemma nxt_SS (e : {set G}) : nxt e != set0 -> nxt e \in SS.
Proof.
case: (boolP (e \in SS)) => [|/nxt_out-> //]; last by rewrite eqxx.
rewrite inE => /orP[hA|hB] hn.
  by rewrite inE; move: (nxt_SA hA hn) => /andP[-> _]; rewrite orbT.
by rewrite inE; move: (nxt_SB hB hn) => /andP[-> _].
Qed.

Lemma SB_tvx_uniq (e1 e2 : {set G}) : e1 \in SB -> e2 \in SB -> tvx e1 = tvx e2 -> e1 = e2.
Proof.
move=> h1 h2 h12; have he1 := SB_edge h1.
have /set0Pn[v hv] := tvx_neq0 he1.
case: mB => _ huniq; apply: (huniq _ _ _ _ v).
- by move: h1; rewrite !inE => /andP[].
- by move: h2; rewrite !inE => /andP[].
- by move: hv; rewrite inE => /andP[].
- by move: hv; rewrite h12 inE => /andP[].
Qed.

Lemma SA_fvx_uniq (e1 e2 : {set G}) : e1 \in SA -> e2 \in SA -> fvx e1 = fvx e2 -> e1 = e2.
Proof.
move=> h1 h2 h12; have he1 := SA_edge h1.
have /set0Pn[v hv] := fvx_neq0 he1.
case: mA => _ huniq; apply: (huniq _ _ _ _ v).
- by move: h1; rewrite !inE => /andP[].
- by move: h2; rewrite !inE => /andP[].
- by move: hv; rewrite inE => /andP[].
- by move: hv; rewrite h12 inE => /andP[].
Qed.

Lemma SA_tvx_uniq (e1 e2 : {set G}) : e1 \in SA -> e2 \in SA -> tvx e1 = tvx e2 -> e1 = e2.
Proof.
move=> h1 h2 h12; have he1 := SA_edge h1.
have /set0Pn[v hv] := tvx_neq0 he1.
case: mA => _ huniq; apply: (huniq _ _ _ _ v).
- by move: h1; rewrite !inE => /andP[].
- by move: h2; rewrite !inE => /andP[].
- by move: hv; rewrite inE => /andP[].
- by move: hv; rewrite h12 inE => /andP[].
Qed.

Lemma SB_fvx_uniq (e1 e2 : {set G}) : e1 \in SB -> e2 \in SB -> fvx e1 = fvx e2 -> e1 = e2.
Proof.
move=> h1 h2 h12; have he1 := SB_edge h1.
have /set0Pn[v hv] := fvx_neq0 he1.
case: mB => _ huniq; apply: (huniq _ _ _ _ v).
- by move: h1; rewrite !inE => /andP[].
- by move: h2; rewrite !inE => /andP[].
- by move: hv; rewrite inE => /andP[].
- by move: hv; rewrite h12 inE => /andP[].
Qed.

Lemma nxtPA (e e' : {set G}) : e \in SA -> e' \in SB -> tvx e' = tvx e -> nxt e = e'.
Proof.
move=> he he' h; rewrite /nxt he; case: pickP => [e'' /andP[h1 /eqP h2]|hno] /=.
  by apply: SB_tvx_uniq h1 he' _; rewrite h2 h.
by move: (hno e'); rewrite he' h eqxx.
Qed.

Lemma nxtPB (e e' : {set G}) : e \in SB -> e' \in SA -> fvx e' = fvx e -> nxt e = e'.
Proof.
move=> he he' h; have heA : e \notin SA by apply/negP => hh; exact: (SAB0 hh he).
rewrite /nxt (negbTE heA) he; case: pickP => [e'' /andP[h1 /eqP h2]|hno] /=.
  by apply: SA_fvx_uniq h1 he' _; rewrite h2 h.
by move: (hno e'); rewrite he' h eqxx.
Qed.

(** Every adjacency inside [SS] is an [nxt]-step. *)
Lemma meetP (e e' : {set G}) (v : G) :
  e \in SS -> e' \in SS -> e != e' -> v \in e -> v \in e' ->
  (nxt e == e') || (nxt e' == e).
Proof.
move=> /SSP/orP[hA|hA] /SSP/orP[hB|hB] hne hv hv'.
- case/eqP: hne; case: mA => _ huniq; apply: (huniq _ _ _ _ v) => //.
  + exact: SA_A.
  + exact: SA_A.
- case: (boolP (f v)) => fv.
    by rewrite (nxtPA hA hB) ?eqxx // (tvxE (SB_edge hB) hv') // (tvxE (SA_edge hA) hv).
  by rewrite (nxtPB hB hA) ?eqxx ?orbT // (fvxE (SA_edge hA) hv) // (fvxE (SB_edge hB) hv').
- case: (boolP (f v)) => fv.
    by rewrite (nxtPA hB hA) ?eqxx ?orbT // (tvxE (SB_edge hA) hv) // (tvxE (SA_edge hB) hv').
  by rewrite (nxtPB hA hB) ?eqxx // (fvxE (SA_edge hB) hv') // (fvxE (SB_edge hA) hv).
- case/eqP: hne; case: mB => _ huniq; apply: (huniq _ _ _ _ v) => //.
  + exact: SB_B.
  + exact: SB_B.
Qed.

(** [nxt] is injective where defined. *)
Lemma nxt_inj (e1 e2 : {set G}) :
  e1 \in SS -> e2 \in SS -> nxt e1 != set0 -> nxt e1 = nxt e2 -> e1 = e2.
Proof.
move=> /SSP h1 /SSP h2 hn0 heq.
have hn0' : nxt e2 != set0 by rewrite -heq.
case/orP: h1 => h1; case/orP: h2 => h2.
- move: (nxt_SA h1 hn0) (nxt_SA h2 hn0') => /andP[_ /eqP t1] /andP[_ /eqP t2].
  by apply: (SA_tvx_uniq h1 h2); rewrite -t1 -t2 heq.
- move: (nxt_SA h1 hn0) (nxt_SB h2 hn0') => /andP[i1 _] /andP[i2 _].
  by move: i2; rewrite -heq => i2; exfalso; exact: (SAB0 i2 i1).
- move: (nxt_SB h1 hn0) (nxt_SA h2 hn0') => /andP[i1 _] /andP[i2 _].
  by move: i2; rewrite -heq => i2; exfalso; exact: (SAB0 i1 i2).
- move: (nxt_SB h1 hn0) (nxt_SB h2 hn0') => /andP[_ /eqP t1] /andP[_ /eqP t2].
  by apply: (SB_fvx_uniq h1 h2); rewrite -t1 -t2 heq.
Qed.

Lemma nxt_neq (e : {set G}) : e \in SS -> nxt e != e.
Proof.
move=> /SSP/orP[h|h]; apply/negP => /eqP heq.
  case: (boolP (nxt e == set0)) => [/eqP h0|hn0].
    by move: (SS_neq0 (mem_SS_A h)); rewrite -heq h0 eqxx.
  by move: (nxt_SA h hn0) => /andP[i _]; rewrite heq in i; exact: (SAB0 h i).
case: (boolP (nxt e == set0)) => [/eqP h0|hn0].
  by move: (SS_neq0 (mem_SS_B h)); rewrite -heq h0 eqxx.
by move: (nxt_SB h hn0) => /andP[i _]; rewrite heq in i; exact: (SAB0 i h).
Qed.

(** ** Chains of [nxt]: acyclicity, and the alternating selection *)

Lemma iter_nxt0 (n : nat) : iter n nxt set0 = set0.
Proof. by elim: n => [//|n IH]; rewrite iterS IH nxt0. Qed.

Lemma fconnect_set0 (y : {set G}) : fconnect nxt set0 y -> y = set0.
Proof. by move=> h; rewrite -(iter_findex h) iter_nxt0. Qed.

Lemma order_set0 : order nxt set0 = 1.
Proof.
rewrite /order -(card1 (set0 : {set G})); apply: eq_card => y.
by rewrite !inE; apply/idP/idP => [/fconnect_set0->|/eqP->]; rewrite ?eqxx ?connect0.
Qed.

Lemma iter_cycle (e : {set G}) (k m : nat) : iter k nxt e = e -> iter (k * m) nxt e = e.
Proof.
move=> h; elim: m => [|m IH]; first by rewrite muln0.
by rewrite mulnS iterD IH h.
Qed.

Lemma chain_acyclic (e : {set G}) :
  e != set0 -> fconnect nxt e set0 -> ~~ fconnect nxt (nxt e) e.
Proof.
move=> he0 h0; apply/negP => hcyc.
set k := (findex nxt (nxt e) e).+1.
have hk : iter k nxt e = e by rewrite /k iterSr (iter_findex hcyc).
set j := findex nxt e set0.
have hj : iter j nxt e = set0 by rewrite (iter_findex h0).
have hle : j <= k * j by rewrite leq_pmull // ltn0Sn.
have : iter (k * j) nxt e = set0.
  by rewrite -(subnK hle) iterD hj iter_nxt0.
by rewrite (iter_cycle _ hk) => he; rewrite he eqxx in he0.
Qed.

Lemma fconnect_stepE (e y : {set G}) :
  fconnect nxt e y = (y == e) || fconnect nxt (nxt e) y.
Proof.
apply/idP/idP => [/connectP[p]|].
  case: p => [_ ->|z p /= /andP[/eqP hz hp] hy]; first by rewrite eqxx.
  by rewrite -hz in hp hy; apply/orP; right; apply/connectP; exists p.
case/orP => [/eqP->|h]; first exact: connect0.
by apply: connect_trans h; apply: connect1; rewrite /= eqxx.
Qed.

Lemma orderS (e : {set G}) : e != set0 -> fconnect nxt e set0 ->
  order nxt e = (order nxt (nxt e)).+1.
Proof.
move=> he0 h0; rewrite /order.
have hE : fconnect nxt e =i [predU1 e & fconnect nxt (nxt e)].
  by move=> y; rewrite !inE fconnect_stepE.
rewrite (eq_card hE) cardU1.
have /negbTE -> : e \notin fconnect nxt (nxt e) by rewrite inE; exact: chain_acyclic.
by [].
Qed.

(** [cyc e]: the chain through [e] is a cycle (it never reaches [set0]). *)
Definition cyc (e : {set G}) : bool := ~~ fconnect nxt e set0.

Lemma cyc_nxt0 (e : {set G}) : cyc e -> nxt e != set0.
Proof.
by apply: contraNneq => h0; apply: connect1; rewrite /= h0 eqxx.
Qed.

Lemma cyc_step (e : {set G}) : e != set0 -> cyc (nxt e) = cyc e.
Proof.
move=> he0; rewrite /cyc [in RHS]fconnect_stepE eq_sym (negbTE he0) /=.
by [].
Qed.

Lemma SS_side (e : {set G}) : e \in SS -> (e \in SB) = ~~ (e \in SA).
Proof.
move=> /SSP/orP[h|h].
  by rewrite h; apply/negbTE/negP => h'; exact: (SAB0 h h').
by rewrite h; apply/esym/negP => h'; exact: (SAB0 h' h).
Qed.

Lemma nxt_side (e : {set G}) : e \in SS -> nxt e != set0 ->
  (nxt e \in SA) = ~~ (e \in SA).
Proof.
move=> /SSP/orP[h|h] hn.
  rewrite h /=; move: (nxt_SA h hn) => /andP[hi _].
  by apply/negbTE/negP => h'; exact: (SAB0 h' hi).
move: (nxt_SB h hn) => /andP[hi _]; rewrite hi.
by apply/esym; rewrite -(SS_side (mem_SS_B h)) h.
Qed.

(** The alternating selection along the chains: the last edge of a path is
    always selected, and selection alternates at every step. *)
Definition sel (e : {set G}) : bool :=
  if cyc e then e \in SA else ~~ odd (order nxt e).

Lemma sel_end (e : {set G}) : e \in SS -> nxt e = set0 -> sel e.
Proof.
move=> he hn; have he0 : e != set0 by exact: SS_neq0.
have h0 : fconnect nxt e set0 by apply: connect1; rewrite /= hn eqxx.
by rewrite /sel /cyc h0 /= (orderS he0 h0) hn order_set0.
Qed.

Lemma sel_step (e : {set G}) : e \in SS -> nxt e != set0 ->
  sel (nxt e) = ~~ sel e.
Proof.
move=> he hn; have he0 : e != set0 by exact: SS_neq0.
rewrite /sel (cyc_step he0); case: (boolP (cyc e)) => hc.
  by rewrite (nxt_side he hn).
rewrite (orderS he0) ?negbK //; by move: hc; rewrite /cyc negbK.
Qed.

Definition Tsel : {set {set G}} := [set e in SS | sel e].

Lemma TselP (e : {set G}) : (e \in Tsel) = (e \in SS) && sel e.
Proof. by rewrite inE. Qed.

Lemma Tsel_sub : Tsel \subset SS.
Proof. by apply/subsetP => e; rewrite TselP => /andP[]. Qed.

Lemma Tsel_indep (e : {set G}) : e \in SS -> e \in Tsel -> nxt e \notin Tsel.
Proof.
move=> he; rewrite !TselP he /= => hs; apply/negP => /andP[hi hsn].
have hn : nxt e != set0 by apply: SS_neq0.
by move: hsn; rewrite (sel_step he hn) hs.
Qed.

Lemma Tsel_dom (e : {set G}) : e \in SS -> (e \in Tsel) || (nxt e \in Tsel).
Proof.
move=> he; rewrite !TselP he /=; case: (boolP (sel e)) => //= hs.
have hn : nxt e != set0.
  by apply/negP => /eqP h0; move: hs; rewrite (sel_end he h0).
by rewrite (nxt_SS hn) /= (sel_step he hn) (negbTE hs).
Qed.

(** ** Merging two matchings

    One matching covering every [f]-true vertex covered by [A] and every
    [f]-false vertex covered by [B]. *)

Definition merge : {set {set G}} := (A :&: B) :|: Tsel.

Lemma mergeP (e : {set G}) : (e \in merge) = (e \in A :&: B) || (e \in Tsel).
Proof. by rewrite inE. Qed.

Lemma merge_sub : merge \subset A :|: B.
Proof.
apply/subsetP => e; rewrite mergeP => /orP[he|he].
  by move: he; rewrite !inE => /andP[hA _]; rewrite hA.
move: he; rewrite TselP => /andP[/SSP/orP[hs|hs] _].
  by rewrite inE (SA_A hs).
by rewrite inE (SB_B hs) orbT.
Qed.

Lemma merge_matching : matching merge.
Proof.
split.
  move=> e; rewrite mergeP => /orP[|].
    by rewrite inE => /andP[hA _]; case: mA => hs _; exact: (hs _ hA).
  by rewrite TselP => /andP[/SS_edge he _].
have hT : forall e, e \in merge -> e \notin A -> (e \in SB) && (e \in Tsel).
  move=> e; rewrite mergeP => /orP[|hTe].
    by rewrite inE => /andP[hA _]; rewrite hA.
  move=> hnA; rewrite hTe andbT.
  move: hTe; rewrite TselP => /andP[/SSP/orP[hs|hs] _] //.
  by move: hnA; rewrite (SA_A hs).
have hT' : forall e, e \in merge -> e \notin B -> (e \in SA) && (e \in Tsel).
  move=> e; rewrite mergeP => /orP[|hTe].
    by rewrite inE => /andP[_ hB]; rewrite hB.
  move=> hnB; rewrite hTe andbT.
  move: hTe; rewrite TselP => /andP[/SSP/orP[hs|hs] _] //.
  by move: hnB; rewrite (SB_B hs).
move=> e1 e2 h1 h2 v hv1 hv2.
case: (e1 =P e2) => // hne.
have hne1 : e1 != e2 by apply/eqP.
have hne2 : e2 != e1 by rewrite eq_sym.
have hcross : forall e1' e2', e1' \in SA -> e1' \in Tsel -> e2' \in SB -> e2' \in Tsel ->
    e1' != e2' -> v \in e1' -> v \in e2' -> False.
  move=> e1' e2' hs1 ht1 hs2 ht2 hn hw1 hw2.
  case/orP: (meetP (mem_SS_A hs1) (mem_SS_B hs2) hn hw1 hw2) => /eqP hnx.
    by move: (Tsel_indep (mem_SS_A hs1) ht1); rewrite hnx ht2.
  by move: (Tsel_indep (mem_SS_B hs2) ht2); rewrite hnx ht1.
case: (boolP (e1 \in A)) => hA1; case: (boolP (e2 \in A)) => hA2.
- by case: mA => _ hu; apply: (hu _ _ _ _ v).
- move: (hT _ h2 hA2) => /andP[hs2 ht2].
  case: (boolP (e1 \in B)) => hB1.
    by case: mB => _ hu; apply: (hu _ _ _ _ v) => //; exact: (SB_B hs2).
  move: (hT' _ h1 hB1) => /andP[hs1 ht1].
  by case: (hcross e1 e2 hs1 ht1 hs2 ht2 hne1 hv1 hv2).
- move: (hT _ h1 hA1) => /andP[hs1 ht1].
  case: (boolP (e2 \in B)) => hB2.
    by case: mB => _ hu; apply: (hu _ _ _ _ v) => //; exact: (SB_B hs1).
  move: (hT' _ h2 hB2) => /andP[hs2 ht2].
  by case: (hcross e2 e1 hs2 ht2 hs1 ht1 hne2 hv2 hv1).
- move: (hT _ h1 hA1) => /andP[hs1 ht1]; move: (hT _ h2 hA2) => /andP[hs2 ht2].
  by case: mB => _ hu; apply: (hu _ _ _ _ v) => //; exact: SB_B.
Qed.

Lemma merge_cover_true (v : G) (e : {set G}) :
  f v -> e \in A -> v \in e -> exists2 e', e' \in merge & v \in e'.
Proof.
move=> fv heA hv; case: (boolP (e \in B)) => heB.
  by exists e => //; rewrite mergeP inE heA heB.
have hs : e \in SA by rewrite inE heB heA.
have he : e \in E(G) by exact: SA_edge.
case/orP: (Tsel_dom (mem_SS_A hs)) => ht.
  by exists e => //; rewrite mergeP ht orbT.
have hn0 : nxt e != set0.
  by apply: SS_neq0; move: ht; rewrite TselP => /andP[].
exists (nxt e); first by rewrite mergeP ht orbT.
move: (nxt_SA hs hn0) => /andP[_ /eqP htv].
have : v \in tvx (nxt e) by rewrite htv (tvxE he hv fv) inE eqxx.
by rewrite inE => /andP[].
Qed.

Lemma merge_cover_false (v : G) (e : {set G}) :
  ~~ f v -> e \in B -> v \in e -> exists2 e', e' \in merge & v \in e'.
Proof.
move=> fv heB hv; case: (boolP (e \in A)) => heA.
  by exists e => //; rewrite mergeP inE heA heB.
have hs : e \in SB by rewrite inE heA heB.
have he : e \in E(G) by exact: SB_edge.
case/orP: (Tsel_dom (mem_SS_B hs)) => ht.
  by exists e => //; rewrite mergeP ht orbT.
have hn0 : nxt e != set0.
  by apply: SS_neq0; move: ht; rewrite TselP => /andP[].
exists (nxt e); first by rewrite mergeP ht orbT.
move: (nxt_SB hs hn0) => /andP[_ /eqP htv].
have : v \in fvx (nxt e) by rewrite htv (fvxE he hv fv) inE eqxx.
by rewrite inE => /andP[].
Qed.

(** ** Linearising the union of the two matchings

    [nxt] is a partial injection of [SS]; extending it by an arbitrary
    bijection from the chain ends to the chain starts gives a permutation
    [sigma] of the whole type, which fixes everything outside [SS].  The
    orbits of [sigma] then cut [SS] into blocks, each of which is a cyclic
    [sigma]-chain; every adjacency of [SS] is an [nxt]-step, hence a step
    inside one block. *)

Definition dom : {set {set G}} := [set e in SS | nxt e != set0].
Definition img : {set {set G}} := [set nxt e | e in dom].
Definition Sd : {set {set G}} := SS :\: dom.
Definition Si : {set {set G}} := SS :\: img.

Lemma domP (e : {set G}) : (e \in dom) = (e \in SS) && (nxt e != set0).
Proof. by rewrite inE. Qed.

Lemma dom_sub : dom \subset SS.
Proof. by apply/subsetP => e; rewrite domP => /andP[]. Qed.

Lemma img_sub : img \subset SS.
Proof.
apply/subsetP => e /imsetP[e' he' ->].
by apply: nxt_SS; move: he'; rewrite domP => /andP[].
Qed.

Lemma card_dom_img : #|img| = #|dom|.
Proof.
apply: card_in_imset => e1 e2; rewrite !domP => /andP[h1 hn1] /andP[h2 _].
exact: nxt_inj.
Qed.

Lemma card_Sd_Si : #|Sd| = #|Si|.
Proof.
rewrite /Sd /Si !cardsD.
have -> : SS :&: dom = dom by apply/setIidPr; exact: dom_sub.
have -> : SS :&: img = img by apply/setIidPr; exact: img_sub.
by rewrite card_dom_img.
Qed.

Lemma Sd_SS (e : {set G}) : e \in Sd -> e \in SS.
Proof. by rewrite inE => /andP[]. Qed.

Lemma Sd_in (e : {set G}) : e \in SS -> nxt e = set0 -> e \in Sd.
Proof. by move=> h1 h2; rewrite inE h1 andbT domP h2 eqxx andbF. Qed.

Definition beta (e : {set G}) : {set G} := nth set0 (enum Si) (index e (enum Sd)).

Lemma beta_Si (e : {set G}) : e \in Sd -> beta e \in Si.
Proof.
move=> he; rewrite /beta -mem_enum; apply: mem_nth.
rewrite -cardE -card_Sd_Si cardE index_mem mem_enum //.
Qed.

Lemma beta_inj : {in Sd &, injective beta}.
Proof.
move=> e1 e2 h1 h2; rewrite /beta => hb.
have hlt (e : {set G}) : e \in Sd -> index e (enum Sd) < size (enum Si).
  by move=> he; rewrite -cardE -card_Sd_Si cardE index_mem mem_enum.
have := nth_uniq set0 (hlt _ h1) (hlt _ h2) (enum_uniq (mem Si)).
rewrite hb eqxx => /esym/eqP hidx.
by rewrite -(nth_index set0 (_ : e1 \in enum Sd)) ?mem_enum // hidx nth_index ?mem_enum.
Qed.

Definition sigma (e : {set G}) : {set G} :=
  if nxt e != set0 then nxt e else if e \in Sd then beta e else e.

Lemma sigma_nxt (e : {set G}) : nxt e != set0 -> sigma e = nxt e.
Proof. by rewrite /sigma => ->. Qed.

Lemma sigma_out (e : {set G}) : e \notin SS -> sigma e = e.
Proof.
move=> he; rewrite /sigma nxt_out // eqxx /=.
have -> : (e \in Sd) = false.
  by apply/negbTE/negP => /Sd_SS hSS; rewrite hSS in he.
by [].
Qed.

Lemma sigma_SS (e : {set G}) : e \in SS -> sigma e \in SS.
Proof.
move=> he; rewrite /sigma; case: (boolP (nxt e != set0)) => [hn|hn].
  exact: nxt_SS.
have hSd : e \in Sd by apply: Sd_in => //; move: hn; rewrite negbK => /eqP.
by rewrite hSd; move: (beta_Si hSd); rewrite inE => /andP[].
Qed.

Lemma sigma_inj : injective sigma.
Proof.
have key (e : {set G}) : nxt e != set0 -> e \in SS.
  by apply: contraTT => he; rewrite nxt_out // eqxx.
have keySd (e : {set G}) : e \in SS -> nxt e = set0 -> e \in Sd by apply: Sd_in.
move=> e1 e2; rewrite /sigma.
case: (boolP (nxt e1 != set0)) => hn1; case: (boolP (nxt e2 != set0)) => hn2.
- by move=> h; apply: (nxt_inj (key _ hn1) (key _ hn2) hn1 h).
- case: (boolP (e2 \in Sd)) => h2 h.
    have : nxt e1 \in img by apply/imsetP; exists e1 => //; rewrite domP hn1 (key _ hn1).
    by rewrite h; move: (beta_Si h2); rewrite inE => /andP[] /negbTE ->.
  have he2 : e2 \notin SS.
    apply/negP => he2; move: h2; rewrite keySd //.
    by move: hn2; rewrite negbK => /eqP.
  by move: he2; rewrite -h (nxt_SS hn1).
- case: (boolP (e1 \in Sd)) => h1 h.
    have : nxt e2 \in img by apply/imsetP; exists e2 => //; rewrite domP hn2 (key _ hn2).
    by rewrite -h; move: (beta_Si h1); rewrite inE => /andP[] /negbTE ->.
  have he1 : e1 \notin SS.
    apply/negP => he1; move: h1; rewrite keySd //.
    by move: hn1; rewrite negbK => /eqP.
  by move: he1; rewrite h (nxt_SS hn2).
case: (boolP (e1 \in Sd)) => h1; case: (boolP (e2 \in Sd)) => h2 h.
- exact: beta_inj.
- have he2 : e2 \notin SS.
    by apply/negP => he2; move: h2; rewrite keySd //; move: hn2; rewrite negbK => /eqP.
  by move: he2; rewrite -h; move: (beta_Si h1); rewrite inE => /andP[_ ->].
- have he1 : e1 \notin SS.
    by apply/negP => he1; move: h1; rewrite keySd //; move: hn1; rewrite negbK => /eqP.
  by move: he1; rewrite h; move: (beta_Si h2); rewrite inE => /andP[_ ->].
- exact: h.
Qed.

(** The blocks: the [sigma]-orbits of the elements of [SS]. *)

Definition reps : seq {set G} := [seq e <- enum SS | froots sigma e].
Definition blocks : seq (seq {set G}) := [seq orbit sigma r | r <- reps].
Definition bl : seq {set G} := flatten blocks.

Lemma iter_sigma_SS (k : nat) (e : {set G}) : e \in SS -> iter k sigma e \in SS.
Proof. by move=> he; elim: k => [//|k IH]; rewrite iterS; exact: sigma_SS. Qed.

Lemma fconnect_SS (e y : {set G}) : e \in SS -> fconnect sigma e y -> y \in SS.
Proof. by move=> he hy; rewrite -(iter_findex hy); exact: iter_sigma_SS. Qed.

Lemma root_SS (e : {set G}) : e \in SS -> froot sigma e \in SS.
Proof. by move=> he; apply: (fconnect_SS he); exact: connect_root. Qed.

Lemma mem_reps (r : {set G}) : (r \in reps) = (r \in SS) && (froots sigma r).
Proof. by rewrite mem_filter mem_enum andbC. Qed.

Lemma uniq_reps : uniq reps.
Proof. by rewrite filter_uniq // enum_uniq. Qed.

Lemma mem_bl (e : {set G}) : (e \in bl) = (e \in SS).
Proof.
apply/idP/idP.
  move=> /flattenP[b hb he]; case/mapP: hb => r hr hbr.
  move: he; rewrite hbr -fconnect_orbit => hc.
  by apply: (fconnect_SS _ hc); move: hr; rewrite mem_reps => /andP[].
move=> he; apply/flattenP; exists (orbit sigma (froot sigma e)).
  apply/mapP; exists (froot sigma e); last by [].
  by rewrite mem_reps (root_SS he) (roots_root (fconnect_sym sigma_inj)).
by rewrite -fconnect_orbit (fconnect_sym sigma_inj); exact: connect_root.
Qed.

Lemma uniq_bl : uniq bl.
Proof.
apply: count_mem_uniq => x.
have key : count_mem x bl = count (fun r => x \in orbit sigma r) reps.
  rewrite /bl count_flatten /blocks -map_comp.
  elim: reps => [//|r rs IH] /=; rewrite IH; congr (_ + _).
  by rewrite count_uniq_mem ?orbit_uniq.
rewrite key mem_bl.
have hle : count (fun r => x \in orbit sigma r) reps <= 1.
  rewrite (@eq_in_count _ _ (fun r => (x \in orbit sigma r) && froots sigma r)); last first.
    by move=> r; rewrite mem_reps => /andP[_ ->]; rewrite andbT.
  apply: leq_trans (_ : count_mem (froot sigma x) reps <= 1); last first.
    by rewrite count_uniq_mem ?uniq_reps // leq_b1.
  apply: sub_count => r /=; rewrite -fconnect_orbit => /andP[hc /eqP hr].
  rewrite -{1}hr; apply/eqP.
  by apply/(rootP (fconnect_sym sigma_inj)); exact: hc.
case: (boolP (x \in SS)) => hx.
  apply/eqP; rewrite eqn_leq hle /=.
  have hmem : froot sigma x \in reps.
    by rewrite mem_reps (root_SS hx) (roots_root (fconnect_sym sigma_inj)).
  rewrite -has_count; apply/hasP; exists (froot sigma x) => //=.
  by rewrite -fconnect_orbit (fconnect_sym sigma_inj); exact: connect_root.
apply/eqP; rewrite -leqn0 leqNgt -has_count; apply/negP => /hasP[r hr /=].
rewrite -fconnect_orbit => hc; move: hx.
have : r \in SS by move: hr; rewrite mem_reps => /andP[].
by move=> hrS; rewrite (fconnect_SS hrS hc).
Qed.

Lemma blocksP (b : seq {set G}) :
  b \in blocks -> exists2 r, (r \in SS) & b = orbit sigma r.
Proof.
by case/mapP => r; rewrite mem_reps => /andP[hr _] ->; exists r.
Qed.

Lemma block_uniq (b : seq {set G}) : b \in blocks -> uniq b.
Proof. by case/blocksP => r _ ->; exact: orbit_uniq. Qed.

Lemma block_size (b : seq {set G}) : b \in blocks -> 0 < size b.
Proof. by case/blocksP => r _ ->; rewrite size_orbit order_gt0. Qed.

Lemma block_sub (b : seq {set G}) (e : {set G}) : b \in blocks -> e \in b -> e \in SS.
Proof.
move=> hb he; rewrite -mem_bl; apply/flattenP; exists b => //.
Qed.

Lemma block_nth (b : seq {set G}) (k : nat) :
  b \in blocks -> k < size b ->
  sigma (nth set0 b k) = nth set0 b (k.+1 %% size b).
Proof.
case/blocksP => r hr -> hk.
have hsz : size (orbit sigma r) = order sigma r by exact: size_orbit.
have hnth (j : nat) : j < order sigma r -> nth set0 (orbit sigma r) j = iter j sigma r.
  move=> hj; rewrite (set_nth_default r) ?hsz //.
  by rewrite /orbit nth_traject.
move: hk; rewrite hsz => hk.
rewrite hnth //.
case: (ltnP k.+1 (order sigma r)) => hk1.
  by rewrite modn_small // hnth.
have hkeq : k.+1 = order sigma r by apply/eqP; rewrite eqn_leq hk1 hk.
rewrite -hkeq modnn hnth //=.
by rewrite -iterS hkeq (iter_order sigma_inj).
Qed.

End TwoMatchings.
