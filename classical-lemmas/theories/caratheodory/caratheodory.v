(** * ClassicalLemmas.caratheodory.caratheodory — Carathéodory's theorem over ℚ

    A convex combination of points of ℚ^d can be rewritten as a convex
    combination of at most [d+1] of them.  The points are given as functions
    ['I_d -> rat] (coordinates), which is how the statistics of a matching are
    presented downstream; matrices appear only inside the proof, to produce an
    affine dependency once more than [d+1] weights are positive. *)

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

    ESTIMATED TOKEN COST FOR THIS FILE.  Claude Opus 5, 156k tokens, of which
    72k output.  Method: as in necklace/necklace.v — for every assistant
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

      [C1911]  C. Carathéodory, "Über den Variabilitätsbereich der
             Fourier'schen Konstanten von positiven harmonischen Funktionen",
             Rend. Circ. Mat. Palermo 32 (1911) 193-217: a point of the convex
             hull of a set in dimension d is a convex combination of at most
             d+1 of its points.  Proved here by the standard argument: more
             than d+1 positive weights give an affine dependency, which is
             followed until one weight vanishes.

    WHAT CORRESPONDS TO WHAT.

      - [LLM] step 2, "by Carathéodory's theorem the average of the Delta
        matchings is a convex combination of at most m+2 of them"
                                    -> [caratheodory] (rational weights),
                                       [caratheodory_nat] (the same with the
                                       denominators cleared, which is the form
                                       used downstream)
      - the affine dependency, from a non-trivial kernel vector of the matrix
        of the points with a row of ones added
                                    -> [dependency], [seq_min], [set_min],
                                       [clear_denoms]
 *)

From mathcomp Require Import all_boot all_order all_algebra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Num.Theory Order.POrderTheory Order.TotalTheory.
Set SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.

(** ** A minimiser of a rational function on a nonempty sequence *)

Lemma seq_min (T : eqType) (F : T -> rat) (s : seq T) :
  forall x : T, x \in s -> exists2 t, t \in s & forall u, u \in s -> F t <= F u.
Proof.
elim: s => [x|a s IH x hx]; first by rewrite in_nil.
case: (boolP (nilp s)) => [/nilP hs|hs].
  exists a; first by rewrite inE eqxx.
  by move=> u; rewrite hs inE => /eqP->.
have hb : nth x s 0 \in s by apply: mem_nth; rewrite lt0n; move: hs; rewrite /nilp.
have [t hts hmin] := IH _ hb.
case: (lerP (F a) (F t)) => hcmp.
  exists a; first by rewrite inE eqxx.
  move=> u; rewrite inE => /orP[/eqP->//|hu].
  by apply: le_trans hcmp _; exact: hmin.
exists t; first by rewrite inE hts orbT.
move=> u; rewrite inE => /orP[/eqP->|hu]; last exact: hmin.
exact: ltW.
Qed.

Lemma set_min (T : finType) (F : T -> rat) (S : {set T}) (x : T) :
  x \in S -> exists2 t, t \in S & forall u, u \in S -> F t <= F u.
Proof.
move=> hx.
have hxs : x \in enum S by rewrite mem_enum.
have [t hts hmin] := seq_min F hxs.
by exists t => [|u hu]; [rewrite -mem_enum|apply: hmin; rewrite mem_enum].
Qed.

(** ** An affine dependency among more than [d+1] points *)

Section Dependency.
Variables (d : nat) (T : finType).

Lemma dependency (S : {set T}) (z : T -> 'I_d -> rat) (t0 : T) :
  t0 \in S -> (d.+1 < #|S|)%N ->
  exists nu : T -> rat,
    [/\ (forall t, t \notin S -> nu t = 0),
        (exists t, nu t != 0),
        \sum_t nu t = 0 &
        forall c : 'I_d, \sum_t nu t * z t c = 0].
Proof.
move=> ht0 hcard.
pose n := #|S|.
pose A : 'M[rat]_(n, 1 + d) :=
  row_mx (const_mx 1) (\matrix_(i < n, c < d) z (enum_val i) c).
have hrank : (\rank A <= d.+1)%N by apply: rank_leq_col.
have hnfree : ~~ row_free A.
  by rewrite -row_leq_rank -ltnNge; apply: leq_ltn_trans hrank hcard.
have hker : kermx A != 0 by rewrite kermx_eq0.
have [u husub hu0] := rowV0Pn hker.
have huA : u *m A = 0 by apply/sub_kermxP.
have hentry (j : 'I_(1 + d)) : \sum_(i < n) u 0 i * A i j = 0.
  by have := huA; move/matrixP => /(_ 0 j); rewrite !mxE.
pose nu : T -> rat := fun t => if t \in S then u 0 (enum_rank_in ht0 t) else 0.
have hsum (g : 'I_n -> rat) :
    \sum_t (if t \in S then g (enum_rank_in ht0 t) else 0) = \sum_(i < n) g i.
  rewrite (bigID (fun t => t \in S)) /=.
  rewrite [X in _ + X]big1 ?addr0; last by move=> t /negbTE ->.
  rewrite (eq_bigr (fun t => g (enum_rank_in ht0 t))); last by move=> t ->.
  by rewrite big_enum_val; apply: eq_bigr => i _; rewrite enum_valK_in.
exists nu; split.
- by move=> t /negbTE; rewrite /nu => ->.
- have [i hui] : exists i, u 0 i != 0 by apply/rV0Pn.
  exists (enum_val i); rewrite /nu (enum_valP i) enum_valK_in //.
- rewrite /nu (hsum (fun i => u 0 i)).
  have := hentry (lshift d ord0).
  by rewrite (eq_bigr (fun i => u 0 i)) // => i _; rewrite row_mxEl mxE mulr1.
move=> c; rewrite /nu.
rewrite (eq_bigr (fun t => if t \in S
    then u 0 (enum_rank_in ht0 t) * z (enum_val (enum_rank_in ht0 t)) c
    else 0)); last first.
  move=> t _; case: (boolP (t \in S)) => ht; last by rewrite mul0r.
  by rewrite enum_rankK_in.
rewrite (hsum (fun i => u 0 i * z (enum_val i) c)).
have := hentry (rshift 1 c).
rewrite (eq_bigr (fun i => u 0 i * z (enum_val i) c)) // => i _.
by rewrite row_mxEr mxE.
Qed.

End Dependency.

(** ** Carathéodory's theorem *)

Theorem caratheodory (d : nat) (T : finType) (z : T -> 'I_d -> rat) (lam : T -> rat) :
  (forall t, 0 <= lam t) -> \sum_t lam t = 1 ->
  exists mu : T -> rat,
    [/\ forall t, 0 <= mu t,
        \sum_t mu t = 1,
        forall c : 'I_d, \sum_t mu t * z t c = \sum_t lam t * z t c &
        (#|[set t | mu t != 0%R]| <= d.+1)%N].
Proof.
suff key : forall (n : nat) (la : T -> rat), (#|[set t | la t != 0%R]| <= n)%N ->
    (forall t, 0 <= la t) -> \sum_t la t = 1 ->
    exists mu : T -> rat,
      [/\ forall t, 0 <= mu t, \sum_t mu t = 1,
          forall c : 'I_d, \sum_t mu t * z t c = \sum_t la t * z t c &
          (#|[set t | mu t != 0%R]| <= d.+1)%N].
  by move=> hpos hsum1; apply: (key #|T|) => //; apply: max_card.
elim=> [|n IH] la hcard hpos hsum1.
  by exists la; split=> //; apply: leq_trans hcard _.
case: (leqP #|[set t | la t != 0]| d.+1) => [hle|hgt].
  by exists la; split.
have ht0 : exists t0, t0 \in [set t | la t != 0].
  by apply/card_gt0P; apply: leq_trans hgt; rewrite ltn0Sn.
case: ht0 => t0 ht0.
have [nu [hnu0 hnuex hnusum hnuz]] := dependency z ht0 hgt.
case: hnuex => tn hnun.
have hex_pos : exists t, 0 < nu t.
  case: (boolP [forall t, nu t <= 0]) => [/forallP hall|hno]; last first.
    by move: hno; rewrite negb_forall => /existsP[t]; rewrite -ltNge => ht; exists t.
  exfalso.
  have hle0 : forall t, 0 <= - nu t by move=> t; rewrite oppr_ge0; exact: hall.
  have : \sum_t (- nu t) == 0 by rewrite sumrN hnusum oppr0 eqxx.
  rewrite psumr_eq0 // => /allP/(_ tn (mem_index_enum tn)).
  by rewrite oppr_eq0 (negbTE hnun).
pose Sp : {set T} := [set t | 0 < nu t].
have htp : exists t, t \in Sp by case: hex_pos => t h; exists t; rewrite inE.
case: htp => tp htp.
have [tm htm hmin] := set_min (fun t => la t / nu t) htp.
have hnum : 0 < nu tm by move: htm; rewrite inE.
pose theta := la tm / nu tm.
have htheta0 : 0 <= theta by rewrite /theta divr_ge0 // ltW.
pose la' : T -> rat := fun t => la t - theta * nu t.
have hla'pos : forall t, 0 <= la' t.
  move=> t; rewrite /la' subr_ge0; case: (lerP (nu t) 0) => hnt.
    by apply: le_trans (hpos t); rewrite -oppr_ge0 -mulrN mulr_ge0 // oppr_ge0.
  have htmem : t \in Sp by rewrite inE.
  by rewrite -ler_pdivlMr //; exact: hmin.
have hla'sum : \sum_t la' t = 1.
  rewrite /la' sumrB hsum1 -mulr_sumr hnusum mulr0 subr0 //.
have hla'z : forall c : 'I_d, \sum_t la' t * z t c = \sum_t la t * z t c.
  move=> c; rewrite /la'.
  rewrite (eq_bigr (fun t => la t * z t c - theta * (nu t * z t c))); last first.
    by move=> t _; rewrite mulrBl mulrA.
  by rewrite sumrB -mulr_sumr hnuz mulr0 subr0.
have hlam0 : la tm != 0.
  apply/negP => /eqP h0.
  have hnutm : nu tm = 0 by apply: hnu0; rewrite inE h0 eqxx.
  by move: hnum; rewrite hnutm ltxx.
have hla'm : la' tm = 0.
  rewrite /la' /theta divfK ?subrr //.
  by rewrite gt_eqF.
have hsubset : [set t | la' t != 0] \subset [set t | la t != 0] :\ tm.
  apply/subsetP => t; rewrite !inE => hne.
  have hlat : la t != 0.
    apply: contraNneq hne => h0.
    by rewrite /la' h0 hnu0 ?mulr0 ?subrr // inE h0 eqxx.
  apply/andP; split; last exact: hlat.
  by apply/negP => /eqP heq; move: hne; rewrite heq hla'm eqxx.
have hcard' : (#|[set t | la' t != 0%R]| <= n)%N.
  apply: leq_trans (subset_leq_card hsubset) _.
  rewrite (cardsD1 tm [set t | la t != 0]) inE hlam0 /= add1n in hcard.
  by move: hcard; rewrite ltnS.
have [mu [h1 h2 h3 h4]] := IH _ hcard' hla'pos hla'sum.
by exists mu; split=> // c; rewrite h3 hla'z.
Qed.

Print Assumptions caratheodory.

(** ** Clearing denominators: from rational to natural weights *)

Section ClearDenoms.
Variable T : finType.

Lemma clear_denoms (x : T -> rat) :
  (forall t, 0 <= x t) ->
  exists (a : T -> nat) (q : nat),
    (0 < q)%N /\ forall t, x t * q%:R = (a t)%:R.
Proof.
move=> hpos.
pose dn (t : T) : nat := `|denq (x t)|%N.
have hdn (t : T) : (0 < dn t)%N by rewrite /dn absz_gt0 gt_eqF ?denq_gt0.
pose q : nat := \prod_t dn t.
have hq : (0 < q)%N by rewrite /q prodn_gt0.
pose Q (t : T) : nat := \prod_(u | u != t) dn u.
have hqQ (t : T) : q = (dn t * Q t)%N by rewrite /q (bigD1 t).
exists (fun t => (`|numq (x t)|%N * Q t)%N), q; split=> // t.
rewrite (hqQ t) natrM mulrA.
have -> : ((dn t)%:R : rat) = (denq (x t))%:~R.
  by rewrite /dn natr_absz ger0_norm // ltW // denq_gt0.
rewrite -numqE natrM natr_absz ger0_norm //.
by rewrite numq_ge0 hpos.
Qed.

End ClearDenoms.

(** ** Carathéodory with natural weights

    The convex combination is presented by natural weights [w] (the point being
    [(sum w_t z_t)/(sum w_t)]); the conclusion gives natural weights [a]
    supported on at most [d+1] points and defining the same point, written
    without division. *)

Theorem caratheodory_nat (d : nat) (T : finType) (z : T -> 'I_d -> nat)
    (w : T -> nat) :
  (0 < \sum_t w t)%N ->
  exists a : T -> nat,
    [/\ (0 < \sum_t a t)%N,
        (#|[set t | a t != 0%N]| <= d.+1)%N &
        forall c : 'I_d, ((\sum_t a t * z t c) * (\sum_t w t)
                        = (\sum_t w t * z t c) * (\sum_t a t))%N].
Proof.
move=> hw.
pose S := (\sum_t w t)%N.
have hSr : (S%:R : rat) != 0 by rewrite pnatr_eq0 -lt0n.
pose lam (t : T) : rat := (w t)%:R / S%:R.
have hlam0 : forall t, 0 <= lam t by move=> t; rewrite /lam divr_ge0 ?ler0n.
have hlam1 : \sum_t lam t = 1.
  by rewrite /lam -mulr_suml -natr_sum divff.
pose zr (t : T) (c : 'I_d) : rat := (z t c)%:R.
have [mu [hmu0 hmu1 hmuz hmusupp]] := caratheodory zr hlam0 hlam1.
have [a [q [hq ha]]] := clear_denoms hmu0.
have hqr : (q%:R : rat) != 0 by rewrite pnatr_eq0 -lt0n.
have hsum : (\sum_t a t)%N = q.
  apply/eqP; rewrite -(@eqr_nat rat).
  rewrite natr_sum (eq_bigr (fun t => mu t * q%:R)); last by move=> t _; rewrite ha.
  by rewrite -mulr_suml hmu1 mul1r.
exists a; split.
- by rewrite hsum.
- apply: (leq_trans _ hmusupp); apply: subset_leq_card; apply/subsetP => t.
  rewrite !inE => hat; apply/negP => /eqP hmut.
  by move: hat; rewrite -(@eqr_nat rat) -ha hmut mul0r eqxx.
- move=> c.
  apply/eqP; rewrite -(@eqr_nat rat) !natrM !natr_sum.
  rewrite (eq_bigr (fun t => mu t * q%:R * (z t c)%:R)); last first.
    by move=> t _; rewrite natrM ha.
  have hL : \sum_i (w i)%:R = (S%:R : rat) by rewrite -natr_sum.
  have hA : \sum_i (a i)%:R = (q%:R : rat) by rewrite -natr_sum hsum.
  rewrite hL hA.
  have -> : \sum_i mu i * q%:R * (z i c)%:R = q%:R * \sum_i lam i * (z i c)%:R.
    rewrite -hmuz mulr_sumr; apply: eq_bigr => t _.
    by rewrite [mu t * q%:R]mulrC -mulrA.
  have -> : \sum_i lam i * (z i c)%:R = (\sum_i (w i * z i c)%:R) / S%:R.
    rewrite mulr_suml; apply: eq_bigr => t _.
    by rewrite /lam natrM mulrAC.
  by rewrite -mulrA mulfVK // mulrC eqxx.
Qed.

Print Assumptions caratheodory_nat.
