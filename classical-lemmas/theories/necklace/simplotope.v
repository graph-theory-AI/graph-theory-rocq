(** * ClassicalLemmas.simplotope — the complex L = (Δ_{p-1})^t and its chain complex

    Stage C foundation (Meunier 2014, §2.1–2.3).  A simplotope of
    [L = (Δ_{p-1})^t] is a product [σ_1 × … × σ_t] of nonempty subsets of ['I_p];
    we represent it as [Lcell := {ffun 'I_t -> {set 'I_p}}] (cells with an empty
    factor are inert: they are never produced by the boundary from a genuine
    simplotope).  Its dimension is [Ldim σ = Σ_i (|σ_i| - 1)].

    Each factor carries the canonical increasing orientation, so the boundary of
    §2.3 becomes

      ∂σ = Σ_{i : |σ_i| ≥ 2} Σ_{v ∈ σ_i} (-1)^{rk_i(v) + D_i} (σ with v removed from σ_i)

    where [rk_i(v)] is the rank of [v] in [σ_i] and [D_i = Σ_{i' < i} (|σ_{i'}|-1)].
    The main result is [Lbd_bd : ∂∂ = 0]. *)

(** ** Provenance, sources, and what corresponds to what

    HOW THIS FILE WAS OBTAINED.  It was written with Claude Code (Anthropic),
    driving Rocq interactively through the rocq-mcp-evolve MCP server ("build"
    to list the open goals of a file, "open"/"step"/"try"/"check" to drive a
    single proof), so that a failing tactic was diagnosed on the spot instead
    of by recompiling.  rocq-mcp-evolve is developed by the LLM4Rocq project,
    https://github.com/LLM4Rocq/rocq-mcp-evolve (Apache-2.0; the opam package
    still carries its former slug LLM4Rocq/rocq-tools); it is gratefully
    acknowledged here.  Every error that recurred, together with the tactic
    that fixed it, is recorded in tactics-playbook.md at the root of the
    repository.  No result is admitted: "Print Assumptions" on the results of
    this file answers "Closed under the global context".

    MODELS AND ESTIMATED TOKEN COST FOR THIS FILE.

        Claude Opus 5       627k tokens   (09-15 08:04 -> 09-15 13:19 UTC)
        TOTAL               627k tokens   of which 248k were output

      Method: the figures are estimated from the logs of the Claude Code
      session of 14-15 September 2026.  For every assistant message they count
      input + cache-creation + output tokens, i.e. the tokens processed anew,
      excluding the cached conversation that is re-read at each turn (772M
      over the project); a message is charged to the file its tool calls were
      acting on.  Three whole-session context rebuilds (compaction or resume),
      1.61M tokens in all, are charged to no file.  Project totals: 4.10M
      tokens of per-file work, 1.61M of context rebuilds, 5.70M overall.

    SOURCES.

      [M14]  F. Meunier, "Simplotopal maps and necklace splitting",
             Discrete Mathematics 323 (2014) 14-26.
             Local copy: classical-lemmas/Meunier2014-Simplotopal_Necklace_web.pdf

    WHAT CORRESPONDS TO WHAT.

      The simplotopal complex L = (Delta_{p-1})^t of [M14, Sect. 3.2] and the
      part of [M14, Sect. 2] it needs.

      - [M14, Sect. 2.1], abstract simplotopes, their faces and their facets
                                    -> Lcell, Ldim, Lfacet, Lvalid, Lsub,
                                       Lsub_facet, Ldim_Lfacet
      - [M14, Sect. 2.2-2.3], orientation and boundary
                                    -> Lsign, Lbd1, Lbd
      - [M14, Lemma 2.2], "d o d = 0"
                                    -> Lbd_bd
      - [M14, Lemma 2.1], "the graph whose vertices are the facets of a
        d-simplotope sigma, d >= 2, ... is connected", used in the proof of
        [M14, Theorem 2.4] together with the corollary of Lemma 2.2 to conclude
        that "all the beta_{tau'} are equal"
                                    -> Lfacet_ker2
        and its dimension-1 counterpart, which [M14] settles by counting the
        two endpoints of an edge
                                    -> Lfacet_ker1, Lbd1_aug
      - [M14, Sect. 3.3], the cyclic action of Z_p on L, which is not
        orientation preserving, so that the induced action on chains carries a
        sign
                                    -> Lsh, esgn, Lnu, Lbd_Lnu *)

From mathcomp Require Import all_boot all_algebra.
From ClassicalLemmas Require Import necklace.chains.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Set SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.

Section Simplotope.
Variables (t p : nat).

Definition Lcell := {ffun 'I_t -> {set 'I_p}}.

Definition Ldim (s : Lcell) : nat := \sum_(i : 'I_t) (#|s i| - 1).

(** remove the vertex [v] from factor [i] *)
Definition Lfacet (s : Lcell) (i : 'I_t) (v : 'I_p) : Lcell :=
  [ffun i' => if i' == i then (s i') :\ v else s i'].

Definition rkL (s : Lcell) (i : 'I_t) (v : 'I_p) : nat :=
  #|[set w in s i | (val w < val v)%N]|.

Definition Dpre (s : Lcell) (i : 'I_t) : nat :=
  \sum_(i' : 'I_t | (val i' < val i)%N) (#|s i'| - 1).

(** [(i,v)] indexes a genuine facet of [s] *)
Definition Lvalid (s : Lcell) (iv : 'I_t * 'I_p) : bool :=
  (2 <= #|s iv.1|)%N && (iv.2 \in s iv.1).

Definition Lsign (s : Lcell) (iv : 'I_t * 'I_p) : nat :=
  rkL s iv.1 iv.2 + Dpre s iv.1.

(** ** facet calculus *)

Lemma LfacetE s i v i' : Lfacet s i v i' = if i' == i then (s i') :\ v else s i'.
Proof. by rewrite ffunE. Qed.

Lemma Lfacet_same s i v : Lfacet s i v i = (s i) :\ v.
Proof. by rewrite LfacetE eqxx. Qed.

Lemma Lfacet_diff s i v i' : i' != i -> Lfacet s i v i' = s i'.
Proof. by move=> h; rewrite LfacetE (negbTE h). Qed.

Lemma LfacetC s i v j w :
  Lfacet (Lfacet s i v) j w = Lfacet (Lfacet s j w) i v.
Proof.
apply/ffunP => l; rewrite !LfacetE.
case: (eqVneq l j) => [lj|lj]; case: (eqVneq l i) => [li|li].
- by apply/setP => x; rewrite !inE andbCA.
all: by [].
Qed.

Lemma card_Lfacet (s : Lcell) i (v : 'I_p) : v \in s i -> #|(s i) :\ v| = (#|s i|).-1.
Proof. by move=> h; rewrite [in RHS](cardsD1 v) h. Qed.

Lemma rkL_diff s i v j w : j != i -> rkL (Lfacet s i v) j w = rkL s j w.
Proof. by move=> h; rewrite /rkL Lfacet_diff. Qed.

Lemma rkL_same (s : Lcell) i (v w : 'I_p) : v \in s i ->
  rkL (Lfacet s i v) i w = (rkL s i w - (val v < val w))%N.
Proof.
move=> vs; rewrite /rkL Lfacet_same.
have -> : [set x in (s i) :\ v | (val x < val w)%N]
        = [set x in s i | (val x < val w)%N] :\ v.
  by apply/setP => x; rewrite !inE andbA.
rewrite [in RHS](cardsD1 v) inE vs /=.
by case: (val v < val w)%N; rewrite ?add1n ?add0n ?subn1 ?subn0.
Qed.

Lemma rkL_gt0 (s : Lcell) i (v w : 'I_p) : v \in s i -> (val v < val w)%N -> (0 < rkL s i w)%N.
Proof. by move=> vs vw; rewrite /rkL (cardsD1 v) inE vs vw. Qed.

Lemma Dpre_Lfacet (s : Lcell) i (v : 'I_p) j : (2 <= #|s i|)%N -> v \in s i ->
  Dpre (Lfacet s i v) j = (Dpre s j - (val i < val j))%N.
Proof.
move=> h2 vs; rewrite /Dpre.
case: (ltnP (val i) (val j)) => hij; last first.
  rewrite subn0; apply: eq_bigr => i' hi'.
  by rewrite Lfacet_diff // -(inj_eq val_inj) neq_ltn (leq_trans hi' hij).
rewrite (bigD1 i) //= [in RHS](bigD1 i) //= Lfacet_same card_Lfacet //.
rewrite (eq_bigr (fun i' => (#|s i'| - 1)%N)); last first.
  by move=> i' /andP[_ i'i]; rewrite Lfacet_diff.
have hcard : (0 < #|s i| - 1)%N by rewrite subn_gt0.
by rewrite -subn1 -[in RHS]addnBAC.
Qed.

Lemma Dpre_gt0 (s : Lcell) i j : (2 <= #|s i|)%N -> (val i < val j)%N -> (0 < Dpre s j)%N.
Proof.
by move=> hs hij; rewrite /Dpre (bigD1 i) //= addn_gt0 subn_gt0 hs.
Qed.

(** ** the two removals of a double facet, as a set-valued "removal" function *)

Definition rem2 (iv jw : 'I_t * 'I_p) (k : 'I_t) : {set 'I_p} :=
  (if k == iv.1 then [set iv.2] else set0) :|: (if k == jw.1 then [set jw.2] else set0).

Lemma mem_rem2 iv jw k x : (x \in rem2 iv jw k) = ((k, x) \in [set iv; jw]).
Proof.
case: iv => i v; case: jw => j w; rewrite /rem2 !inE /= !xpair_eqE.
by case: (k == i); case: (k == j); rewrite !inE //= ?orbF.
Qed.

Lemma dfE s iv jw :
  Lfacet (Lfacet s iv.1 iv.2) jw.1 jw.2 = [ffun k => s k :\: rem2 iv jw k].
Proof.
case: iv => i v; case: jw => j w.
apply/ffunP => k; rewrite !LfacetE ffunE /rem2 /=.
case: (eqVneq k j) => [kj|kj]; case: (eqVneq k i) => [ki|ki].
- by rewrite setDDl.
- by rewrite set0U.
- by rewrite setU0.
- by rewrite setU0 setD0.
Qed.

Lemma doubleton_eqP (T : finType) (a b c d : T) :
  a != b -> [set a; b] = [set c; d] -> (a = c /\ b = d) \/ (a = d /\ b = c).
Proof.
move=> ab e.
have ha : a \in [set c; d] by rewrite -e !inE eqxx.
have hb : b \in [set c; d] by rewrite -e !inE eqxx orbT.
move: ha hb; rewrite !inE => /orP[/eqP ea|/eqP ea] /orP[/eqP eb|/eqP eb].
- by move: ab; rewrite ea eb eqxx.
- by left.
- by right.
- by move: ab; rewrite ea eb eqxx.
Qed.

Lemma sub_setD (T : finType) (A B : {set T}) : B \subset A -> A :\: (A :\: B) = B.
Proof.
move=> sub; apply/setP => x; rewrite !inE.
case: (boolP (x \in B)) => [xB|xB] /=.
- by rewrite (subsetP sub).
- by case: (x \in A).
Qed.

Lemma Lvalid_neq s iv jw :
  Lvalid s iv -> Lvalid (Lfacet s iv.1 iv.2) jw -> iv != jw.
Proof.
move=> _ h2; apply/eqP => e; move: h2; rewrite -e /Lvalid Lfacet_same in_setD1.
by rewrite eqxx /= andbF.
Qed.

Lemma rem2_sub s iv jw :
  Lvalid s iv -> Lvalid (Lfacet s iv.1 iv.2) jw ->
  forall k, rem2 iv jw k \subset s k.
Proof.
case: iv => i v; case: jw => j w /= h1 h2 k.
have vs : v \in s i by move: h1 => /andP[].
have ws : w \in s j.
  move: h2 => /andP[_]; rewrite LfacetE.
  by case: (eqVneq j i) => [_|_] //; rewrite in_setD1 => /andP[].
apply/subsetP => x; rewrite mem_rem2 !inE.
by move=> /orP[/eqP[-> ->]|/eqP[-> ->]].
Qed.

Lemma double_facet_uniq s iv jw iv' jw' :
  Lvalid s iv -> Lvalid (Lfacet s iv.1 iv.2) jw ->
  Lvalid s iv' -> Lvalid (Lfacet s iv'.1 iv'.2) jw' ->
  Lfacet (Lfacet s iv'.1 iv'.2) jw'.1 jw'.2 = Lfacet (Lfacet s iv.1 iv.2) jw.1 jw.2 ->
  (iv' = iv /\ jw' = jw) \/ (iv' = jw /\ jw' = iv).
Proof.
move=> h1 h2 h1' h2' e.
have hrem : forall k, rem2 iv' jw' k = rem2 iv jw k.
  move=> k; rewrite -(sub_setD (rem2_sub h1' h2' k)) -(sub_setD (rem2_sub h1 h2 k)).
  by move: e; rewrite !dfE => /ffunP/(_ k); rewrite !ffunE => ->.
have hset : [set iv'; jw'] = [set iv; jw].
  apply/setP => q; case: q => k x.
  by rewrite -!mem_rem2 hrem.
by apply: doubleton_eqP hset; apply: (Lvalid_neq h1' h2').
Qed.

Lemma Lfacet_inj s iv jw :
  Lvalid s iv -> Lvalid s jw ->
  Lfacet s iv.1 iv.2 = Lfacet s jw.1 jw.2 -> iv = jw.
Proof.
case: iv => i v; case: jw => j w => /andP[_ vs] /andP[_ ws] /= e.
have ei : i = j.
  apply/eqP; apply: contraT => ij.
  move: e => /ffunP/(_ i); rewrite !LfacetE eqxx (negbTE ij) => ei.
  by move: vs; rewrite /= -ei in_setD1 eqxx.
move: vs ws e; rewrite ei /= => vs ws /ffunP/(_ j); rewrite !LfacetE eqxx => ej.
congr pair => //.
apply/eqP; apply: contraT => vw.
have hv : v \in s j :\ w by rewrite in_setD1 vw.
by move: hv; rewrite -ej in_setD1 eqxx.
Qed.

(** ** sub-simplotopes and dimensions *)

Lemma leq_add_eq (a b c d : nat) :
  (a <= c)%N -> (b <= d)%N -> (c + d = a + b)%N -> c = a /\ d = b.
Proof.
move=> ac bd e.
have ca : (c <= a)%N by rewrite -(leq_add2r d) e leq_add2l.
have ec : c = a by apply/eqP; rewrite eqn_leq ca ac.
by split=> //; move: e; rewrite ec => /addnI.
Qed.

Lemma sum_leq_eq (I : finType) (P : pred I) (F G : I -> nat) :
  (forall i, P i -> (F i <= G i)%N) ->
  (\sum_(i | P i) F i = \sum_(i | P i) G i)%N ->
  forall i, P i -> F i = G i.
Proof.
move=> le e i Pi; apply/eqP; rewrite eqn_leq (le i Pi) andTb leqNgt.
apply/negP => lt.
have lt2 : (\sum_(j | P j) F j < \sum_(j | P j) G j)%N.
  rewrite (bigD1 i) //= [X in (_ < X)%N](bigD1 i) //=.
  apply: leq_ltn_trans (_ : (F i + \sum_(j | P j && (j != i)) G j < _)%N).
    by rewrite leq_add2l; apply: leq_sum => j /andP[Pj _]; exact: le.
  by rewrite ltn_add2r.
by rewrite e ltnn in lt2.
Qed.

Definition Lsub (s s' : Lcell) : bool := [forall i, s i \subset s' i].

Lemma LsubP (s s' : Lcell) : reflect (forall i, s i \subset s' i) (Lsub s s').
Proof. exact: forallP. Qed.

Lemma Ldim_sub s s' : Lsub s s' -> (Ldim s <= Ldim s')%N.
Proof.
move=> /forallP h; apply: leq_sum => i _.
by rewrite leq_sub2r // subset_leq_card.
Qed.

Lemma Lsub_eq s s' :
  Lsub s s' -> (forall i, s i != set0) -> Ldim s = Ldim s' -> s = s'.
Proof.
move=> /forallP sub ne e; apply/ffunP => i.
have key : forall j, (#|s j| - 1 = #|s' j| - 1)%N.
  move=> j; apply: (@sum_leq_eq _ xpredT (fun k => (#|s k| - 1)%N)
                     (fun k => (#|s' k| - 1)%N)) => // k _.
  by rewrite leq_sub2r // subset_leq_card.
have h1 : (1 <= #|s i|)%N by rewrite card_gt0.
have h1' : (1 <= #|s' i|)%N by rewrite (leq_trans h1) // subset_leq_card.
apply/eqP; rewrite eqEcard sub /=.
by rewrite -(subnK h1) -(subnK h1') (key i).
Qed.

Lemma Ldim_Lfacet s iv :
  Lvalid s iv -> Ldim (Lfacet s iv.1 iv.2) = (Ldim s).-1.
Proof.
case: iv => i v /andP[h2 vs] /=.
rewrite /Ldim (bigD1 i) //= [in RHS](bigD1 i) //= Lfacet_same card_Lfacet //.
rewrite (eq_bigr (fun j => (#|s j| - 1)%N)); last by move=> j ji; rewrite Lfacet_diff.
have h1 : (1 <= #|s i| - 1)%N by rewrite subn_gt0.
case E : (#|s i| - 1)%N h1 => [//|a] _.
have -> : (#|s i|.-1 - 1 = a)%N by rewrite -subn1 E subn1.
by rewrite addSn.
Qed.

Lemma Lvalid_dim s iv : Lvalid s iv -> (1 <= Ldim s)%N.
Proof.
case: iv => i v /andP[h2 _] /=.
rewrite /Ldim (bigD1 i) //=; apply: leq_trans (leq_addr _ _).
by rewrite subn_gt0.
Qed.

Lemma Ldim_valid s : (1 <= Ldim s)%N -> exists iv, Lvalid s iv.
Proof.
move=> d1; have [i hi] : exists i, (2 <= #|s i|)%N.
  apply/existsP; apply: contraLR d1 => /existsPn h.
  rewrite -ltnNge ltnS leqn0 /Ldim; apply/eqP; apply: big1 => i _.
  by move: (h i); rewrite -ltnNge ltnS => hi; apply/eqP; rewrite subn_eq0.
have : (0 < #|s i|)%N by apply: leq_trans hi.
rewrite card_gt0 => /set0Pn[v vs].
by exists (i, v); rewrite /Lvalid /= hi vs.
Qed.

Lemma Lsub_facet s s' :
  Lsub s s' -> (forall i, s i != set0) -> Ldim s' = (Ldim s).+1 ->
  exists iv, Lvalid s' iv /\ s = Lfacet s' iv.1 iv.2.
Proof.
move=> /forallP sub ne e.
have lec j : (#|s j| - 1 <= #|s' j| - 1)%N by rewrite leq_sub2r // subset_leq_card.
have [i0 hi0] : exists i, (#|s i| - 1 < #|s' i| - 1)%N.
  apply/existsP; apply: contraT => /existsPn h.
  have heq : Ldim s = Ldim s'.
    by apply: eq_bigr => j _; apply/eqP; rewrite eqn_leq lec andTb leqNgt h.
  by move: e; rewrite heq => /eqP; rewrite eqn_leq ltnn andbF.
have hsplit : (#|s' i0| - 1 = (#|s i0| - 1).+1)%N
           /\ (\sum_(j | j != i0) (#|s' j| - 1) = \sum_(j | j != i0) (#|s j| - 1))%N.
  apply: leq_add_eq; [exact: hi0 | by apply: leq_sum => j _; exact: lec |].
  by move: e; rewrite /Ldim (bigD1 i0) //= [in RHS](bigD1 i0) //= addSn.
case: hsplit => hcard hrest.
have hother : forall j, j != i0 -> (#|s j| - 1 = #|s' j| - 1)%N.
  apply: (@sum_leq_eq _ (fun j => j != i0) (fun k => (#|s k| - 1)%N)
                       (fun k => (#|s' k| - 1)%N)) => [j _|]; first exact: lec.
  by rewrite hrest.
have hsame : forall j, j != i0 -> s j = s' j.
  move=> j ji; apply/eqP; rewrite eqEcard sub /=.
  have hj1 : (1 <= #|s j|)%N by rewrite card_gt0.
  have hj1' : (1 <= #|s' j|)%N by rewrite (leq_trans hj1) // subset_leq_card.
  by rewrite -(subnK hj1) -(subnK hj1') (hother j ji).
have h1 : (1 <= #|s i0|)%N by rewrite card_gt0.
have h1' : (1 <= #|s' i0|)%N by rewrite (leq_trans h1) // subset_leq_card.
have hc : #|s' i0| = (#|s i0|).+1.
  by rewrite -(subnK h1') hcard addn1 subn1 prednK.
have hD : #|s' i0 :\: s i0| = 1%N.
  by rewrite cardsD (setIidPr (sub i0)) hc subSn // subnn.
have [v hv] : exists v, s' i0 :\: s i0 = [set v] by apply/cards1P; rewrite hD.
have vs' : v \in s' i0 by move: (set11 v); rewrite -hv inE => /andP[_].
exists (i0, v); split.
  by rewrite /Lvalid /= vs' andbT hc ltnS.
apply/ffunP => j; rewrite LfacetE.
case: (eqVneq j i0) => [->|ji]; last exact: hsame.
by rewrite -[LHS](sub_setD (sub i0)) hv.
Qed.

Lemma Ldim2_other s i : (2 <= Ldim s)%N -> #|s i| = 2%N ->
  exists k, (k != i) && (2 <= #|s k|)%N.
Proof.
move=> d2 ci; apply/existsP; apply: contraLR d2 => /existsPn h.
rewrite -ltnNge /Ldim (bigD1 i) //= ci big1 ?addn0 // => k ki.
by move: (h k); rewrite negb_and ki /= -ltnNge ltnS -subn_eq0 => /eqP.
Qed.

Lemma rkL_pairE (s : Lcell) i (v w : 'I_p) :
  s i = [set v; w] -> v != w -> rkL s i v = (val w < val v)%N.
Proof.
move=> hsi vw; rewrite /rkL hsi.
have hset : [set x in [set v; w] | (val x < val v)%N]
          = if (val w < val v)%N then [set w] else set0.
  case: ifP => h; apply/setP => x; rewrite !inE.
  - case: (eqVneq x v) => [->|xv]; first by rewrite ltnn andbF (negbTE vw).
    by case: (eqVneq x w) => [->|xw]; rewrite ?h.
  - case: (eqVneq x v) => [->|xv]; first by rewrite ltnn andbF.
    by case: (eqVneq x w) => [->|xw]; rewrite ?h ?andbF.
by rewrite hset; case: ifP => _; rewrite ?cards1 ?cards0.
Qed.

Lemma Ldim1_shape s iv : Ldim s = 1%N -> Lvalid s iv ->
  #|s iv.1| = 2%N /\ forall k, k != iv.1 -> (#|s k| <= 1)%N.
Proof.
case: iv => i v /= e /andP[h2 _].
have h0 : (1 <= #|s i|)%N by apply: leq_trans h2.
have h1 : (1 <= #|s i| - 1)%N by rewrite subn_gt0.
move: e h1; rewrite /Ldim (bigD1 i) //=.
case E : (#|s i| - 1)%N => [|[|a]] //= e _.
have hSum : (\sum_(k | k != i) (#|s k| - 1) = 0)%N by move: e; rewrite add1n; case.
split; first by rewrite -(subnK h0) E.
move=> k ki.
have hle : (#|s k| - 1 <= \sum_(i0 | i0 != i) (#|s i0| - 1))%N.
  by rewrite (bigD1 k) //= leq_addr.
by move: hle; rewrite hSum leqn0 subn_eq0.
Qed.

Section Ring.
Variable R : comNzRingType.

Definition Lterm (s : Lcell) (iv : 'I_t * 'I_p) : {ffun Lcell -> R^o} :=
  if Lvalid s iv then (-1) ^+ (Lsign s iv) *: cc (Lfacet s iv.1 iv.2) else 0.

Definition Lbd1 (s : Lcell) : {ffun Lcell -> R^o} :=
  \sum_(iv : 'I_t * 'I_p) Lterm s iv.
Definition Lbd : {ffun Lcell -> R^o} -> {ffun Lcell -> R^o} := lin Lbd1.

Lemma LbdD x y : Lbd (x + y) = Lbd x + Lbd y. Proof. exact: linD. Qed.
Lemma LbdZ a x : Lbd (a *: x) = a *: Lbd x. Proof. exact: linZ. Qed.
Lemma Lbd_cc s : Lbd (cc s) = Lbd1 s. Proof. exact: lin_cc. Qed.

(** ** the double term of ∂∂ *)
Definition LTT (s : Lcell) (iv jw : 'I_t * 'I_p) : {ffun Lcell -> R^o} :=
  if Lvalid s iv then (-1) ^+ (Lsign s iv) *: Lterm (Lfacet s iv.1 iv.2) jw else 0.

Lemma LTT_diag s iv : LTT s iv iv = 0.
Proof.
rewrite /LTT; case: ifP => // _.
rewrite /Lterm /Lvalid /Lfacet !ffunE eqxx in_setD1 eqxx /=.
by rewrite andbF scaler0.
Qed.

Lemma Lbd_bd1 s : Lbd (Lbd1 s) = \sum_(iv : 'I_t * 'I_p) \sum_(jw : 'I_t * 'I_p) LTT s iv jw.
Proof.
rewrite /Lbd /Lbd1 lin_sum; apply: eq_bigr => iv _.
rewrite /LTT [in LHS]/Lterm; case: (Lvalid s iv).
- by rewrite linZ lin_cc -scaler_sumr.
- by rewrite lin0 big1.
Qed.

(** normal form of the double term *)
Lemma LTT_E s iv jw :
  LTT s iv jw =
  if Lvalid s iv && Lvalid (Lfacet s iv.1 iv.2) jw
  then (-1) ^+ (Lsign s iv + Lsign (Lfacet s iv.1 iv.2) jw)
       *: cc (Lfacet (Lfacet s iv.1 iv.2) jw.1 jw.2)
  else 0.
Proof.
rewrite /LTT /Lterm; case: (Lvalid s iv); last by [].
by case: (Lvalid (Lfacet s iv.1 iv.2) jw); rewrite ?scaler0 // scalerA exprD.
Qed.

(** the two admissibility conditions are symmetric in the two removals *)
Lemma Lcond_sym s iv jw :
  Lvalid s iv && Lvalid (Lfacet s iv.1 iv.2) jw
  = Lvalid s jw && Lvalid (Lfacet s jw.1 jw.2) iv.
Proof.
case: iv => i v; case: jw => j w; rewrite /Lvalid /=.
case: (eqVneq j i) => [->|ji]; last first.
  rewrite (Lfacet_diff _ _ ji) (Lfacet_diff _ _ (_ : i != j)); last by rewrite eq_sym.
  by case: (1 < #|s i|)%N; case: (v \in s i); case: (1 < #|s j|)%N; case: (w \in s j).
have key (a b : 'I_p) :
  [&& (1 < #|s i|)%N && (a \in s i), (1 < #|Lfacet s i a i|)%N & b \in Lfacet s i a i]
  = [&& (2 < #|s i|)%N, a \in s i, b \in s i & b != a].
  rewrite Lfacet_same in_setD1.
  case: (boolP (a \in s i)) => [as_|as_]; last by rewrite !andbF.
  rewrite card_Lfacet // !andbT.
  have -> : (1 < (#|s i|).-1)%N = (2 < #|s i|)%N by rewrite -subn1 ltn_subRL.
  have [h2|h2] := leqP #|s i| 2; first by rewrite !andbF.
  by rewrite (ltnW h2) /= andbC.
rewrite !key.
by case: (2 < #|s i|)%N; case: (v \in s i); case: (w \in s i); rewrite //= eq_sym.
Qed.

Lemma sgnS (m : nat) : (-1) ^+ m.+1 = - ((-1) ^+ m) :> R.
Proof. by rewrite exprS mulN1r. Qed.

(** the two sign exponents differ by exactly one *)
Lemma Lsign_succ s iv jw :
  Lvalid s iv && Lvalid (Lfacet s iv.1 iv.2) jw ->
  ((Lsign s jw + Lsign (Lfacet s jw.1 jw.2) iv)%N
     = (Lsign s iv + Lsign (Lfacet s iv.1 iv.2) jw).+1)%N
  \/ ((Lsign s iv + Lsign (Lfacet s iv.1 iv.2) jw)%N
     = (Lsign s jw + Lsign (Lfacet s jw.1 jw.2) iv).+1)%N.
Proof.
case: iv => i v; case: jw => j w /=; move=> hcond.
have hsym : Lvalid s (j,w) && Lvalid (Lfacet s j w) (i,v) by rewrite -Lcond_sym.
move: hcond => /andP[hv1 hv2]; move: hsym => /andP[hw1 hw2].
have h2i : (2 <= #|s i|)%N by move: hv1 => /andP[].
have vsi : v \in s i by move: hv1 => /andP[].
have h2j : (2 <= #|s j|)%N by move: hw1 => /andP[].
have wsj : w \in s j by move: hw1 => /andP[].
rewrite /Lsign /= (Dpre_Lfacet _ h2i vsi) (Dpre_Lfacet _ h2j wsj).
case: (eqVneq j i) => [ji|ji]; last first.
  have ij : i != j by rewrite eq_sym.
  rewrite (@rkL_diff s i v j w ji) (@rkL_diff s j w i v ij).
  case: (ltngtP (val i) (val j)) => [hij|hij|/val_inj eij]; last by rewrite eij eqxx in ij.
  - have hDj : (0 < Dpre s j)%N by apply: (Dpre_gt0 h2i).
    left; rewrite subn0 subn1 -addnS -addnS prednK //.
    by rewrite addnC.
  - have hDi : (0 < Dpre s i)%N by apply: (Dpre_gt0 h2j).
    right; rewrite subn0 subn1 -addnS -addnS prednK //.
    by rewrite addnC.
move: wsj hv2; rewrite ji => wsi hv2.
have wv : w != v by move: hv2 => /andP[_]; rewrite Lfacet_same in_setD1 => /andP[].
rewrite ltnn subn0 (rkL_same _ vsi) (rkL_same _ wsi).
case: (ltngtP (val v) (val w)) => [hvw|hvw|/val_inj evw]; last by rewrite evw eqxx in wv.
- have hr : (0 < rkL s i w)%N by apply: (rkL_gt0 vsi).
  left; rewrite subn0 subn1 -addnS -addSn prednK //.
  by rewrite addnC.
- have hr : (0 < rkL s i v)%N by apply: (rkL_gt0 wsi).
  right; rewrite subn0 subn1 -addnS -addSn prednK //.
  by rewrite addnC.
Qed.

Lemma Lsign_anti s iv jw :
  Lvalid s iv && Lvalid (Lfacet s iv.1 iv.2) jw ->
  (-1) ^+ (Lsign s jw + Lsign (Lfacet s jw.1 jw.2) iv)
  = - ((-1) ^+ (Lsign s iv + Lsign (Lfacet s iv.1 iv.2) jw)) :> R.
Proof.
by move=> hc; case: (Lsign_succ hc) => ->; rewrite sgnS ?opprK.
Qed.

Lemma LTT_anti s iv jw : LTT s jw iv = - LTT s iv jw.
Proof.
rewrite !LTT_E -Lcond_sym.
case: (boolP (Lvalid s iv && Lvalid (Lfacet s iv.1 iv.2) jw)) => hc; last by rewrite oppr0.
by rewrite Lsign_anti // LfacetC scaleNr.
Qed.

Lemma Lbd_bd x : Lbd (Lbd x) = 0.
Proof.
have dd s : Lbd (Lbd1 s) = 0.
  rewrite Lbd_bd1.
  apply: (@sum_pair_anti _ _ (fun q : 'I_t * 'I_p => val (enum_rank q))).
  - by move=> a b /val_inj/enum_rank_inj.
  - exact: LTT_diag.
  - by move=> i j; rewrite LTT_anti.
rewrite {1}/Lbd lin_comp /lin big1 // => s _.
by rewrite -/(lin Lbd1 (Lbd1 s)) -/(Lbd (Lbd1 s)) dd scaler0.
Qed.

(** ** facet coefficients of the boundary *)

Lemma scaleE (a : R) (f : {ffun Lcell -> R^o}) (x : Lcell) : (a *: f) x = a * f x.
Proof. by rewrite ffunE. Qed.

Lemma sign_sqr (m : nat) : (-1) ^+ m * (-1) ^+ m = 1 :> R.
Proof. by rewrite -expr2 sqrr_sign. Qed.

Lemma sign_neq0 (m : nat) : (-1) ^+ m != 0 :> R.
Proof.
apply/eqP => e; have := sign_sqr m; rewrite e mul0r => /esym /eqP.
by rewrite oner_eq0.
Qed.

Lemma Lbd1_valid s :
  Lbd1 s = \sum_(iv | Lvalid s iv) (-1) ^+ (Lsign s iv) *: cc (Lfacet s iv.1 iv.2).
Proof. by rewrite /Lbd1 [RHS]big_mkcond. Qed.

Lemma Lbd1_coef s iv : Lvalid s iv ->
  Lbd1 s (Lfacet s iv.1 iv.2) = (-1) ^+ (Lsign s iv).
Proof.
move=> hv; rewrite /Lbd1 sum_ffunE (bigD1 iv) //= /Lterm hv.
rewrite scaleE ccE eqxx mulr1 big1 ?addr0 // => jw jwi.
case: ifP => hw; last by rewrite ffunE.
rewrite scaleE ccE.
have -> : (Lfacet s iv.1 iv.2 == Lfacet s jw.1 jw.2) = false.
  apply/negbTE; apply/eqP => e.
  by move/eqP: jwi; apply; apply: (Lfacet_inj hw hv); rewrite e.
by rewrite mulr0.
Qed.

Lemma Lbd1_neq0 s : (1 <= Ldim s)%N -> Lbd1 s != 0.
Proof.
move=> d1; have [iv hv] := Ldim_valid d1.
apply/eqP => e; move: (Lbd1_coef hv); rewrite e ffunE => e2.
by move: (sign_neq0 (Lsign s iv)); rewrite -e2 eqxx.
Qed.

(** ** the kernel of the boundary on the facet chains of a simplotope

    (Meunier, Lemma 2.1 and the "corollary of Lemma 2.2" in the proof of
    Theorem 2.4): a combination of the facets of [s] whose boundary vanishes has
    all its coefficients equal, up to the induced orientations. *)

Lemma Lfacet_ker2 (s : Lcell) (b : 'I_t * 'I_p -> R) :
  (2 <= Ldim s)%N ->
  Lbd (\sum_(iv | Lvalid s iv) b iv *: cc (Lfacet s iv.1 iv.2)) = 0 ->
  forall iv jw, Lvalid s iv -> Lvalid s jw ->
    (-1) ^+ (Lsign s iv) * b iv = (-1) ^+ (Lsign s jw) * b jw.
Proof.
move=> d2 hz.
pose gam (iv : 'I_t * 'I_p) := (-1) ^+ (Lsign s iv) * b iv.
move: hz; rewrite big_mkcond /Lbd lin_sum => hz.
have hdbl : \sum_(iv : 'I_t * 'I_p) \sum_(jw : 'I_t * 'I_p) gam iv *: LTT s iv jw = 0.
  rewrite -[RHS]hz; apply: eq_bigr => iv _.
  case hv : (Lvalid s iv); last first.
    by rewrite lin0 big1 // => jw _; rewrite /LTT hv scaler0.
  rewrite linZ lin_cc /Lbd1 scaler_sumr; apply: eq_bigr => jw _.
  rewrite /LTT hv scalerA; congr (_ *: _).
  by rewrite /gam -mulrA [b iv * _]mulrC mulrA sign_sqr mul1r.
have key : forall iv jw, Lvalid s iv -> Lvalid (Lfacet s iv.1 iv.2) jw ->
    gam iv = gam jw.
  move=> iv jw hiv hjw.
  have hcond : Lvalid s iv && Lvalid (Lfacet s iv.1 iv.2) jw by rewrite hiv hjw.
  have hcond' : Lvalid s jw && Lvalid (Lfacet s jw.1 jw.2) iv by rewrite -Lcond_sym.
  have ivjw : iv != jw by apply: (Lvalid_neq hiv hjw).
  set rho := Lfacet (Lfacet s iv.1 iv.2) jw.1 jw.2.
  have E0 : \sum_(q : ('I_t * 'I_p) * ('I_t * 'I_p)) gam q.1 * (LTT s q.1 q.2 rho) = 0.
    have -> : \sum_(q : ('I_t * 'I_p) * ('I_t * 'I_p)) gam q.1 * (LTT s q.1 q.2 rho)
            = \sum_(iv0 : 'I_t * 'I_p) \sum_(jw0 : 'I_t * 'I_p)
                 gam iv0 * (LTT s iv0 jw0 rho).
      by rewrite pair_bigA.
    have E1 := congr1 (fun f : {ffun Lcell -> R^o} => f rho) hdbl.
    move: E1; rewrite /= sum_ffunE ffunE => E1.
    rewrite -[RHS]E1; apply: eq_bigr => q _.
    by rewrite sum_ffunE; apply: eq_bigr => q' _; rewrite scaleE.
  have hX : LTT s iv jw rho = (-1) ^+ (Lsign s iv + Lsign (Lfacet s iv.1 iv.2) jw).
    by rewrite LTT_E hcond scaleE ccE eqxx mulr1.
  move: E0; rewrite (bigD1 (iv,jw)) //= (bigD1 (jw,iv)) /=; last first.
    by rewrite xpair_eqE negb_and ivjw orbT.
  rewrite big1 ?addr0 => [|q /andP[q1 q2]]; last first.
    rewrite LTT_E;
      case hc : (Lvalid s q.1 && Lvalid (Lfacet s q.1.1 q.1.2) q.2);
      last by rewrite ffunE mulr0.
    rewrite scaleE ccE.
    have -> : (rho == Lfacet (Lfacet s q.1.1 q.1.2) q.2.1 q.2.2) = false.
      apply/negbTE; apply/eqP => e; move: hc => /andP[hc1 hc2].
      case: (double_facet_uniq hiv hjw hc1 hc2 (esym e)) => [][a1 a2].
      - by move/eqP: q1; apply; rewrite [q]surjective_pairing a1 a2.
      - by move/eqP: q2; apply; rewrite [q]surjective_pairing a1 a2.
    by rewrite mulr0 mulr0.
  rewrite [LTT s jw iv]LTT_anti ffunE hX mulrN -mulrBl => hh.
  have h2 : (gam iv - gam jw) * (-1) ^+ (Lsign s iv + Lsign (Lfacet s iv.1 iv.2) jw)
            * (-1) ^+ (Lsign s iv + Lsign (Lfacet s iv.1 iv.2) jw) = 0.
    by rewrite hh mul0r.
  by move: h2; rewrite -mulrA sign_sqr mulr1 => /eqP; rewrite subr_eq0 => /eqP.
have diff : forall i v j w, i != j -> Lvalid s (i,v) -> Lvalid s (j,w) ->
    gam (i,v) = gam (j,w).
  move=> i v j w ij hiv hjw; apply: key => //=.
  have ji : j != i by rewrite eq_sym.
  by rewrite /Lvalid /= (@Lfacet_diff s i v j ji).
have same3 : forall i v w, (3 <= #|s i|)%N -> Lvalid s (i,v) -> Lvalid s (i,w) ->
    v != w -> gam (i,v) = gam (i,w).
  move=> i v w c3 hiv hiw vw; apply: key => //=.
  have h0 : (0 < #|s i|)%N by apply: leq_trans c3.
  move: hiv hiw => /andP[hc1 hm1] /andP[_ hm2].
  rewrite /Lvalid /= Lfacet_same card_Lfacet // in_setD1 eq_sym vw hm2 andbT.
  by rewrite andbT -ltnS prednK.
move=> iv jw hiv hjw.
suff h : gam iv = gam jw by [].
case: iv hiv => i v hiv; case: jw hjw => j w hjw.
case: (eqVneq i j) hiv => [->|ij] hiv; last exact: diff.
case: (eqVneq v w) => [->//|vw].
case: (ltnP #|s j| 3) => [c2|c3]; last exact: same3.
have hc2 : #|s j| = 2%N.
  by apply/eqP; rewrite eqn_leq -ltnS c2 /=; move: hiv => /andP[].
have [k /andP[ki ck]] := Ldim2_other d2 hc2.
have : (0 < #|s k|)%N by apply: leq_trans ck.
rewrite card_gt0 => /set0Pn[x xk].
have hkx : Lvalid s (k, x) by rewrite /Lvalid /= ck xk.
have jk : j != k by rewrite eq_sym.
by rewrite (diff j v k x jk hiv hkx) (diff j w k x jk hjw hkx).
Qed.

Lemma Lfacet_ker1 (s : Lcell) (b : 'I_t * 'I_p -> R) :
  Ldim s = 1%N ->
  \sum_(iv | Lvalid s iv) b iv = 0 ->
  forall iv jw, Lvalid s iv -> Lvalid s jw ->
    (-1) ^+ (Lsign s iv) * b iv = (-1) ^+ (Lsign s jw) * b jw.
Proof.
move=> e hsum [i v] [j w] hiv hjw.
have [c2 hoth] := Ldim1_shape e hiv.
have [c2' _] := Ldim1_shape e hjw.
move: c2 c2' hoth => /= c2 c2' hoth.
have ij : i = j.
  apply/eqP; apply: contraT => ij.
  have ji : j != i by rewrite eq_sym.
  by move: (hoth j ji); rewrite c2'.
move: hjw hoth c2'; rewrite -ij => hjw hoth c2'.
case: (eqVneq v w) => [->//|vw].
have hsi : s i = [set v; w].
  apply/eqP; rewrite eq_sym eqEcard cards2 vw /= c2 leqnn andbT.
  apply/subsetP => x; rewrite !inE => /orP[/eqP->|/eqP->].
    by move: hiv => /andP[_]; rewrite /=.
  by move: hjw => /andP[_]; rewrite /=.
have hsi' : s i = [set w; v] by rewrite hsi setUC.
have hrv : rkL s i v = (val w < val v)%N by apply: (rkL_pairE hsi).
have hrw : rkL s i w = (val v < val w)%N.
  by apply: (rkL_pairE hsi'); rewrite eq_sym.
have hexp : \sum_(kx | Lvalid s kx) b kx = b (i,v) + b (i,w).
  rewrite (bigD1 (i,v)) //= (bigD1 (i,w)) /=; last first.
    by rewrite hjw xpair_eqE eqxx /= eq_sym vw.
  rewrite big1 ?addr0 // => q /andP[/andP[hq q1] q2].
  exfalso; case: q hq q1 q2 => k x /= hq q1 q2.
  have ki : k = i.
    apply/eqP; apply: contraT => ki.
    by move: hq => /andP[hk _]; move: (hoth k ki); rewrite leqNgt hk.
  move: hq; rewrite ki => /andP[_]; rewrite hsi !inE => /orP[/eqP xv|/eqP xw].
  - by move: xv q1 => /= ->; rewrite ki eqxx.
  - by move: xw q2 => /= ->; rewrite ki eqxx.
move: hsum; rewrite hexp => hb.
have hbw : b (i,w) = - b (i,v).
  by move/eqP: hb; rewrite addrC addr_eq0 => /eqP.
have hpar : (rkL s i v + rkL s i w = 1)%N.
  rewrite hrv hrw.
  by case: (ltngtP (val v) (val w)) => [_|_|/val_inj e2] //;
     move: vw; rewrite e2 eqxx.
have hsg : (-1) ^+ (rkL s i v) = - (-1) ^+ (rkL s i w) :> R.
  have h : (-1) ^+ (rkL s i v) * (-1) ^+ (rkL s i w) = -1 :> R.
    by rewrite -exprD hpar expr1.
  have h2 : (-1) ^+ (rkL s i v) * ((-1) ^+ (rkL s i w) * (-1) ^+ (rkL s i w))
          = -1 * (-1) ^+ (rkL s i w) :> R.
    by rewrite mulrA h.
  by move: h2; rewrite sign_sqr mulr1 mulN1r.
rewrite /Lsign /= !exprD hsg hbw.
by rewrite mulNr mulrN mulNr.
Qed.

(** the augmentation of the boundary of a 1-dimensional simplotope vanishes *)

Lemma Lbd1_aug (s : Lcell) : Ldim s = 1%N ->
  \sum_(sig : Lcell) (Lbd1 s) sig = 0.
Proof.
move=> e; rewrite Lbd1_valid aug_bigsum.
have hd1 : (1 <= Ldim s)%N by rewrite e.
have [iv hiv] := Ldim_valid hd1.
case: iv hiv => i v hiv.
have [c2 hoth] := Ldim1_shape e hiv; move: c2 hoth => /= c2 hoth.
have [w hw hvw] : exists2 w, w \in s i & v != w.
  have : (1 < #|s i|)%N by rewrite c2.
  rewrite (cardsD1 v) (_ : (v \in s i) = true); last by move: hiv => /andP[].
  rewrite add1n ltnS card_gt0 => /set0Pn[w]; rewrite in_setD1 => /andP[wv ws].
  by exists w => //; rewrite eq_sym.
have hjw : Lvalid s (i, w) by rewrite /Lvalid /= c2 hw.
have hsi : s i = [set v; w].
  apply/eqP; rewrite eq_sym eqEcard cards2 hvw /= c2 leqnn andbT.
  apply/subsetP => x; rewrite !inE => /orP[/eqP->|/eqP->] //.
  by move: hiv => /andP[_].
have hsi' : s i = [set w; v] by rewrite hsi setUC.
have hrv : rkL s i v = (val w < val v)%N by apply: (rkL_pairE hsi).
have hrw : rkL s i w = (val v < val w)%N.
  by apply: (rkL_pairE hsi'); rewrite eq_sym.
have hpar : (rkL s i v + rkL s i w = 1)%N.
  rewrite hrv hrw.
  by case: (ltngtP (val v) (val w)) => [_|_|/val_inj e2] //;
     move: hvw; rewrite e2 eqxx.
have hsg : (-1) ^+ (rkL s i v) = - (-1) ^+ (rkL s i w) :> R.
  have h : (-1) ^+ (rkL s i v) * (-1) ^+ (rkL s i w) = -1 :> R.
    by rewrite -exprD hpar expr1.
  have h2 : (-1) ^+ (rkL s i v) * ((-1) ^+ (rkL s i w) * (-1) ^+ (rkL s i w))
          = -1 * (-1) ^+ (rkL s i w) :> R by rewrite mulrA h.
  by move: h2; rewrite sign_sqr mulr1 mulN1r.
rewrite (bigD1 (i,v)) //= (bigD1 (i,w)) /=; last first.
  by rewrite hjw xpair_eqE eqxx /= eq_sym hvw.
rewrite big1 ?addr0; last first.
  move=> q /andP[/andP[hq q1] q2].
  exfalso; case: q hq q1 q2 => k x /= hq q1 q2.
  have ki : k = i.
    apply/eqP; apply: contraT => ki.
    by move: hq => /andP[hk _]; move: (hoth k ki); rewrite /= leqNgt hk.
  move: hq; rewrite ki => /andP[_]; rewrite hsi !inE => /orP[/eqP xv|/eqP xw].
  - by move: xv q1 => /= ->; rewrite ki eqxx.
  - by move: xw q2 => /= ->; rewrite ki eqxx.
by rewrite /Lsign /= !exprD hsg mulNr addNr.
Qed.

End Ring.
End Simplotope.

Arguments Lcell : clear implicits.
Arguments Ldim {t p} s.
Arguments Lfacet {t p} s i v.
Arguments rkL {t p} s i v.
Arguments Dpre {t p} s i.
Arguments Lvalid {t p} s iv.
Arguments Lsign {t p} s iv.
Arguments Lsub {t p} s s'.
Arguments Lterm {t p R} s iv.
Arguments Lbd1 {t p R} s.
Arguments Lbd {t p R} x.
Arguments LTT {t p R} s iv jw.

(** ** the cyclic ℤ_p action on [L] *)

Section Zp.
Variables (t p : nat).
Hypothesis p_gt0 : (0 < p)%N.

Definition shp (x : 'I_p) : 'I_p := Ordinal (ltn_pmod x.+1 p_gt0).
Definition taup : 'I_p := rev_ord (Ordinal p_gt0).

Lemma val_taup : val taup = p.-1.
Proof. by rewrite /taup /= subn1. Qed.

Lemma ltn_taup (x : 'I_p) : x != taup -> (val x < p.-1)%N.
Proof.
move=> h; rewrite ltn_neqAle -ltnS (ltn_predK p_gt0) ltn_ord andbT.
by apply: contra h => /eqP e; apply/eqP/val_inj; rewrite val_taup.
Qed.

Lemma val_shp (x : 'I_p) : x != taup -> val (shp x) = (val x).+1.
Proof.
move=> h; rewrite /shp /= modn_small //.
by apply: (leq_ltn_trans (ltn_taup h)); rewrite ltn_predL.
Qed.

Lemma val_shp_taup : val (shp taup) = 0%N.
Proof. by rewrite /shp /= /taup /= subn1 (ltn_predK p_gt0) modnn. Qed.

Lemma shp_inj : injective shp.
Proof.
move=> x y e; apply/val_inj; move: (congr1 (@nat_of_ord p) e).
case: (eqVneq x taup) => [-> |hx]; case: (eqVneq y taup) => [->|hy] //.
- by rewrite val_shp_taup val_shp //.
- by rewrite val_shp_taup val_shp //.
- by rewrite !val_shp // => [] [].
Qed.

Definition Lsh (s : Lcell t p) : Lcell t p := [ffun i => shp @: s i].
Definition eA (A : {set 'I_p}) : nat := if taup \in A then (#|A| - 1)%N else 0%N.
Definition esgn (s : Lcell t p) : nat := \sum_(i : 'I_t) eA (s i).

Lemma card_Lsh s i : #|Lsh s i| = #|s i|.
Proof. by rewrite ffunE card_imset //; exact: shp_inj. Qed.

Lemma mem_Lsh s i v : (shp v \in Lsh s i) = (v \in s i).
Proof.
by rewrite ffunE; apply/imsetP/idP => [[w hw /shp_inj ->//]|h]; exists v.
Qed.

Lemma Lvalid_Lsh s i v : Lvalid (Lsh s) (i, shp v) = Lvalid s (i, v).
Proof. by rewrite /Lvalid /= card_Lsh mem_Lsh. Qed.

Lemma Lsh_facet s i v : Lfacet (Lsh s) i (shp v) = Lsh (Lfacet s i v).
Proof.
apply/ffunP => j; rewrite LfacetE /Lsh !ffunE.
case: (eqVneq j i) => [_|_] //.
apply/setP => x; rewrite !inE.
apply/andP/imsetP => [[xv /imsetP[w ws e]]|[w]].
  exists w => //; rewrite in_setD1 ws andbT.
  by apply: contra xv => /eqP ew; rewrite e ew.
rewrite in_setD1 => /andP[wv ws] ->; split.
  by apply: contra wv => /eqP/shp_inj ->.
by apply/imsetP; exists w.
Qed.

Lemma Dpre_Lsh s i : Dpre (Lsh s) i = Dpre s i.
Proof. by apply: eq_bigr => j _; rewrite card_Lsh. Qed.

Lemma rkL_taup (s : Lcell t p) i : taup \in s i -> rkL s i taup = (#|s i| - 1)%N.
Proof.
move=> h; rewrite /rkL subn1 -(card_Lfacet h).
apply: eq_card => x; rewrite !inE andbC; congr (_ && _).
case: (eqVneq x taup) => [->|hx]; first by rewrite ltnn.
by rewrite val_taup ltn_taup.
Qed.

Lemma rkL_Lsh_taup (s : Lcell t p) i : rkL (Lsh s) i (shp taup) = 0%N.
Proof.
apply/eqP; rewrite cards_eq0; apply/eqP/setP => x.
by rewrite !inE val_shp_taup ltn0 andbF.
Qed.

Lemma card_taup (A : {set 'I_p}) : #|A :&: [set taup]| = (taup \in A).
Proof.
case: (boolP (taup \in A)) => h.
  rewrite (_ : A :&: [set taup] = [set taup]) ?cards1 //.
  by apply/setP => u; rewrite !inE; case: (eqVneq u taup) => [->|_];
     rewrite ?h ?andbF ?andbT.
rewrite (_ : A :&: [set taup] = set0) ?cards0 //.
by apply/setP => u; rewrite !inE; case: (eqVneq u taup) => [->|_];
   rewrite ?(negbTE h) ?andbF.
Qed.

Lemma rkL_Lsh (s : Lcell t p) i v : v != taup ->
  rkL (Lsh s) i (shp v) = (rkL s i v + (taup \in s i))%N.
Proof.
move=> hv.
have htv : (val taup < val v)%N = false.
  by apply/negbTE; rewrite -leqNgt ltnW // val_taup ltn_taup.
rewrite /rkL.
have -> : [set x in Lsh s i | (val x < val (shp v))%N]
        = shp @: [set u in s i | (val (shp u) < val (shp v))%N].
  apply/setP => x; rewrite !inE /Lsh ffunE.
  apply/andP/imsetP => [[/imsetP[u us e] hlt]|[u]].
    by exists u => //; rewrite !inE us -e hlt.
  by rewrite !inE => /andP[us hlt] ->; split => //; apply/imsetP; exists u.
rewrite card_imset; last exact: shp_inj.
have -> : [set u in s i | (val (shp u) < val (shp v))%N]
        = [set u in s i | (val u < val v)%N] :|: (s i :&: [set taup]).
  apply/setP => u; rewrite !inE.
  case: (eqVneq u taup) => [->|hu].
    by rewrite val_shp_taup val_shp // ltn0Sn htv andbF /= andbT.
  by rewrite andbF orbF !val_shp // ltnS.
have hdisj : [set u in s i | (val u < val v)%N] :&: (s i :&: [set taup]) = set0.
  apply/setP => u; rewrite !inE.
  case: (eqVneq u taup) => [->|hu]; last by rewrite andbF !andbF.
  by rewrite htv !andbF.
have := cardsUI [set u in s i | (val u < val v)%N] (s i :&: [set taup]).
by rewrite hdisj cards0 addn0 card_taup => ->.
Qed.


(** *** the parity identity behind ℤ_p-equivariance of the boundary *)

Lemma esgn_split s i : esgn s = (eA (s i) + \sum_(j | j != i) eA (s j))%N.
Proof. by rewrite /esgn (bigD1 i). Qed.

Lemma esgn_Lfacet s i v :
  esgn (Lfacet s i v) = (eA (s i :\ v) + \sum_(j | j != i) eA (s j))%N.
Proof.
rewrite /esgn (bigD1 i) //= Lfacet_same; congr (_ + _)%N.
by apply: eq_bigr => j ji; rewrite Lfacet_diff.
Qed.

Lemma Ldim_Lsh s : Ldim (Lsh s) = Ldim s.
Proof. by apply: eq_bigr => i _; rewrite card_Lsh. Qed.

Lemma esgn_dim0 s : Ldim s = 0%N -> esgn s = 0%N.
Proof.
move=> h; apply: big1 => i _; rewrite /eA.
case: ifP => // hi.
have : (#|s i| - 1 <= Ldim s)%N by rewrite /Ldim (bigD1 i) //= leq_addr.
by rewrite h leqn0 => /eqP.
Qed.

Lemma odd_core (s : Lcell t p) i v : Lvalid s (i,v) ->
  odd (eA (s i) + rkL (Lsh s) i (shp v)) = odd (rkL s i v + eA (s i :\ v)).
Proof.
move=> /andP[h2 hv]; move: h2 hv; rewrite /= => h2 hv.
case: (eqVneq v taup) => [hvt|hvt].
  rewrite hvt rkL_Lsh_taup addn0 rkL_taup -?hvt // /eA -hvt hv.
  by rewrite in_setD1 eqxx /= addn0.
rewrite (rkL_Lsh s i hvt) /eA.
case: (boolP (taup \in s i)) => htau; last first.
  rewrite (_ : (taup \in s i :\ v) = false); last first.
    by rewrite in_setD1 (negbTE htau) andbF.
  by rewrite /= !addn0.
rewrite (_ : (taup \in s i :\ v) = true); last first.
  by rewrite in_setD1 htau andbT; apply: contra hvt => /eqP ->.
rewrite (card_Lfacet hv).
have hm : #|s i| = ((#|s i| - 2) + 2)%N by rewrite subnK.
rewrite {1}hm {2}hm -subn1 !addn2 /= !subn1 /= !oddD.
by case: (odd (#|s i| - 2)%N); case: (odd (rkL s i v)).
Qed.

Lemma odd_sign_key (s : Lcell t p) i v : Lvalid s (i,v) ->
  odd (esgn s + Lsign (Lsh s) (i, shp v))
  = odd (Lsign s (i, v) + esgn (Lfacet s i v)).
Proof.
move=> hval; have hc := odd_core hval.
rewrite /Lsign /= Dpre_Lsh (esgn_split s i) esgn_Lfacet.
move: hc; rewrite !oddD.
case: (odd (eA (s i))); case: (odd (rkL (Lsh s) i (shp v)));
case: (odd (rkL s i v)); case: (odd (eA (s i :\ v)));
case: (odd (Dpre s i)); case: (odd (\sum_(j | j != i) eA (s j))) => //=.
Qed.

Section ZpRing.
Variable R : comNzRingType.

Definition Lnu1 (s : Lcell t p) : {ffun Lcell t p -> R^o} :=
  (-1) ^+ (esgn s) *: cc (Lsh s).
Definition Lnu : {ffun Lcell t p -> R^o} -> {ffun Lcell t p -> R^o} := lin Lnu1.

Lemma LnuD x y : Lnu (x + y) = Lnu x + Lnu y. Proof. exact: linD. Qed.
Lemma LnuZ a x : Lnu (a *: x) = a *: Lnu x. Proof. exact: linZ. Qed.
Lemma Lnu_cc s : Lnu (cc s) = Lnu1 s. Proof. exact: lin_cc. Qed.
Lemma Lnu0 : Lnu 0 = 0. Proof. exact: lin0. Qed.

Lemma Lbd_Lnu1 s : Lbd (Lnu1 s) = Lnu (Lbd1 s).
Proof.
rewrite /Lnu1 LbdZ Lbd_cc Lbd1_valid scaler_sumr /Lnu.
rewrite [X in _ = lin _ X]Lbd1_valid lin_sum_cond.
rewrite (reindex_inj (h := fun q : 'I_t * 'I_p => (q.1, shp q.2))); last first.
  move=> [a x] [b y] /= [e1 e2].
  by rewrite e1; congr pair; apply: shp_inj; apply/val_inj; exact: e2.
apply: eq_big => [q|q hq].
  by rewrite Lvalid_Lsh; congr Lvalid; rewrite -surjective_pairing.
case: q hq => a x /= hq.
rewrite linZ lin_cc /Lnu1 Lsh_facet !scalerA.
congr (_ *: _); rewrite -!exprD -[LHS]signr_odd -[RHS]signr_odd.
congr ((-1) ^+ _).
have hv : Lvalid s (a,x) by rewrite -Lvalid_Lsh.
by rewrite (odd_sign_key hv).
Qed.

Lemma Lbd_Lnu x : Lbd (Lnu x) = Lnu (Lbd x).
Proof.
apply: (chain_ext (F := fun y => Lbd (Lnu y)) (G := fun y => Lnu (Lbd y))).
- by move=> c1 c2; rewrite LnuD LbdD.
- by move=> a c; rewrite LnuZ LbdZ.
- by move=> c1 c2; rewrite LbdD LnuD.
- by move=> a c; rewrite LbdZ LnuZ.
- by move=> c; rewrite Lnu_cc Lbd_cc Lbd_Lnu1.
Qed.

End ZpRing.

End Zp.

Arguments shp {p} p_gt0 x.
Arguments taup {p} p_gt0.
Arguments Lsh {t p} p_gt0 s.
Arguments eA {p} p_gt0 A.
Arguments esgn {t p} p_gt0 s.
Arguments Lnu1 {t p} p_gt0 {R} s.
Arguments Lnu {t p} p_gt0 {R} x.
