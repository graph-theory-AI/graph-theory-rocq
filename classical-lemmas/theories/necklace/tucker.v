(** * ClassicalLemmas.tucker — Stage E: the ℤ_p-simplotopal Tucker lemma

    Meunier (2014), Theorem 3.3.  This file
    (1) instantiates the abstract chain map of [chainmap.v] with the cubical
        complex [K] of [cubical.v]/[hemispheres.v] (the "Stage C glue"),
    (2) runs the induction of Meunier's proof with the hemisphere chains of
        [hemispheres.v], the chain map [η_#] of [eta.v] and the cochains of
        [bar.v], and
    (3) reads the conclusion back in the vocabulary of [necklace_complex.v]. *)

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

        Claude Opus 5       337k tokens   (09-15 14:07 -> 09-15 16:04 UTC)
        TOTAL               337k tokens   of which 105k were output

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

      [HSSZ] B. Hanke, R. Sanyal, C. Schultz, G. M. Ziegler, "Combinatorial
             Stokes formulas via minimal resolutions", Journal of Combinatorial
             Theory, Series A 116 (2009) 404-420.  (Reference [9] of [M14].)
             Local copy: classical-lemmas/HankeSSZ-Combinatorial_stokes_formulas-1-s2.0-S0097316508000988-main.pdf

    WHAT CORRESPONDS TO WHAT.

      [M14, Theorem 3.3] -- the Z_p-simplotopal version of Tucker's lemma --
      for prime p, assembled from the three objects of [M14]'s proof:
      (i) hemispheres.h, (ii) eta.eta, (iii) bar.phi.

      - [M14, Sect. 3.2], the identification of a cubical cell of R^N with a
        face (u,S) of K in the sense of necklace_complex.v, and the smallest
        simplotope of L containing its image
                                    -> uof, Sof, vert_vsel, face_inK,
                                       image_mspN, card_Sof, mspN
      - [M14, Theorem 2.4] applied to the simplotopal map mu: its hypotheses
        are discharged here and the induced chain map is obtained from
        chainmap.v
                                    -> muK, muK_bd, muK_dim, muK_equiv
      - [M14], first line of the proof of Theorem 3.3, "all chains have
        coefficients in Z_p"
                                    -> the ring is instantiated at 'F_p at the
                                       very end (pchar_Fp / pcharf0)
      - [M14], the two families to be propagated,
        "(phi_{(2l)#} o eta_# o mu_#)((sum_r nu^r) h_{2l}) = (-1)^l" and
        "(phi_{(2l+1)#} o eta_# o mu_#)((nu - id) h_{2l+1}) = (-1)^{l+1}"
                                    -> EK, Psi, Psi_bd_even, Psi_bd_odd
        (our normalisation absorbs the sign, so the invariant reads Psi ... = 1)
      - [M14], "start with l = 0 ... we use the fact that eta_# applied on a
        vertex of L provides a vertex in the first copy of Z_p"
                                    -> baseA
      - [M14], "after that, the formulas above are proved by a straightforward
        induction"
                                    -> stepA, stepB, indA, indB
      - [M14], "which shows that mu_#(h_{t(p-1)}) is nonzero and hence that
        there is an oriented t(p-1)-simplotope sigma of K whose image by mu_#
        is nonzero"
                                    -> keyD, muK_hD_neq0, key_cell
      - [M14, Theorem 3.3]          -> zp_tucker_prime *)

From mathcomp Require Import all_boot all_algebra.
From ClassicalLemmas Require Import necklace.chains necklace.necklace_complex necklace.cubical necklace.hemispheres.
From ClassicalLemmas Require Import necklace.simplotope necklace.chainmap necklace.bar necklace.eta.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Set SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.


Lemma chain_neq0 (R : nzRingType) (cell : finType) (x : {ffun cell -> R^o}) :
  x != 0 -> exists c, x c != 0.
Proof.
move=> hx; apply/existsP; rewrite -[X in is_true X]negbK; apply/negP => /existsPn h.
move/eqP: hx; apply; apply/ffunP => c; rewrite ffunE.
by move: (h c); rewrite negbK => /eqP.
Qed.

(** ** N-generic facts about the cubical complex *)

Section CubFacts.
Variables (n p N : nat).
Hypothesis p_gt0 : (0 < p)%N.
Variable R : comNzRingType.

Local Notation cM := (cellN n p N).

Lemma vsel_vtx (c : cM) T j (v : cut n p) : c j = Vtx v -> vsel c T j = v.
Proof. by move=> h; rewrite /vsel ffunE h. Qed.

Lemma vsel_edg (c : cM) T j (kr : 'I_n * 'I_p) : c j = Edg kr ->
  vsel c T j = (if j \in T then Some kr else slide (Some kr)).
Proof. by move=> h; rewrite /vsel ffunE h. Qed.

Lemma vsel_fv_top (c : cM) j T : is_edge (c j) ->
  vsel (fv c j (tc (c j))) T = vsel c (j |: T).
Proof.
case hj : (c j) => [v|kr] // _; apply/ffunP => i; rewrite /vsel !ffunE.
case: (eqVneq i j) => [->|hij]; first by rewrite /= hj !inE eqxx.
by rewrite !inE (negbTE hij) /=.
Qed.

Lemma vsel_fv_bot (c : cM) j T : is_edge (c j) ->
  vsel (fv c j (bc (c j))) T = vsel c (T :\ j).
Proof.
case hj : (c j) => [v|kr] // _; apply/ffunP => i; rewrite /vsel !ffunE.
case: (eqVneq i j) => [->|hij]; first by rewrite /= hj !inE eqxx.
by rewrite !inE (negbTE hij) /=.
Qed.

Lemma dimN_fv (c : cM) j v : is_edge (c j) -> dimN (fv c j v) = (dimN c).-1.
Proof.
move=> hj; rewrite /dimN.
have -> : [set i | is_edge (fv c j v i)] = [set i | is_edge (c i)] :\ j.
  by apply/setP => i; rewrite !inE is_edge_fv andbC.
by rewrite [in RHS](cardsD1 j) inE hj.
Qed.

Lemma bd1_supp (c f : cM) : (bd1 c : {ffun cM -> R^o}) f != 0 ->
  exists2 j, is_edge (c j) &
    f = fv c j (tc (c j)) \/ f = fv c j (bc (c j)).
Proof.
rewrite /bd1 => /supp_bigsum[j _ hj].
have hej : is_edge (c j).
  apply: contraR hj => hn.
  by rewrite (@edgeterm_novtx n p N R c j hn) ffunE eqxx.
exists j => //; move: hj; rewrite /edgeterm.
case hc : (c j) hej => [v|kr] // _.
rewrite scale_ffunE ffunE ffunE ffunE ccE /etop /ebot /tc /bc.
case: (eqVneq f (fv c j (Some kr))) => [->|h1]; first by left.
case: (eqVneq f (fv c j (slide (Some kr)))) => [->|h2]; first by right.
by rewrite subr0 mulr0 eqxx.
Qed.

Lemma bd1_aug (c : cM) : \sum_(f : cM) (bd1 c : {ffun cM -> R^o}) f = 0.
Proof.
rewrite /bd1 (eq_bigr (fun f => \sum_(j : 'I_N) (edgeterm c j : {ffun cM -> R^o}) f));
  last by move=> f _; rewrite sum_ffunE.
rewrite exchange_big /=; apply: big1 => j _.
rewrite /edgeterm; case hc : (c j) => [v|kr]; first by apply: big1 => f _; rewrite ffunE.
rewrite (eq_bigr (fun f => (-1) ^+ (rk c j) *
    ((cc (fv c j (etop kr)) : {ffun cM -> R^o}) f
     - (cc (fv c j (ebot kr)) : {ffun cM -> R^o}) f))); last first.
  by move=> f _; rewrite scale_ffunE ffunE ffunE ffunE.
by rewrite -mulr_sumr sumrB !sum_cc_aug subrr mulr0.
Qed.

Lemma inK_fv (c : cM) j : inK c -> is_edge (c j) ->
  inK (fv c j (tc (c j))) && inK (fv c j (bc (c j))).
Proof.
move=> /forallP hc hj; apply/andP; split; apply/forallP => T.
  by rewrite (vsel_fv_top T hj); exact: hc.
by rewrite (vsel_fv_bot T hj); exact: hc.
Qed.

Lemma dimN_shift (c : cM) : dimN (shift p_gt0 c) = dimN c.
Proof.
rewrite /dimN; apply: eq_card => j; rewrite !inE /shift ffunE.
by case: (c j).
Qed.

Lemma bd1_dim (c f : cM) : (bd1 c : {ffun cM -> R^o}) f != 0 ->
  dimN f = (dimN c).-1.
Proof. by move=> /bd1_supp[j hj [->|->]]; exact: dimN_fv. Qed.

End CubFacts.

(** ** the hemisphere chain [h d] is a d-chain *)

Section Homog.
Variables (n p N : nat).
Hypothesis p_gt0 : (0 < p)%N.
Hypothesis N_gt0 : (0 < N)%N.
Variable R : comNzRingType.

Local Notation cM := (cellN n p N).
Local Notation chM := {ffun cM -> R^o}.

Definition homd (k : nat) (x : chM) : Prop := forall c, x c != 0 -> dimN c = k.

Lemma homd_cc (c : cM) k : dimN c = k -> homd k (cc c).
Proof. by move=> h f; rewrite ccE; case: (eqVneq f c) => [->|_] //; rewrite eqxx. Qed.

Lemma homd0 k : homd k (0 : chM).
Proof. by move=> c; rewrite ffunE eqxx. Qed.

Lemma homd_D k (x y : chM) : homd k x -> homd k y -> homd k (x + y).
Proof.
move=> hx hy c; rewrite ffunE => hc.
have [xc|xc] := eqVneq (x c) 0; last exact: hx.
by apply: hy; move: hc; rewrite xc add0r.
Qed.

Lemma homd_N k (x : chM) : homd k x -> homd k (- x).
Proof. by move=> hx c; rewrite ffunE oppr_eq0 => hc; exact: hx. Qed.

Lemma homd_Z k a (x : chM) : homd k x -> homd k (a *: x).
Proof.
move=> hx c hc; apply: hx; apply: contraNN hc => /eqP e.
by rewrite scale_ffunE e mulr0.
Qed.

Lemma homd_sum k (I : finType) (P : pred I) (F : I -> chM) :
  (forall i, P i -> homd k (F i)) -> homd k (\sum_(i | P i) F i).
Proof. by move=> h c /supp_bigsum[i hi hc]; exact: (h i hi c hc). Qed.

Lemma homd_lin k (f : cM -> chM) (x : chM) :
  (forall c, x c != 0 -> homd k (f c)) -> homd k (lin f x).
Proof.
move=> hf; rewrite /lin; apply: homd_sum => c _.
have [xc|xc] := eqVneq (x c) 0; first by rewrite xc scale0r; exact: homd0.
by apply: homd_Z; exact: hf.
Qed.

Lemma homd_nu k (x : chM) : homd k x -> homd k (nu p_gt0 x).
Proof.
move=> hx; rewrite /nu; apply: homd_lin => c hc.
by apply: homd_cc; rewrite dimN_shift; exact: hx.
Qed.

Lemma homd_nupow r k (x : chM) : homd k x -> homd k (nupow p_gt0 r x).
Proof.
rewrite /nupow; elim: r x => [|r IH] x hx //=.
by apply: homd_nu; exact: IH.
Qed.

Lemma homd_sigma k (x : chM) : homd k x -> homd k (sigma p_gt0 x).
Proof. by move=> hx; rewrite /sigma; apply: homd_sum => r _; exact: homd_nupow. Qed.

Lemma homd_opd d k (x : chM) : homd k x -> homd k (opd p_gt0 d x).
Proof.
move=> hx; rewrite /opd; case: (odd d); last exact: homd_sigma.
by apply: homd_D; [exact: homd_nu | exact: homd_N].
Qed.

Lemma homd_bd k (x : chM) : homd k.+1 x -> homd k (bd x).
Proof.
move=> hx; rewrite /bd; apply: homd_lin => c hc f hf.
by rewrite (bd1_dim hf) (hx c hc).
Qed.

Lemma dimN_setc (c : cM) j x : ~~ is_edge (c j) -> is_edge x ->
  dimN (setc c j x) = (dimN c).+1.
Proof.
move=> hj hx; rewrite /dimN.
have -> : [set i | is_edge (setc c j x i)] = j |: [set i | is_edge (c i)].
  apply/setP => i; rewrite !inE /setc ffunE.
  by case: (eqVneq i j) => [->|_]; rewrite ?hx ?eqxx.
by rewrite cardsU1 inE hj.
Qed.

Lemma consP_supp j (X : chM) f : (consP p_gt0 j X) f != 0 ->
  exists2 c, X c != 0 & exists k : 'I_n, f = setc c j (Edg (k, p1 p_gt0)).
Proof.
rewrite /consP /lin => /supp_bigsum[c _ hc].
have hXc : X c != 0.
  by apply: contraNN hc => /eqP e; rewrite e scale0r ffunE eqxx.
exists c => //.
have hs : (\sum_(k : 'I_n) cc (setc c j (Edg (k, p1 p_gt0))) : chM) f != 0.
  by apply: contraNN hc => /eqP e; rewrite scale_ffunE e mulr0 eqxx.
move: hs => /supp_bigsum[k _ hk]; exists k.
move: hk; rewrite ccE.
by case: (eqVneq f (setc c j (Edg (k, p1 p_gt0)))) => // _; rewrite eqxx.
Qed.

Lemma homd_consP j k (X : chM) :
  homd k X -> (forall c, X c != 0 -> ~~ is_edge (c j)) ->
  homd k.+1 (consP p_gt0 j X).
Proof.
move=> hX hj f /consP_supp[c hc [kk ->]].
by rewrite dimN_setc ?(hX c hc) //; exact: hj.
Qed.

Lemma homd_htil d : (d < N)%N -> homd d (htil n R p_gt0 N_gt0 d).
Proof.
elim: d => [|d IH] hd.
  apply: homd_cc; rewrite /dimN; apply/eqP; rewrite cards_eq0; apply/eqP.
  by apply/setP => j; rewrite !inE /o_cell ffunE.
have hd' : (d < N)%N by apply: ltnW.
have hcons : homd d.+1 (consP p_gt0 (pc N_gt0 d) (htil n R p_gt0 N_gt0 d)).
  apply: homd_consP; first exact: IH.
  move=> c hc.
  have hb := @below_htil n p N R p_gt0 N_gt0 d hd'.
  by rewrite (hb c hc (pc N_gt0 d) (leqnn _)).
rewrite [htil _ _ _ _ _.+1]/=.
by case: (odd d) hcons => hcons;
   [apply: homd_D; [apply: homd_nu | apply: homd_N] | apply: homd_sigma].
Qed.

Lemma homd_h d : (d < N)%N -> homd d (h n R p_gt0 N_gt0 d).
Proof.
move=> hd; rewrite /h; apply: homd_D; last exact: homd_htil.
apply: homd_bd; apply: homd_consP; first exact: homd_htil.
move=> c hc.
have hb := @below_htil n p N R p_gt0 N_gt0 d hd.
by rewrite (hb c hc (pc N_gt0 d) (leqnn _)).
Qed.

End Homog.

(** ** the cubical complex K as a source for [chainmap.v] *)

Section Glue.
Variables (n t p : nat).
Hypothesis p_gt0 : (0 < p)%N.
Variable R : comNzRingType.
Variable lam : vertex n t p -> 'I_t -> 'I_p.

Local Notation NN := (N t p).
Local Notation cN := (cellN n p NN).

Definition Sof (c : cN) : {set 'I_NN} := [set j | is_edge (c j)].
Definition uof (c : cN) : vertex n t p := vsel c setT.
Definition mspN (c : cN) : Lcell t p :=
  [ffun i => [set lam (vsel c T) i | T in [set: {set 'I_NN}]]].

Lemma card_Sof (c : cN) : #|Sof c| = dimN c.
Proof. by []. Qed.

















Lemma mspN_ne (c : cN) i : mspN c i != set0.
Proof.
rewrite ffunE; apply/set0Pn; exists (lam (vsel c setT) i).
by apply/imsetP; exists setT; rewrite ?inE.
Qed.

Lemma mspN_mono (c f : cN) : (bd1 c : {ffun cN -> R^o}) f != 0 ->
  Lsub (mspN f) (mspN c).
Proof.
move=> /bd1_supp[j hj [->|->]]; apply/forallP => i; apply/subsetP => x;
  rewrite !ffunE => /imsetP[T _ ->]; apply/imsetP.
  by exists (j |: T); rewrite ?inE // (vsel_fv_top T hj).
by exists (T :\ j); rewrite ?inE // (vsel_fv_bot T hj).
Qed.

(** *** the bridge to the [(u, S)] presentation of a face *)

Lemma vsel_eq (c : cN) T T' : T :&: Sof c = T' :&: Sof c -> vsel c T = vsel c T'.
Proof.
move=> h; apply/ffunP => j; rewrite /vsel !ffunE.
case hc : (c j) => [v|kr] //.
have hj : j \in Sof c by rewrite inE hc.
have hin : (j \in T) = (j \in T').
  by move: hj h => /=; rewrite inE hc => _ /setP/(_ j); rewrite !inE hc /= !andbT.
by rewrite hin.
Qed.

Lemma vert_vsel (c : cN) (T : {set 'I_NN}) : T \subset Sof c ->
  vert (uof c) T = vsel c (Sof c :\: T).
Proof.
move=> hT; apply/ffunP => j; rewrite /vert /uof /vsel !ffunE.
case hc : (c j) => [v|kr].
  have hj : j \notin Sof c by rewrite inE hc.
  have hjT : j \notin T by apply: contra hj; exact: (subsetP hT).
  by rewrite (negbTE hjT).
rewrite !inE hc /=.
by case: (j \in T).
Qed.

Lemma in_XE (v : vertex n t p) : in_X v = inX v.
Proof. by []. Qed.

Lemma face_inK (c : cN) : inK c -> face (uof c) (Sof c).
Proof.
move=> hc; apply/andP; split; apply/forall_inP => x hx.
  move: hx; rewrite inE /uof /vsel ffunE.
  by case hcx : (c x) => [v|kr] //= _; rewrite inE.
rewrite powersetE in hx.
by rewrite (vert_vsel hx) in_XE; exact: (forallP hc).
Qed.

Lemma image_mspN (c : cN) i : image_set lam (uof c) (Sof c) i = mspN c i.
Proof.
apply/setP => x; rewrite ffunE; apply/imsetP/imsetP => [[T hT ->]|[T _ ->]].
  rewrite powersetE in hT.
  by exists (Sof c :\: T); rewrite ?inE // (vert_vsel hT).
exists (Sof c :\: (T :&: Sof c)); first by rewrite powersetE subsetDl.
rewrite (vert_vsel (subsetDl _ _)) (sub_setD (subsetIr T (Sof c))).
congr (lam _ i); apply: (@vsel_eq c T (T :&: Sof c)).
by rewrite -setIA setIid.
Qed.

(** *** the ℤ_p action on K *)

Lemma vsel_shift (c : cN) (T : {set 'I_NN}) :
  vsel (shift p_gt0 c) T = shift_vertex p_gt0 (vsel c T).
Proof.
apply/ffunP => j; rewrite /vsel /shift /shift_vertex !ffunE /shift_cut.
case hc : (c j) => [v|[k r]] //=.
case: (j \in T) => //=.
by case: (k == 0 :> nat).
Qed.



Lemma inX_shift (v : vertex n t p) : inX (shift_vertex p_gt0 v) = inX v.
Proof.
have hcov : forall j b, covers ((shift_vertex p_gt0 v) j) b = covers (v j) b.
  move=> j b; rewrite /shift_vertex ffunE /shift_cut.
  by case: (v j) => [[k r]|].
by apply/forallP/forallP => h b; have := h b => /existsP[j hj]; apply/existsP;
   exists j; move: hj; rewrite ?hcov // -hcov.
Qed.

Lemma inK_shift (c : cN) : inK c -> inK (shift p_gt0 c).
Proof.
move=> /forallP hc; apply/forallP => T.
by rewrite vsel_shift inX_shift; exact: hc.
Qed.

(** *** the induced chain map for K *)

Section Induced.
Hypothesis hsimp : simplotopal lam.

Lemma mspN_dim (c : cN) : inK c -> (Ldim (mspN c) <= dimN c)%N.
Proof.
move=> hc; rewrite -card_Sof.
have hh := hsimp (face_inK hc).
rewrite /Ldim (eq_bigr (fun i => (#|image_set lam (uof c) (Sof c) i| - 1)%N)).
  exact: hh.
by move=> i _; rewrite image_mspN.
Qed.

Let hokf (c f : cN) : inK c -> (bd1 c : {ffun cN -> R^o}) f != 0 -> inK f.
Proof. by move=> hc /bd1_supp[j hj [->|->]]; move: (inK_fv hc hj) => /andP[]. Qed.

Let hdim (c f : cN) : inK c -> (bd1 c : {ffun cN -> R^o}) f != 0 ->
  dimN f = (dimN c).-1.
Proof. by move=> _ /bd1_supp[j hj [->|->]]; exact: dimN_fv. Qed.

Let hdim0 (c : cN) : inK c -> dimN c = 0%N -> (bd1 c : {ffun cN -> R^o}) = 0.
Proof.
move=> _ h0; rewrite /bd1 big1 // => j _; apply: edgeterm_novtx.
apply/negP => hj.
have : j \in [set i | is_edge (c i)] by rewrite inE.
by move: h0; rewrite /dimN => /eqP; rewrite cards_eq0 => /eqP ->; rewrite inE.
Qed.

Let hbdbd (c : cN) : inK c -> bd (bd1 c : {ffun cN -> R^o}) = 0.
Proof. by move=> _; rewrite -(bd_cc c) bd_bd. Qed.

Let haug (c : cN) : inK c -> (0 < dimN c)%N ->
  \sum_(f : cN) (bd1 c : {ffun cN -> R^o}) f = 0.
Proof. by move=> _ _; exact: bd1_aug. Qed.

Let hne (c : cN) i : mspN c i != set0. Proof. exact: mspN_ne. Qed.

Let hmono (c f : cN) : inK c -> (bd1 c : {ffun cN -> R^o}) f != 0 ->
  Lsub (mspN f) (mspN c).
Proof. by move=> _; exact: mspN_mono. Qed.

Let hmdim (c : cN) : inK c -> (Ldim (mspN c) <= dimN c)%N.
Proof. exact: mspN_dim. Qed.

Definition muK : {ffun cN -> R^o} -> {ffun Lcell t p -> R^o} :=
  chainmap.mu dimN (@bd1 n p NN R) mspN.
Definition muK1 (c : cN) : {ffun Lcell t p -> R^o} :=
  chainmap.mu1 dimN (@bd1 n p NN R) mspN c.

Lemma muK_linE (x : {ffun cN -> R^o}) : muK x = lin muK1 x.
Proof. by []. Qed.

Lemma muK_bd (x : {ffun cN -> R^o}) : (forall c, x c != 0 -> inK c) ->
  Lbd (muK x) = muK (bd x).
Proof. exact: (chainmap.mu_bd hokf hdim hdim0 hbdbd haug hne hmono hmdim). Qed.

Lemma muK_dim (c : cN) : inK c -> muK1 c != 0 -> Ldim (mspN c) = dimN c.
Proof. exact: (chainmap.mu_dim hokf hdim hdim0 hbdbd haug hne hmono hmdim). Qed.

Hypothesis hequiv : equivariant p_gt0 lam.

Lemma mspN_shift (c : cN) : inK c -> mspN (shift p_gt0 c) = Lsh p_gt0 (mspN c).
Proof.
move=> hc; apply/ffunP => i; rewrite /Lsh !ffunE.
apply/setP => x; apply/imsetP/imsetP => [[T _ ->]|[y hy ->]].
  exists (lam (vsel c T) i); first by apply/imsetP; exists T; rewrite ?inE.
  by rewrite vsel_shift (hequiv (forallP hc T) i).
move: hy => /imsetP[T _ ->].
by exists T; rewrite ?inE // vsel_shift (hequiv (forallP hc T) i).
Qed.

Lemma muK_equiv (x : {ffun cN -> R^o}) : (forall c, x c != 0 -> inK c) ->
  muK (nu p_gt0 x) = Lnu p_gt0 (muK x).
Proof.
move=> hx; rewrite /nu.
have h1 : forall c : cN, inK c -> inK (shift p_gt0 c).
  by move=> c; exact: inK_shift.
have h2 : forall c : cN, dimN (shift p_gt0 c) = dimN c.
  by move=> c; exact: dimN_shift.
have h3 : forall c : cN, inK c -> mspN (shift p_gt0 c) = Lsh p_gt0 (mspN c).
  by move=> c; exact: mspN_shift.
have h4 : forall c : cN, inK c ->
  (bd1 (shift p_gt0 c) : {ffun cN -> R^o})
  = lin (fun f : cN => cc (shift p_gt0 f)) (bd1 c).
  by move=> c _; exact: bd1_shift.
have HH := @chainmap.mu_equiv t p R cN dimN (@bd1 n p NN R) (@inK n p NN) mspN
  hokf hdim hdim0 hbdbd haug hne hmono hmdim p_gt0 (shift p_gt0) h1 h2 h3 h4 x hx.
exact: HH.
Qed.

(** ** the assembly (Meunier, proof of Theorem 3.3) *)

Hypothesis n_gt0 : (0 < n)%N.
Hypothesis t_gt0 : (0 < t)%N.
Hypothesis p_prime : prime p.
Hypothesis pR : (p%:R = 0 :> R).

Let NNgt0 : (0 < NN)%N := ltn0Sn _.

Local Notation hK := (@hemispheres.h n p NN R p_gt0 NNgt0).
Local Notation etaL := (@eta.eta t p p_gt0 t_gt0 R).
Local Notation phiB := (@bar.phi p NN R).
Local Notation nuK := (@hemispheres.nu n p NN R p_gt0).
Local Notation sigK := (@hemispheres.sigma n p NN R p_gt0).
Local Notation nupowK := (@hemispheres.nupow n p NN R p_gt0).
Local Notation nuBB := (@bar.nuB p NN p_gt0 R).

Definition EK (x : {ffun cN -> R^o}) := etaL (muK x).
Definition Psi (d : nat) (x : {ffun cN -> R^o}) : R := phiB d (EK x).

Definition goodK (x : {ffun cN -> R^o}) : Prop :=
  forall c, x c != 0 -> inK c /\ (dimN c < t * p.-1)%N.

Lemma goodK_inK x : goodK x -> forall c, x c != 0 -> inK c.
Proof. by move=> h c hc; move: (h c hc) => []. Qed.

Lemma muK_supp (x : {ffun cN -> R^o}) s : (muK x) s != 0 ->
  exists2 c, x c != 0 & muK1 c != 0 /\ s = mspN c.
Proof.
rewrite muK_linE /lin => /supp_bigsum[c _ hc].
have hx : x c != 0 by apply: contraNN hc => /eqP e; rewrite e scale0r ffunE eqxx.
exists c => //.
have hm : (muK1 c) s != 0.
  by apply: contraNN hc => /eqP e; rewrite scale_ffunE e mulr0 eqxx.
split.
  by apply/eqP => e; move: hm; rewrite e ffunE eqxx.
have [a ha] := chainmap.mu1_shape dimN (@bd1 n p NN R) mspN c.
move: hm; rewrite /muK1 ha scale_ffunE ccE.
by case: (eqVneq s (mspN c)) => // _; rewrite mulr0 eqxx.
Qed.

Lemma goodK_okL x : goodK x -> forall s, (muK x) s != 0 -> eta.okL s.
Proof.
move=> hx s /muK_supp[c hc [hm ->]].
have [hin hd] := hx c hc.
rewrite /eta.okL; apply/andP; split.
  by apply/forallP => i; exact: mspN_ne.
apply/eqP => e; move: hd; rewrite -(muK_dim hin hm) e eta.Ldim_topL.
by rewrite ltnn.
Qed.

Lemma goodK_nu x : goodK x -> goodK (nuK x).
Proof.
move=> hx c hc.
have [c0 hc0 <-] := lin_cc_supp (g := shift p_gt0) hc.
have [hin hd] := hx c0 hc0.
by rewrite dimN_shift; split => //; exact: inK_shift.
Qed.

Lemma goodK_nupow r x : goodK x -> goodK (nupowK r x).
Proof.
rewrite /nupow; elim: r x => [|r IH] x hx //=.
by apply: goodK_nu; exact: IH.
Qed.

Lemma goodK_h d : (d < t * p.-1)%N -> goodK (hK d).
Proof.
move=> hd; have hdN : (d < NN)%N by rewrite ltnW.
move=> c hc; split.
  by have := @h_inK n p NN R n_gt0 p_gt0 pR NNgt0 d hdN c hc.
by have := @homd_h n p NN p_gt0 NNgt0 R d hdN c hc => ->.
Qed.

(** *** [Psi] is linear *)

Lemma PsiD d x y : Psi d (x + y) = Psi d x + Psi d y.
Proof. by rewrite /Psi /EK muK_linE linD eta.etaD bar.phiD. Qed.

Lemma PsiZ d a x : Psi d (a *: x) = a * Psi d x.
Proof. by rewrite /Psi /EK muK_linE linZ eta.etaZ bar.phiZ. Qed.

Lemma PsiN d x : Psi d (- x) = - Psi d x.
Proof. by rewrite -scaleN1r PsiZ mulN1r. Qed.

Lemma Psi_sum d (I : finType) (F : I -> {ffun cN -> R^o}) :
  Psi d (\sum_(i : I) F i) = \sum_(i : I) Psi d (F i).
Proof.
rewrite /Psi /EK muK_linE lin_sum_cond.
rewrite (@eta.eta_sum t p p_gt0 t_gt0 R I (fun i => lin muK1 (F i))).
by rewrite bar.phi_sum.
Qed.

(** *** the two Stokes relations transported to K *)

Lemma EK_nu x : goodK x -> EK (nuK x) = nuBB (EK x).
Proof.
move=> hx; rewrite /EK (muK_equiv (goodK_inK hx)).
by have := @eta.eta_equivariant t p p_gt0 p_prime t_gt0 R (muK x) (goodK_okL hx) => ->.
Qed.

Lemma EK_nupow r x : goodK x -> EK (nupowK r x) = iter r nuBB (EK x).
Proof.
elim: r x => [|r IH] x hx; first by rewrite /nupow /=.
rewrite /nupow iterSr -/(nupow p_gt0 r (nuK x)) (IH _ (goodK_nu hx)).
by rewrite (EK_nu hx) -iterSr.
Qed.

Lemma Psi_bd_even l x : ((2 * l).+2 <= NN)%N -> goodK x ->
  Psi (2 * l) (bd x) = Psi (2 * l).+1 (nuK x) - Psi (2 * l).+1 x.
Proof.
move=> hM hx; rewrite /Psi /EK -(muK_bd (goodK_inK hx)).
have hch := @eta.eta_chainmap t p p_gt0 p_prime t_gt0 R (muK x) (goodK_okL hx).
rewrite -/(Lbd (muK x)) -hch (@bar.phi_bd_even p NN p_gt0 R l (EK x) hM).
by congr (_ - _); rewrite -(EK_nu hx).
Qed.

Lemma Psi_bd_odd l x : ((2 * l).+3 <= NN)%N -> goodK x ->
  Psi (2 * l).+1 (bd x) = \sum_(r < p) Psi (2 * l).+2 (nupowK r x).
Proof.
move=> hM hx.
rewrite (eq_bigr (fun r : 'I_p => phiB (2*l).+2 (iter (val r) nuBB (EK x))));
  last by move=> r _; rewrite /Psi (EK_nupow (val r) hx).
rewrite /Psi /EK -(muK_bd (goodK_inK hx)).
have hch := @eta.eta_chainmap t p p_gt0 p_prime t_gt0 R (muK x) (goodK_okL hx).
rewrite -/(Lbd (muK x)) -hch.
exact: (@bar.phi_bd_odd p NN p_gt0 R l (EK x) hM).
Qed.

(** *** the induction of the proof of Theorem 3.3 *)

Let D := (t * p.-1)%N.

Lemma D_gt0 : (0 < D)%N.
Proof. by rewrite /D muln_gt0 t_gt0 /= -subn1 subn_gt0 prime_gt1. Qed.

Lemma muK1_dim0 (c : cN) : dimN c = 0%N -> muK1 c = cc (mspN c).
Proof. by move=> h0; rewrite /muK1 /chainmap.mu1 h0. Qed.

Lemma baseA : Psi 0 (sigK (hK 0)) = 1.
Proof.
have hg : goodK (hK 0) by apply: goodK_h; exact: D_gt0.
rewrite /sigma Psi_sum.
rewrite (eq_bigr (fun r : 'I_p => phiB 0 (iter (val r) nuBB (EK (hK 0)))));
  last by move=> r _; rewrite /Psi (EK_nupow (val r) hg).
have [c0 hc0] : exists c0 : cN, hK 0 = cc c0.
  exists (setc (o_cell n p NN) (pc NNgt0 0) (Vtx (topv n_gt0 p_gt0))).
  exact: (@h0_val n p NN R n_gt0 p_gt0 NNgt0).
have hcc0 : (hK 0) c0 != 0 by rewrite hc0 ccE eqxx oner_neq0.
have hd0 : dimN c0 = 0%N by have := @homd_h n p NN p_gt0 NNgt0 R 0 NNgt0 c0 hcc0.
have hin0 : inK c0 by have := @h_inK n p NN R n_gt0 p_gt0 pR NNgt0 0 NNgt0 c0 hcc0.
have hL0 : Ldim (mspN c0) = 0%N.
  by apply/eqP; rewrite -leqn0 -hd0; exact: (hmdim hin0).
have hok0 : eta.okL (mspN c0).
  rewrite /eta.okL; apply/andP; split; first by apply/forallP => i; exact: mspN_ne.
  apply/eqP => e; move: hL0; rewrite e eta.Ldim_topL => e2.
  by move: D_gt0; rewrite /D e2 ltnn.
rewrite /EK hc0 muK_linE lin_cc (muK1_dim0 hd0) eta.eta_cc.
rewrite (eta.eta_vertex p_gt0 t_gt0 R hok0 hL0).
apply: (@bar.phi0_orbit p NN p_gt0 R).
by rewrite bar.sq_padd.
Qed.

Lemma stepA l : ((2 * l).+1 < D)%N -> Psi (2 * l) (sigK (hK (2 * l))) = 1 ->
  Psi (2 * l).+1 (nuK (hK (2 * l).+1) - hK (2 * l).+1) = 1.
Proof.
move=> hl hA.
have hM : ((2 * l).+1 < NN)%N by rewrite /NN ltnS ltnW.
have hg : goodK (hK (2 * l).+1) by apply: goodK_h.
have hb := @Psi_bd_even l (hK (2 * l).+1) hM hg.
move: hb; rewrite (@hrel_odd n p NN R p_gt0 pR NNgt0 l) hA => hb.
by rewrite PsiD PsiN -hb.
Qed.

Lemma stepB l : ((2 * l).+2 < D)%N ->
  Psi (2 * l).+1 (nuK (hK (2 * l).+1) - hK (2 * l).+1) = 1 ->
  Psi (2 * (l.+1)) (sigK (hK (2 * (l.+1)))) = 1.
Proof.
move=> hl hB.
have hM : ((2 * l).+2 < NN)%N by rewrite /NN ltnS ltnW.
have he : (2 * l.+1 = (2 * l).+2)%N by rewrite mulnSr addn2.
have hg : goodK (hK (2 * l).+2) by apply: goodK_h.
have hb := @Psi_bd_odd l (hK (2 * l).+2) hM hg.
move: hb; rewrite (@hrel_even n p NN R p_gt0 pR NNgt0 l) hB => hb.
by rewrite he /sigma Psi_sum -hb.
Qed.

Lemma indA : forall l, (2 * l < D)%N -> Psi (2 * l) (sigK (hK (2 * l))) = 1.
Proof.
elim=> [|l IH] hl; first by rewrite muln0; exact: baseA.
have he : (2 * l.+1 = (2 * l).+2)%N by rewrite mulnSr addn2.
have hl2 : ((2 * l).+2 < D)%N by rewrite -he.
have h2 : (2 * l < D)%N by apply: ltn_trans hl2; rewrite ltnS leqnSn.
apply: (@stepB l hl2).
by apply: (@stepA l (ltnW hl2)); exact: IH.
Qed.

Lemma indB : forall l, ((2 * l).+1 < D)%N ->
  Psi (2 * l).+1 (nuK (hK (2 * l).+1) - hK (2 * l).+1) = 1.
Proof.
move=> l hl; apply: (@stepA l hl); apply: indA.
by apply: ltn_trans hl; rewrite ltnSn.
Qed.

Lemma keyD : Psi D.-1 (bd (hK D)) = 1.
Proof.
have hD := D_gt0.
case hpar : (odd D.-1).
  have [l hl] : exists l, D.-1 = (2 * l).+1.
    by exists (D.-1)./2; rewrite -[in LHS](odd_double_half D.-1) hpar mul2n.
  have hlt : ((2 * l).+1 < D)%N by rewrite -hl ltn_predL.
  have hDe : D = (2 * l).+2 by rewrite -hl prednK.
  rewrite hl hDe (@hrel_even n p NN R p_gt0 pR NNgt0 l).
  exact: (@indB l hlt).
have [l hl] : exists l, D.-1 = (2 * l)%N.
  by exists (D.-1)./2; rewrite -[in LHS](odd_double_half D.-1) hpar mul2n.
have hlt : (2 * l < D)%N by rewrite -hl ltn_predL.
have hDe : D = (2 * l).+1 by rewrite -hl prednK.
rewrite hl hDe (@hrel_odd n p NN R p_gt0 pR NNgt0 l).
exact: (@indA l hlt).
Qed.

(** *** extraction of the top face *)

Lemma muK_hD_neq0 : muK (hK D) != 0.
Proof.
have hin : forall c, (hK D) c != 0 -> inK c.
  by move=> c hc; have := @h_inK n p NN R n_gt0 p_gt0 pR NNgt0 D (ltnSn _) c hc.
apply/eqP => e.
have h1 := keyD.
move: h1; rewrite /Psi /EK -(muK_bd hin) e /Lbd lin0 eta.eta0 bar.phi0 => /esym/eqP.
by rewrite oner_eq0.
Qed.

Lemma key_cell : exists c : cN,
  [/\ inK c, dimN c = D & forall i, mspN c i = setT].
Proof.
have hin : forall c, (hK D) c != 0 -> inK c.
  by move=> c hc; have := @h_inK n p NN R n_gt0 p_gt0 pR NNgt0 D (ltnSn _) c hc.
have [s hs] := chain_neq0 muK_hD_neq0.
have [c hc [hm _]] := muK_supp hs.
have hd : dimN c = D by have := @homd_h n p NN p_gt0 NNgt0 R D (ltnSn _) c hc.
have hLd : Ldim (mspN c) = (t * p.-1)%N by rewrite (muK_dim (hin c hc) hm) hd.
have hnok : ~~ eta.okL (mspN c).
  apply/negP => hok.
  by move: (eta.okL_Ldim p_gt0 hok); rewrite hLd ltnn.
have htop : mspN c = eta.topL t p.
  move: hnok; rewrite /eta.okL negb_and.
  have -> : [forall i, mspN c i != set0] by apply/forallP => i; exact: mspN_ne.
  by rewrite /= negbK => /eqP.
exists c; split; [exact: (hin c hc) | exact: hd | ].
by move=> i; rewrite htop /eta.topL ffunE.
Qed.

End Induced.

End Glue.



(** ** Theorem 3.3 of Meunier (2014): the ℤ_p-simplotopal Tucker lemma,
       prime case. *)

Theorem zp_tucker_prime (n t p : nat) (p_gt0 : (0 < p)%N) :
  prime p -> (0 < t)%N -> @zp_tucker n t p p_gt0.
Proof.
move=> p_prime t_gt0 n_gt0 mu hequiv hsimp.
pose Rp : comNzRingType := 'F_p.
have pR : (p%:R = 0 :> Rp) by apply: pcharf0; exact: pchar_Fp.
have [c [hin hd hmsp]] :=
  @key_cell n t p p_gt0 Rp mu hsimp hequiv n_gt0 t_gt0 p_prime pR.
exists (uof c), (Sof c); split.
- exact: face_inK hin.
- by rewrite card_Sof hd.
- by move=> i; rewrite image_mspN hmsp.
Qed.

Print Assumptions zp_tucker_prime.
