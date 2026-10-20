(** * ClassicalLemmas.chainmap — the chain map induced by a simplotopal map

    Meunier (2014), Theorem 2.4, for a target [L = (Δ_{p-1})^t].

    The source is an abstract graded chain complex ([cellS], [dimS], [bdS1])
    together with a predicate [okS] singling out the subcomplex on which the
    map is defined (in the application: the faces of [K]), and a map [msp]
    sending a cell to the smallest simplotope of [L] containing its image.
    The simplotopal hypothesis is [msp_dim : Ldim (msp c) <= dimS c].

    We build [mu1 c = α_c ⋅ (msp c)] by induction on [dimS c], exactly as in
    Meunier's proof: the boundary [∂c] is mapped into the facets of [msp c],
    [∂(μ_# ∂c) = 0], so all the facet coefficients agree by [Lfacet_ker2]
    (dimension ≥ 2) or by an augmentation argument ([Lfacet_ker1], dimension 1),
    and [α_c] is their common value.

    Deliverables: [mu_bd] (μ_# is a chain map) and [mu_dim] (if [μ_#σ ≠ 0] then
    [μ] maps [σ] onto a simplotope of the same dimension). *)

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

        Claude Opus 5       123k tokens   (09-15 09:01 -> 09-15 14:18 UTC)
        TOTAL               123k tokens   of which 41k were output

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

      [M14, Theorem 2.4], the chain map induced by a simplotopal map, stated
      over an abstract graded source complex so that it can be applied to the
      cubical complex of cubical.v.

      - [M14, Theorem 2.4], "given a simplotopal map lambda : V(S) -> V(T),
        there exists a unique chain map lambda_# ..."
                                    -> mu1, mu, mu_bd
      - [M14], proof of Theorem 2.4: the recursion on the dimension, and the
        common value alpha_sigma supplied by [M14, Lemma 2.1]
                                    -> alphaOf, muP, mu1_shape
      - [M14], end of the proof of Theorem 3.3, "there is an oriented
        t(p-1)-simplotope sigma of K whose image by mu_# is nonzero", i.e. a
        cell whose image has full dimension
                                    -> mu_dim
      - [M14, Sect. 3.3], the induced chain map is equivariant
                                    -> mu_nu1, mu_equiv *)

From mathcomp Require Import all_boot all_algebra.
From ClassicalLemmas Require Import necklace.chains necklace.simplotope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Set SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.

Section Induced.
Variables (t p : nat) (R : comNzRingType).
Variable cellS : finType.
Variable dimS : cellS -> nat.
Variable bdS1 : cellS -> {ffun cellS -> R^o}.
Variable okS : pred cellS.
Variable msp : cellS -> Lcell t p.

Local Notation chainS := {ffun cellS -> R^o}.
Local Notation chainL := {ffun Lcell t p -> R^o}.

Definition bdS : chainS -> chainS := lin bdS1.

Hypothesis ok_facet : forall c f, okS c -> bdS1 c f != 0 -> okS f.
Hypothesis bdS_dim  : forall c f, okS c -> bdS1 c f != 0 -> dimS f = (dimS c).-1.
Hypothesis bdS_dim0 : forall c, okS c -> dimS c = 0%N -> bdS1 c = 0.
Hypothesis bdS_bdS  : forall c, okS c -> bdS (bdS1 c) = 0.
Hypothesis bdS_aug  : forall c, okS c -> (0 < dimS c)%N ->
  \sum_(f : cellS) bdS1 c f = 0.
Hypothesis msp_ne   : forall c i, msp c i != set0.
Hypothesis msp_mono : forall c f, okS c -> bdS1 c f != 0 -> Lsub (msp f) (msp c).
Hypothesis msp_dim  : forall c, okS c -> (Ldim (msp c) <= dimS c)%N.

(** ** the coefficient extracted from a facet chain *)

Definition alphaOf (s : Lcell t p) (z : chainL) : R :=
  if [pick iv | Lvalid s iv] is Some iv
  then (-1) ^+ (Lsign s iv) * z (Lfacet s iv.1 iv.2) else 0.

Lemma alphaOf0 s : alphaOf s 0 = 0.
Proof. by rewrite /alphaOf; case: pickP => [iv _|_] //; rewrite ffunE mulr0. Qed.

(** ** the induced map *)

Fixpoint mf (d : nat) (c : cellS) : chainL :=
  if d is d'.+1 then alphaOf (msp c) (lin (mf d') (bdS1 c)) *: cc (msp c)
  else cc (msp c).

Definition mu1 (c : cellS) : chainL := mf (dimS c) c.
Definition mu : chainS -> chainL := lin mu1.

Lemma mu_cc c : mu (cc c) = mu1 c. Proof. exact: lin_cc. Qed.
Lemma muD x y : mu (x + y) = mu x + mu y. Proof. exact: linD. Qed.
Lemma muZ a x : mu (a *: x) = a *: mu x. Proof. exact: linZ. Qed.
Lemma mu0 : mu 0 = 0. Proof. exact: lin0. Qed.

Lemma mu1_shape c : exists a : R, mu1 c = a *: cc (msp c).
Proof.
rewrite /mu1; case: (dimS c) => [|d]; first by exists 1; rewrite scale1r.
by exists (alphaOf (msp c) (lin (mf d) (bdS1 c))).
Qed.

Lemma mu1_supp c sig : mu1 c sig != 0 -> sig = msp c.
Proof.
have [a ->] := mu1_shape c; rewrite scale_ffunE ccE.
by case: (eqVneq sig (msp c)) => // _; rewrite mulr0 eqxx.
Qed.

(** ** two auxiliary facts about chains of [L] *)

Lemma aug_cc (x : Lcell t p) : \sum_(sig : Lcell t p) (cc x : chainL) sig = 1.
Proof.
by rewrite (bigD1 x) //= ccE eqxx big1 ?addr0 // => sig h; rewrite ccE (negbTE h).
Qed.

Lemma aug_sum (I : finType) (P : pred I) (F : I -> Lcell t p) (b : I -> R) :
  \sum_(sig : Lcell t p) (\sum_(i | P i) b i *: cc (F i) : chainL) sig
  = \sum_(i | P i) b i.
Proof.
rewrite (eq_bigr (fun sig => \sum_(i | P i) (b i *: (cc (F i) : chainL)) sig));
  last by move=> sig _; rewrite sum_ffunE.
rewrite exchange_big /=; apply: eq_bigr => i _.
rewrite (eq_bigr (fun sig => b i * (cc (F i) : chainL) sig)); last first.
  by move=> sig _; rewrite scale_ffunE.
by rewrite -mulr_sumr aug_cc mulr1.
Qed.

Lemma facet_decomp (s : Lcell t p) (z : chainL) :
  (forall sig, z sig != 0 -> exists iv, Lvalid s iv /\ sig = Lfacet s iv.1 iv.2) ->
  z = \sum_(iv | Lvalid s iv) z (Lfacet s iv.1 iv.2) *: cc (Lfacet s iv.1 iv.2).
Proof.
move=> h; apply/ffunP => sig; rewrite sum_ffunE.
case: (altP (z sig =P 0)) => [hz|hz].
  rewrite hz big1 // => iv hiv; rewrite scale_ffunE ccE.
  case: (eqVneq sig (Lfacet s iv.1 iv.2)) => [e|_]; last by rewrite mulr0.
  by rewrite -e hz mul0r.
have [iv [hiv hsig]] := h sig hz.
rewrite (bigD1 iv) //= scale_ffunE ccE -hsig eqxx mulr1.
rewrite big1 ?addr0 // => jw /andP[hjw jwiv]; rewrite scale_ffunE ccE.
case: (eqVneq sig (Lfacet s jw.1 jw.2)) => [e|_]; last by rewrite mulr0.
have ejw : jw = iv by apply: (Lfacet_inj hjw hiv); rewrite -e hsig.
by rewrite ejw eqxx in jwiv.
Qed.

(** ** the main induction *)

Lemma muP : forall d c, okS c -> dimS c = d ->
  (mu1 c != 0 -> Ldim (msp c) = dimS c) /\ Lbd (mu1 c) = mu (bdS1 c).
Proof.
elim=> [|d IH] c okc dc.
  have hd0 : Ldim (msp c) = 0%N.
    by apply/eqP; rewrite -leqn0 -dc; exact: msp_dim.
  split; first by move=> _; rewrite dc.
  rewrite /mu1 dc /= Lbd_cc.
  have -> : Lbd1 (msp c) = 0 :> chainL.
    rewrite Lbd1_valid big1 // => iv hiv.
    by move: (Lvalid_dim hiv); rewrite hd0.
  by rewrite (bdS_dim0 okc dc) mu0.
set s' := msp c.
have hfacet : forall f, bdS1 c f != 0 -> okS f /\ dimS f = d.
  move=> f hf; split; first exact: (ok_facet okc hf).
  by rewrite (bdS_dim okc hf) dc.
have hmf : lin (mf d) (bdS1 c) = mu (bdS1 c).
  by apply: lin_eq_supp => f hf; have [_ e] := hfacet f hf; rewrite /mu1 e.
set z := mu (bdS1 c).
have hmu1 : mu1 c = alphaOf s' z *: cc s' by rewrite /mu1 dc /= hmf.
have hIH : forall f, bdS1 c f != 0 ->
    (mu1 f != 0 -> Ldim (msp f) = d) /\ Lbd (mu1 f) = mu (bdS1 f).
  move=> f hf; have [okf df] := hfacet f hf.
  have [h1 h2] := IH f okf df.
  by split => // hn; rewrite -df; exact: h1.
have hbdz : Lbd z = 0.
  rewrite /z /mu /Lbd lin_comp.
  have -> : lin (fun x : cellS => lin Lbd1 (mu1 x)) (bdS1 c)
          = lin (fun f => lin mu1 (bdS1 f)) (bdS1 c).
    by apply: lin_eq_supp => f hf; have [_ e] := hIH f hf; move: e; rewrite /Lbd /mu.
  have -> : lin (fun f => lin mu1 (bdS1 f)) (bdS1 c) = lin mu1 (lin bdS1 (bdS1 c)).
    by rewrite lin_comp.
  by rewrite -/(bdS (bdS1 c)) (bdS_bdS okc) lin0.
have hzsupp : forall sig, z sig != 0 ->
    exists f, [/\ bdS1 c f != 0, mu1 f != 0, sig = msp f,
               Ldim (msp f) = d & Lsub (msp f) s'].
  move=> sig hsig.
  have [f hf] : exists f, (bdS1 c f != 0) && (mu1 f sig != 0).
    apply/existsP; apply: contraR hsig => /existsPn h.
    rewrite /z /mu /lin sum_ffunE big1 // => f _.
    move: (h f); rewrite negb_and => /orP[/negPn/eqP e|/negPn/eqP e];
      by rewrite scale_ffunE e ?mul0r ?mulr0.
  move: hf => /andP[hf1 hf2].
  have hne : mu1 f != 0 by apply/eqP => e; move: hf2; rewrite e ffunE eqxx.
  have [h1 _] := hIH f hf1.
  by exists f; split => //;
     [exact: mu1_supp | exact: h1 | exact: (msp_mono okc hf1)].
case: (altP (Ldim s' =P dimS c)) => [hdim|hdim]; last first.
  have hle : (Ldim s' <= d)%N.
    move: (msp_dim okc); rewrite dc leq_eqVlt ltnS => /orP[/eqP e|//].
    by move: hdim; rewrite e dc eqxx.
  have hz0 : z = 0.
    case: (altP (Ldim s' =P d)) => [hd|hd]; last first.
      rewrite /z /mu /lin big1 // => f _.
      case: (altP (bdS1 c f =P 0)) => [->|hf]; first by rewrite scale0r.
      have hmf0 : mu1 f = 0.
        apply/eqP; apply: contraT => hne.
        have [h1 _] := hIH f hf.
        have hdf : Ldim (msp f) = d by exact: h1.
        have hge : (d <= Ldim s')%N.
          by rewrite -hdf; exact: (Ldim_sub (msp_mono okc hf)).
        by move: hd; rewrite eqn_leq hle hge.
      by rewrite hmf0 scaler0.
    have hzero : forall f, bdS1 c f != 0 -> mu1 f != 0 -> msp f = s'.
      move=> f hf1 hne; have [h1 _] := hIH f hf1.
      apply: (Lsub_eq (msp_mono okc hf1) (msp_ne f)).
      by rewrite (h1 hne) hd.
    have hsupp1 : forall sig, z sig != 0 -> sig = s'.
      move=> sig hsig; have [f [hf1 hf2 hf3 _ _]] := hzsupp sig hsig.
      by rewrite hf3 (hzero f hf1 hf2).
    have hz : z = z s' *: cc s' by apply: chain_supp1.
    have hgam : z s' = 0.
      case: (posnP d) => [d0|dpos].
        have -> : z s' = \sum_(f : cellS) bdS1 c f.
          rewrite /z /mu /lin sum_ffunE; apply: eq_bigr => f _.
          rewrite scale_ffunE.
          case: (altP (bdS1 c f =P 0)) => [->|hf]; first by rewrite !mul0r.
          have [okf df] := hfacet f hf.
          have hmuf : mu1 f = cc (msp f) by rewrite /mu1 df d0.
          have hne : mu1 f != 0.
            rewrite hmuf; apply/eqP => e.
            move: (congr1 (fun g : chainL => g (msp f)) e).
            by rewrite ccE eqxx ffunE => /eqP; rewrite oner_eq0.
          by rewrite hmuf ccE (hzero f hf hne) eqxx mulr1.
        by apply: (bdS_aug okc); rewrite dc.
      have d1 : (1 <= Ldim s')%N by rewrite hd.
      have [iv hiv] := Ldim_valid d1.
      have hh : z s' *: Lbd1 s' = 0 :> chainL.
        rewrite -Lbd_cc -LbdZ -hz; exact: hbdz.
      have hh1 := congr1 (fun g : chainL => g (Lfacet s' iv.1 iv.2)) hh.
      move: hh1; rewrite /= scale_ffunE (@Lbd1_coef t p R s' iv hiv) ffunE => hh2.
      have hh3 : z s' * (-1) ^+ (Lsign s' iv) * (-1) ^+ (Lsign s' iv) = 0 :> R.
        by rewrite hh2 mul0r.
      by move: hh3; rewrite -mulrA sign_sqr mulr1.
    by rewrite hz hgam scale0r.
  rewrite hmu1 hz0 alphaOf0 scale0r; split; first by rewrite eqxx.
  by rewrite /Lbd lin0.
have hd1 : Ldim s' = d.+1 by rewrite hdim dc.
have hsupp : forall sig, z sig != 0 ->
    exists iv, Lvalid s' iv /\ sig = Lfacet s' iv.1 iv.2.
  move=> sig hsig; have [f [hf1 hf2 hf3 hf4 hf5]] := hzsupp sig hsig.
  have hstep : Ldim s' = (Ldim (msp f)).+1 by rewrite hd1 hf4.
  have [iv [hiv he]] := Lsub_facet hf5 (msp_ne f) hstep.
  by exists iv; split => //; rewrite hf3.
have hzrep := facet_decomp hsupp.
have hker : forall iv jw, Lvalid s' iv -> Lvalid s' jw ->
    (-1) ^+ (Lsign s' iv) * z (Lfacet s' iv.1 iv.2)
    = (-1) ^+ (Lsign s' jw) * z (Lfacet s' jw.1 jw.2).
  case: (posnP d) => [d0|dpos]; last first.
    apply: (@Lfacet_ker2 t p R s' (fun iv => z (Lfacet s' iv.1 iv.2))).
      by rewrite hd1.
    by rewrite -hzrep.
  apply: (@Lfacet_ker1 t p R s' (fun iv => z (Lfacet s' iv.1 iv.2))).
    by rewrite hd1 d0.
  rewrite -(@aug_sum _ (fun iv => Lvalid s' iv)
                       (fun iv : 'I_t * 'I_p => Lfacet s' iv.1 iv.2)
                       (fun iv => z (Lfacet s' iv.1 iv.2))).
  rewrite -hzrep.
  have hzc : z = \sum_(f : cellS) bdS1 c f *: cc (msp f).
    rewrite /z /mu; apply: lin_eq_supp => f hf.
    by have [_ df] := hfacet f hf; rewrite /mu1 df d0.
  rewrite hzc (@aug_sum cellS xpredT msp (fun f => bdS1 c f)).
  by apply: (bdS_aug okc); rewrite dc.
have d1 : (1 <= Ldim s')%N by rewrite hd1.
have [iv0 hiv0] := Ldim_valid d1.
have halpha : alphaOf s' z = (-1) ^+ (Lsign s' iv0) * z (Lfacet s' iv0.1 iv0.2).
  rewrite /alphaOf; case: pickP => [iv hiv|hno];
    last by move: (hno iv0); rewrite hiv0.
  exact: hker.
have hza : z = alphaOf s' z *: Lbd1 s'.
  rewrite halpha [LHS]hzrep Lbd1_valid scaler_sumr; apply: eq_bigr => iv hiv.
  rewrite scalerA; congr (_ *: _).
  by rewrite (hker iv0 iv hiv0 hiv) mulrAC sign_sqr mul1r.
split; first by move=> _; exact: hdim.
by rewrite hmu1 LbdZ Lbd_cc -hza.
Qed.

(** ** deliverables *)

Lemma mu_dim c : okS c -> mu1 c != 0 -> Ldim (msp c) = dimS c.
Proof. by move=> okc; have [h _] := @muP (dimS c) c okc (erefl (dimS c)); exact: h. Qed.

Lemma mu1_bd c : okS c -> Lbd (mu1 c) = mu (bdS1 c).
Proof. by move=> okc; have [_ h] := @muP (dimS c) c okc (erefl (dimS c)). Qed.

Lemma mu_bd (x : chainS) : (forall c, x c != 0 -> okS c) -> Lbd (mu x) = mu (bdS x).
Proof.
move=> hx; rewrite /mu /Lbd lin_comp.
have -> : lin (fun c : cellS => lin Lbd1 (mu1 c)) x
        = lin (fun c => lin mu1 (bdS1 c)) x.
  by apply: lin_eq_supp => c hc;
     have e := mu1_bd (hx c hc); move: e; rewrite /Lbd /mu.
by rewrite lin_comp.
Qed.

(** ** ℤ_p-equivariance *)

Section Equivariant.
Hypothesis p_gt0 : (0 < p)%N.
Variable nuS : cellS -> cellS.
Hypothesis nuS_ok  : forall c, okS c -> okS (nuS c).
Hypothesis nuS_dim : forall c, dimS (nuS c) = dimS c.
Hypothesis nuS_msp : forall c, okS c -> msp (nuS c) = Lsh p_gt0 (msp c).
Hypothesis nuS_bd  : forall c, okS c ->
  bdS1 (nuS c) = lin (fun f => cc (nuS f)) (bdS1 c).

Lemma chain_multiple_eq (sig : Lcell t p) (a b : R) :
  (1 <= Ldim sig)%N -> Lbd (a *: cc sig) = Lbd (b *: cc sig) -> a = b.
Proof.
move=> d1 e; have [iv hiv] := Ldim_valid d1.
move: e; rewrite !LbdZ !Lbd_cc => e.
have e1 := congr1 (fun g : chainL => g (Lfacet sig iv.1 iv.2)) e.
move: e1; rewrite /= !scale_ffunE (@Lbd1_coef t p R sig iv hiv) => e2.
have h0 : (a - b) * (-1) ^+ (Lsign sig iv) = 0 by rewrite mulrBl e2 subrr.
have h1 : (a - b) * (-1) ^+ (Lsign sig iv) * (-1) ^+ (Lsign sig iv) = 0 :> R
  by rewrite h0 mul0r.
by move: h1; rewrite -mulrA sign_sqr mulr1 => /eqP; rewrite subr_eq0 => /eqP.
Qed.

Lemma mu1_nu : forall d c, okS c -> dimS c = d -> mu1 (nuS c) = Lnu p_gt0 (mu1 c).
Proof.
elim=> [|d IH] c okc dc.
  have dn : dimS (nuS c) = 0%N by rewrite nuS_dim dc.
  rewrite /mu1 dn dc /= Lnu_cc /Lnu1 (nuS_msp okc).
  have -> : esgn p_gt0 (msp c) = 0%N.
    by apply: esgn_dim0; apply/eqP; rewrite -leqn0 -dc; exact: msp_dim.
  by rewrite expr0 scale1r.
have dn : dimS (nuS c) = d.+1 by rewrite nuS_dim dc.
have okn := nuS_ok okc.
set sig := Lsh p_gt0 (msp c).
have hmspn : msp (nuS c) = sig by rewrite (nuS_msp okc).
have [a ha] := mu1_shape (nuS c).
have [b0 hb0] := mu1_shape c.
have hb : Lnu p_gt0 (mu1 c) = (b0 * (-1) ^+ (esgn p_gt0 (msp c))) *: cc sig.
  by rewrite hb0 LnuZ Lnu_cc /Lnu1 scalerA.
have hfacet : forall f, bdS1 c f != 0 -> okS f /\ dimS f = d.
  move=> f hf; split; first exact: (ok_facet okc hf).
  by rewrite (bdS_dim okc hf) dc.
have hmid : mu (bdS1 (nuS c)) = Lnu p_gt0 (mu (bdS1 c)).
  rewrite (nuS_bd okc) /mu lin_comp.
  have -> : lin (fun f => lin mu1 (cc (nuS f))) (bdS1 c)
          = lin (fun f => lin (Lnu1 p_gt0) (mu1 f)) (bdS1 c).
    apply: lin_eq_supp => f hf; rewrite lin_cc.
    by have [okf df] := hfacet f hf; rewrite (IH f okf df) /Lnu.
  by rewrite /Lnu lin_comp.
have ha' : mu1 (nuS c) = a *: cc sig by rewrite ha hmspn.
have hbd : Lbd (a *: cc sig)
         = Lbd ((b0 * (-1) ^+ (esgn p_gt0 (msp c))) *: cc sig).
  by rewrite -hb -ha' (mu1_bd okn) hmid -(mu1_bd okc) -Lbd_Lnu.
case: (posnP (Ldim sig)) => [d0|dpos]; last first.
  by rewrite ha' hb (chain_multiple_eq dpos hbd).
have hdmsp : Ldim (msp c) = 0%N by rewrite -(Ldim_Lsh p_gt0 (msp c)).
have hz1 : mu1 c = 0.
  apply/eqP; apply: contraT => hne.
  by move: (mu_dim okc hne); rewrite dc hdmsp.
have hz2 : mu1 (nuS c) = 0.
  apply/eqP; apply: contraT => hne.
  by move: (mu_dim okn hne); rewrite dn hmspn d0.
by rewrite hz1 hz2 /Lnu lin0.
Qed.

Lemma mu_nu1 c : okS c -> mu1 (nuS c) = Lnu p_gt0 (mu1 c).
Proof. by move=> okc; exact: (@mu1_nu (dimS c) c okc (erefl (dimS c))). Qed.

Lemma mu_equiv (x : chainS) : (forall c, x c != 0 -> okS c) ->
  mu (lin (fun c => cc (nuS c)) x) = Lnu p_gt0 (mu x).
Proof.
move=> hx; rewrite /mu lin_comp.
have -> : lin (fun c => lin mu1 (cc (nuS c))) x
        = lin (fun c => lin (Lnu1 p_gt0) (mu1 c)) x.
  by apply: lin_eq_supp => c hc; rewrite lin_cc (mu_nu1 (hx c hc)) /Lnu.
by rewrite /Lnu lin_comp.
Qed.

End Equivariant.

End Induced.
