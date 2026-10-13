(** * ClassicalLemmas.eta — the equivariant chain map C(∂L) → C(EℤZ_p)

    Stage D, part 2.  [∂L] is [L] minus its unique top simplotope; the ℤ_p
    action on its cells is free (here [p] must be prime), so [C(∂L)] is a free
    ℤ[ℤ_p]-module and an equivariant chain map into the CONTRACTIBLE bar complex
    can be built by induction on the dimension: on one representative of each
    orbit put [η_#σ := D (η_# ∂σ)], and propagate along the orbit.

    Note that the ℤ_p action on [C(L)] carries signs ([Lnu1 s = (-1)^{esgn s} ⋅
    (Lsh s)]), so "propagating along the orbit" multiplies by the partial sums of
    [esgn]; this is consistent at the wrap-around exactly because
    [Σ_{i<p} esgn (Lsh^i r)] is even ([Esg_p_even] below), which is also what
    makes [Lnu] an action of ℤ_p at all. *)

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

        Claude Opus 5       271k tokens   (09-15 13:00 -> 09-15 14:48 UTC)
        TOTAL               271k tokens   of which 111k were output

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

      Object (ii) of the proof of [M14, Theorem 3.3]: the equivariant chain map
      eta_# defined on the boundary of L.  Here p must be PRIME.

      See bar.v for the one deliberate departure from [M14]: the target is the
      bar resolution of Z_p instead of the join Z_p^{*(t(p-1)+1)}, so that
      [M14, Sect. 2.6] -- Lemmas 2.5, 2.6, 2.7 and Proposition 2.8, the
      barycentric subdivision operator sd_# -- is NOT formalised and is not
      needed.  [M14, Lemma 2.9] is not needed either.

      - [M14], item (ii), "dL is L minus its unique face of maximal dimension"
                                    -> topL, okL, okL_facet, okL_Ldim
      - [M14, Sect. 3.3], "nu induces a free action", transported to dL; this
        is where primality of p enters (a nonempty proper subset of Z_p cannot
        be invariant under a nontrivial power of the shift)
                                    -> shp_invariant_full, Lshk, Lshk_free
      - [M14], item (ii), "by taking in each orbit of Delta(F(dL)) a face
        sigma of dL (recall that Z_p acts on F(dL))"
                                    -> repL, jofL, repL_shk, jofL_shL
      - the sign cocycle along an orbit, forced by the fact that the action of
        Z_p on the chains of L is not orientation preserving (see
        simplotope.v)
                                    -> Esg, Esg_p_even
      - [M14], item (ii), "finally define eta_# = g_# o sd_#"
                                    -> REPLACED by eta1/eta, defined by
                                       induction on the dimension using the
                                       contraction DB of bar.v
      - the three properties of eta_# that the proof of Theorem 3.3 actually
        uses: that it is a chain map, that it is equivariant, and the remark
        "eta_# applied on a vertex of L provides a vertex in the first copy of
        Z_p"
                                    -> eta_chainmap, eta_equivariant,
                                       eta_vertex *)

From mathcomp Require Import all_boot all_algebra.
From ClassicalLemmas Require Import necklace.chains necklace.simplotope necklace.bar.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Set SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.

(** ** the cyclic shift of ℤ_p as a permutation *)

Section ShpOrbit.
Variable p : nat.
Hypothesis p_gt0 : (0 < p)%N.

Local Notation f := (shp p_gt0).

Lemma iter_shp_inj k : injective (iter k f).
Proof.
elim: k => [|k IH] //= x y e; apply: IH.
by move: e; rewrite !iterS => /shp_inj.
Qed.

Lemma iter_shp_idx (a : 'I_p) i j :
  (i < p)%N -> (j < p)%N -> iter i f a = iter j f a -> i = j.
Proof.
wlog hle : i j / (j <= i)%N.
  move=> hw hi hj e; case: (leqP j i) => h; first exact: (hw i j).
  by apply/esym; apply: (hw j i) => //; apply: ltnW.
move=> hi hj e; apply/eqP; rewrite eqn_leq hle andbT -subn_eq0.
have he : (val a + i = val a + j %[mod p])%N by rewrite -!val_shp_iter e.
move: he => /eqP; rewrite eqn_mod_dvd ?leq_add2l // subnDl => hd.
rewrite eqn0Ngt; apply/negP => h0.
by move: hd; rewrite gtnNdvd // (leq_ltn_trans (leq_subr j i)).
Qed.

Lemma iter_shp_mod k (a : 'I_p) : iter (k %% p) f a = iter k f a.
Proof.
by apply/val_inj; rewrite !val_shp_iter modnDmr.
Qed.

Lemma iter_shp_surj (a b : 'I_p) : exists2 k, (k < p)%N & iter k f a = b.
Proof.
exists ((val b + p - val a) %% p)%N; first by rewrite ltn_pmod.
apply/val_inj; rewrite val_shp_iter modnDmr.
rewrite addnBA; last by rewrite (leq_trans (ltnW (ltn_ord a))) // leq_addl.
rewrite addnC addnK.
by rewrite modnDr modn_small // ltn_ord.
Qed.

End ShpOrbit.

(** ** freeness of the ℤ_p action on proper subsets (p prime) *)

Section ShpPrime.
Variable p : nat.
Hypothesis p_gt0 : (0 < p)%N.
Hypothesis p_prime : prime p.

Local Notation f := (shp p_gt0).

Lemma iter_shp_mul_surj k (a b : 'I_p) : (0 < k)%N -> (k < p)%N ->
  exists m, iter (k * m) f a = b.
Proof.
move=> hk0 hkp.
pose g (m : 'I_p) : 'I_p := iter (k * val m) f a.
have key : forall m m' : 'I_p, (val m' <= val m)%N -> g m = g m' -> m = m'.
  move=> m m' hle e; apply/val_inj; apply/eqP.
  rewrite eqn_leq hle andbT -subn_eq0.
  have he : (k * val m = k * val m' %[mod p])%N.
    apply: (@iter_shp_idx p p_gt0 a); rewrite ?ltn_pmod // !iter_shp_mod.
    exact: e.
  move: he => /eqP; rewrite eqn_mod_dvd ?leq_mul2l ?hle ?orbT // -mulnBr.
  rewrite Euclid_dvdM // gtnNdvd //= => hd.
  rewrite eqn0Ngt; apply/negP => h0.
  by move: hd; rewrite gtnNdvd // (leq_ltn_trans (leq_subr _ _)).
have ginj : injective g.
  move=> m m' e; case: (leqP (val m') (val m)) => h; first exact: key.
  by apply/esym; apply: key => //; apply: ltnW.
have [h hgh hhg] := inj_card_bij ginj (leqnn #|'I_p|).
by exists (val (h b)); rewrite -/(g (h b)) hhg.
Qed.

Lemma shp_invariant_full k (A : {set 'I_p}) :
  (0 < k)%N -> (k < p)%N -> A != set0 ->
  [set iter k f x | x in A] = A -> A = setT.
Proof.
move=> hk0 hkp /set0Pn[a aA] hinv.
have hstep : forall x, x \in A -> iter k f x \in A.
  by move=> x xA; rewrite -hinv; apply/imsetP; exists x.
have hall : forall m, iter (k * m) f a \in A.
  elim=> [|m IH]; first by rewrite muln0.
  by rewrite mulnS iterD; apply: hstep.
apply/eqP; rewrite eqEsubset subsetT /=.
apply/subsetP => b _.
by have [m <-] := iter_shp_mul_surj a b hk0 hkp; exact: hall.
Qed.

End ShpPrime.

(** ** the ℤ_p action on the cells of ∂L, and orbit representatives *)

Section LOrbit.
Variables (t p : nat).
Hypothesis p_gt0 : (0 < p)%N.
Hypothesis p_prime : prime p.

Local Notation Lc := (Lcell t p).
Local Notation shL := (Lsh p_gt0).

Definition Lshk (k : nat) (s : Lc) : Lc := iter k shL s.

Lemma LshkS k s : Lshk k.+1 s = shL (Lshk k s).
Proof. by []. Qed.

Lemma Lshk_add k k' s : Lshk (k + k') s = Lshk k (Lshk k' s).
Proof. exact: iterD. Qed.

Lemma Lshk_val k s i : (Lshk k s) i = [set iter k (shp p_gt0) x | x in s i].
Proof.
elim: k => [|k IH]; first by rewrite /= imset_id.
rewrite LshkS /Lsh ffunE IH -imset_comp.
by apply: eq_imset => x.
Qed.

Lemma Lshk_p s : Lshk p s = s.
Proof.
apply/ffunP => i; rewrite Lshk_val -[RHS]imset_id.
by apply: eq_imset => x; exact: shp_iter_p.
Qed.

Lemma Lshk_mul_p q s : Lshk (p * q) s = s.
Proof.
elim: q => [|q IH]; first by rewrite muln0.
by rewrite mulnS Lshk_add IH Lshk_p.
Qed.

Lemma Lshk_mod k s : Lshk ((k %% p)%N) s = Lshk k s.
Proof. by rewrite {2}(divn_eq k p) Lshk_add mulnC Lshk_mul_p. Qed.

Definition topL : Lc := [ffun _ => setT].
Definition okL (s : Lc) : bool := [forall i, s i != set0] && (s != topL).

Lemma card_Lshk k s i : #|(Lshk k s) i| = #|s i|.
Proof. by rewrite Lshk_val card_imset //; exact: iter_shp_inj. Qed.

Lemma Lshk_setT k s i : ((Lshk k s) i == setT) = (s i == setT).
Proof.
by rewrite !eqEcard !subsetT /= !cardsT !card_ord card_Lshk.
Qed.

Lemma Lshk_set0 k s i : ((Lshk k s) i == set0) = (s i == set0).
Proof. by rewrite -!cards_eq0 card_Lshk. Qed.

Lemma okL_shk k s : okL (Lshk k s) = okL s.
Proof.
rewrite /okL; congr (_ && _).
  by apply: eq_forallb => i; rewrite Lshk_set0.
congr (~~ _); apply/eqP/eqP => e; apply/ffunP => i.
  by rewrite /topL ffunE; apply/eqP; rewrite -(Lshk_setT k) e /topL ffunE eqxx.
by rewrite /topL ffunE; apply/eqP; rewrite (Lshk_setT k) e /topL ffunE eqxx.
Qed.

Lemma Lshk_free s k : okL s -> (0 < k)%N -> (k < p)%N -> Lshk k s != s.
Proof.
move=> /andP[hne htop] hk0 hkp; apply/eqP => e.
have [i hi] : exists i, s i != setT.
  apply/existsP; apply: contraR htop => /existsPn h.
  by apply/eqP; apply/ffunP => i; rewrite /topL ffunE; apply/eqP; move: (h i); rewrite negbK.
move: hi => /eqP; apply.
apply: (@shp_invariant_full p p_gt0 p_prime k) => //.
  by move/forallP: hne => /(_ i).
by rewrite -Lshk_val e.
Qed.

Lemma Lshk_idx s j j' : okL s -> (j < p)%N -> (j' < p)%N ->
  Lshk j s = Lshk j' s -> j = j'.
Proof.
wlog hle : j j' / (j' <= j)%N.
  move=> hw hs hj hj' e; case: (leqP j' j) => h; first exact: (hw j j').
  by apply/esym; apply: (hw j' j) => //; apply: ltnW.
move=> hs hj hj' e; apply/eqP; rewrite eqn_leq hle andbT -subn_eq0.
apply/eqP; apply: contraTeq isT => h0.
have hlt : (j - j' < p)%N by rewrite (leq_ltn_trans (leq_subr _ _)).
have hok : okL (Lshk j' s) by rewrite okL_shk.
have h1 : (0 < j - j')%N by rewrite lt0n.
have := Lshk_free hok h1 hlt.
by rewrite -Lshk_add subnK // e eqxx.
Qed.

(** orbit representative: the element of smallest [enum_rank] in the orbit *)

Definition kmin (s : Lc) : 'I_p :=
  [arg min_(k < (Ordinal p_gt0 : 'I_p)) (val (enum_rank (Lshk (val k) s)))].

Definition repL (s : Lc) : Lc := Lshk (val (kmin s)) s.

Lemma repL_orb s : exists2 k, (k < p)%N & repL s = Lshk k s.
Proof. by exists (val (kmin s)); rewrite ?ltn_ord. Qed.

Lemma repL_min s k :
  (val (enum_rank (repL s)) <= val (enum_rank (Lshk k s)))%N.
Proof.
rewrite /repL /kmin; case: arg_minnP => //= k0 _ hmin.
by rewrite -(Lshk_mod k); exact: (hmin (Ordinal (ltn_pmod k p_gt0))).
Qed.

Lemma repL_shk k s : repL (Lshk k s) = repL s.
Proof.
apply: enum_rank_inj; apply/val_inj; apply/eqP; rewrite eqn_leq; apply/andP; split.
  have [k1 _ e1] := repL_orb s.
  rewrite e1.
  have hle : (k %% p <= p)%N by rewrite ltnW // ltn_pmod.
  have hnat : ((k1 + (p - k %% p) + k) %% p = k1 %% p)%N.
    rewrite -addnA -modnDmr.
    have -> : ((p - k %% p + k) %% p = 0)%N by rewrite -modnDmr subnK ?modnn.
    by rewrite addn0.
  have key : Lshk (k1 + (p - k %% p) + k) s = Lshk k1 s.
    by rewrite -Lshk_mod hnat Lshk_mod.
  by rewrite -key Lshk_add; exact: repL_min.
have [k2 _ ->] := repL_orb (Lshk k s).
rewrite -Lshk_add; exact: repL_min.
Qed.

Lemma okL_repL s : okL (repL s) = okL s.
Proof. by rewrite /repL okL_shk. Qed.

Definition jofL (s : Lc) : nat := ((p - val (kmin s)) %% p)%N.

Lemma jofL_lt s : (jofL s < p)%N.
Proof. by rewrite ltn_pmod. Qed.

Lemma Lshk_jofL s : Lshk (jofL s) (repL s) = s.
Proof.
rewrite /jofL /repL -Lshk_add -Lshk_mod modnDml subnK ?modnn //.
by rewrite ltnW // ltn_ord.
Qed.

Lemma jofL_uniq s j : okL s -> (j < p)%N -> Lshk j (repL s) = s -> j = jofL s.
Proof.
move=> hs hj e; apply: (@Lshk_idx (repL s)) => //; first by rewrite okL_repL.
  exact: jofL_lt.
by rewrite e Lshk_jofL.
Qed.

Lemma jofL_shL s : okL s -> jofL (Lsh p_gt0 s) = ((jofL s).+1 %% p)%N.
Proof.
move=> hs; apply/esym; apply: jofL_uniq; rewrite ?ltn_pmod //.
  by rewrite -[Lsh p_gt0 s]/(Lshk 1 s) okL_shk.
rewrite -[Lsh p_gt0 s]/(Lshk 1 s) (repL_shk 1 s) Lshk_mod.
by rewrite -[(jofL s).+1]/(1 + jofL s)%N Lshk_add Lshk_jofL.
Qed.

(** ** the sign cocycle along an orbit *)

Definition Esg (j : nat) (r : Lc) : nat := \sum_(i < j) esgn p_gt0 (Lshk i r).

Lemma EsgS j r : Esg j.+1 r = (Esg j r + esgn p_gt0 (Lshk j r))%N.
Proof. by rewrite /Esg big_ord_recr. Qed.

Lemma Esg0 r : Esg 0 r = 0%N.
Proof. by rewrite /Esg big_ord0. Qed.

Lemma count_shp_hit (a : 'I_p) :
  (\sum_(i < p) (iter (val i) (shp p_gt0) a == taup p_gt0))%N = 1%N.
Proof.
have [k hk hke] := iter_shp_surj p_gt0 a (taup p_gt0).
rewrite (bigD1 (Ordinal hk)) //= hke eqxx big1 //= => i hi.
apply/eqP; rewrite eqb0; apply/negP => /eqP e.
move/eqP: hi; apply; apply/val_inj => /=.
apply: (@iter_shp_idx p p_gt0 a) => //.
by rewrite e hke.
Qed.

Lemma eA_orbit_even (A : {set 'I_p}) :
  (2 %| \sum_(i < p) eA p_gt0 [set iter (val i) (shp p_gt0) x | x in A])%N.
Proof.
have hcard : forall i : nat, #|[set iter i (shp p_gt0) x | x in A]| = #|A|.
  by move=> i; rewrite card_imset //; exact: iter_shp_inj.
have hterm : forall i : 'I_p,
    eA p_gt0 [set iter (val i) (shp p_gt0) x | x in A]
    = ((taup p_gt0 \in [set iter (val i) (shp p_gt0) x | x in A]) * (#|A| - 1))%N.
  by move=> i; rewrite /eA hcard; case: ifP => _; rewrite ?mul1n ?mul0n.
rewrite (eq_bigr _ (fun i _ => hterm i)) -big_distrl /=.
have hind : forall i : 'I_p,
    ((taup p_gt0 \in [set iter (val i) (shp p_gt0) x | x in A]) : nat)
    = (\sum_(a : 'I_p) ((a \in A) && (iter (val i) (shp p_gt0) a == taup p_gt0)))%N.
  move=> i; case: (boolP (taup p_gt0 \in [set iter (val i) (shp p_gt0) x | x in A])) => h.
    move: h => /imsetP[a0 a0A e0].
    rewrite (bigD1 a0) //= a0A -e0 eqxx /= big1 //= => a ha.
    case ha2 : (a \in A) => //=.
    apply/eqP; rewrite eqb0; apply/negP => /eqP e.
    by move/eqP: ha; apply; apply: (@iter_shp_inj p p_gt0 (val i)); rewrite e e0.
  rewrite big1 // => a _.
  case ha2 : (a \in A) => //=.
  apply/eqP; rewrite eqb0; apply/negP => /eqP e.
  by move/negP: h; apply; apply/imsetP; exists a.
rewrite (eq_bigr _ (fun i _ => hind i)) exchange_big /=.
have hrow : forall a : 'I_p,
    (\sum_(i < p) ((a \in A) && (iter (val i) (shp p_gt0) a == taup p_gt0)))%N
    = ((a \in A) : nat).
  move=> a; rewrite (eq_bigr (fun i : 'I_p =>
      ((a \in A) * (iter (val i) (shp p_gt0) a == taup p_gt0))%N));
    last by move=> i _; rewrite mulnb.
  by rewrite -big_distrr /= count_shp_hit muln1.
rewrite (eq_bigr _ (fun a _ => hrow a)).
have -> : (\sum_(a : 'I_p) ((a \in A) : nat))%N = #|A|.
  rewrite -sum1_card big_mkcond /= [RHS]big_mkcond /=.
  by apply: eq_bigr => a _; case: (a \in A).
case E : #|A| => [|n] //.
by rewrite dvdn2 subn1 /= oddM andNb.
Qed.

Lemma Esg_p_even r : odd (Esg p r) = false.
Proof.
apply/negbTE; rewrite -dvdn2 /Esg.
rewrite (eq_bigr (fun i : 'I_p => \sum_(a : 'I_t) eA p_gt0 ((Lshk (val i) r) a)));
  last by move=> i _; rewrite /esgn.
rewrite exchange_big /=; apply: dvdn_sum => a _.
rewrite (eq_bigr (fun i : 'I_p => eA p_gt0 [set iter (val i) (shp p_gt0) x | x in r a]));
  last by move=> i _; rewrite Lshk_val.
exact: eA_orbit_even.
Qed.

(** ** the construction *)

Section EtaRing.
Hypothesis t_gt0 : (0 < t)%N.
Variable R : comNzRingType.

Definition MM := (t * p.-1).+1.
Lemma MM_gt0 : (0 < MM)%N. Proof. by []. Qed.

Local Notation cB := (cellB p MM).
Local Notation chB := {ffun cB -> R^o}.
Local Notation chL := {ffun Lc -> R^o}.
Local Notation pad := (@padd p MM).
Local Notation nuBp := (@nuB p MM p_gt0 R).
Local Notation DBp := (@DB p MM p_gt0 R).
Local Notation bdBp := (@bdB p MM R).

(** *** dimensions *)

Lemma Ldim_max (s : Lc) : (Ldim s <= t * p.-1)%N.
Proof.
have -> : (t * p.-1)%N = (\sum_(i : 'I_t) p.-1)%N by rewrite sum_nat_const card_ord.
apply: leq_sum => i _; rewrite -subn1 leq_sub2r // -[X in (_ <= X)%N](card_ord p).
exact: max_card.
Qed.

Lemma Ldim_topL : Ldim topL = (t * p.-1)%N.
Proof.
have -> : (t * p.-1)%N = (\sum_(i : 'I_t) p.-1)%N by rewrite sum_nat_const card_ord.
by apply: eq_bigr => i _; rewrite /topL ffunE cardsT card_ord subn1.
Qed.

Lemma okL_Ldim (s : Lc) : okL s -> (Ldim s < t * p.-1)%N.
Proof.
move=> /andP[hne htop]; rewrite ltn_neqAle Ldim_max andbT.
apply/eqP => e; move/eqP: htop; apply; apply/ffunP => i; rewrite /topL ffunE.
have hle : forall j : 'I_t, (#|s j| - 1 <= p.-1)%N.
  by move=> j; rewrite -subn1 leq_sub2r // -[X in (_ <= X)%N](card_ord p) max_card.
have hsum : (\sum_(j : 'I_t) (#|s j| - 1) = \sum_(j : 'I_t) p.-1)%N.
  by rewrite sum_nat_const card_ord -e.
have heq := @sum_leq_eq _ xpredT (fun j => (#|s j| - 1)%N) (fun _ => p.-1)
              (fun j _ => hle j) hsum i isT.
have h1 : (1 <= #|s i|)%N by rewrite card_gt0; move/forallP: hne => /(_ i).
apply/eqP; rewrite eqEcard subsetT /= cardsT card_ord.
by rewrite -(subnK h1) heq -subn1 subnK.
Qed.

Lemma Ldim_Lshk k s : Ldim (Lshk k s) = Ldim s.
Proof. by elim: k => [|k IH] //; rewrite LshkS Ldim_Lsh IH. Qed.

Lemma okL_facet s iv : okL s -> Lvalid s iv -> okL (Lfacet s iv.1 iv.2).
Proof.
case: iv => i v hs hval; move: (hval) => /andP[h2 hv] /=.
apply/andP; split.
  apply/forallP => j; rewrite LfacetE; case: (eqVneq j i) => [->|_]; last first.
    by move/andP: hs => [/forallP /(_ j)].
  by rewrite -card_gt0 card_Lfacet // -ltnS prednK // (leq_trans _ h2).
apply/eqP => e.
have hlt : (Ldim (Lfacet s i v) < t * p.-1)%N.
  rewrite (Ldim_Lfacet hval) /=.
  by rewrite (leq_ltn_trans (leq_pred _)) // okL_Ldim.
by move: hlt; rewrite e Ldim_topL ltnn.
Qed.

(** *** vertices *)

Definition i0 : 'I_t := Ordinal t_gt0.
Definition theta (s : Lc) : 'I_p := odflt (Ordinal p_gt0) [pick x | x \in s i0].

Lemma thetaE (s : Lc) (v : 'I_p) : s i0 = [set v] -> theta s = v.
Proof.
move=> e; rewrite /theta e; case: pickP => [x|hno]; first by rewrite inE => /eqP.
by move: (hno v); rewrite inE eqxx.
Qed.

Lemma Ldim0_single s : okL s -> Ldim s = 0%N -> exists v, s i0 = [set v].
Proof.
move=> /andP[hne _] h0; apply/cards1P.
have hle : (#|s i0| - 1 <= Ldim s)%N by rewrite /Ldim (bigD1 i0) //= leq_addr.
have h1 : (1 <= #|s i0|)%N by rewrite card_gt0; move/forallP: hne => /(_ i0).
rewrite eqn_leq h1 andbT.
by move: hle; rewrite h0 leqn0 subn_eq0.
Qed.

Lemma theta_Lsh s : okL s -> Ldim s = 0%N ->
  theta (Lsh p_gt0 s) = shp p_gt0 (theta s).
Proof.
move=> hs h0; have [v hv] := Ldim0_single hs h0.
by rewrite (thetaE hv) (thetaE (v := shp p_gt0 v)) // /Lsh ffunE hv imset_set1.
Qed.

(** *** the induced map, by recursion on the dimension *)

Definition Wstep (g : Lc -> chB) (r : Lc) : chB := DBp (lin g (Lbd1 r)).

Fixpoint ef (d : nat) (s : Lc) : chB :=
  if d is d'.+1
  then (-1) ^+ (Esg (jofL s) (repL s)) *: iter (jofL s) nuBp (Wstep (ef d') (repL s))
  else cc (pad [:: theta s]).

Definition eta1 (s : Lc) : chB := ef (Ldim s) s.
Definition eta : chL -> chB := lin eta1.

(** *** support and dimension of the values *)

Definition okB (k : nat) (x : chB) : Prop :=
  forall c, x c != 0 -> pad (sqB c) = c /\ size (sqB c) = k.

Lemma okB_scale a k x : okB k x -> okB k (a *: x).
Proof.
move=> h c hc; apply: h; apply: contraNN hc => /eqP e.
by rewrite scale_ffunE e mulr0.
Qed.

Lemma okB_sum (I : finType) (P : pred I) (F : I -> chB) k :
  (forall i, P i -> okB k (F i)) -> okB k (\sum_(i | P i) F i).
Proof. by move=> h c /supp_bigsum[i hi hc]; exact: (h i hi c hc). Qed.

Lemma okB_cc u : (size u <= MM)%N -> okB (size u) (cc (pad u)).
Proof.
move=> hu c; rewrite ccE; case: (eqVneq c (pad u)) => [->|_]; last first.
  by rewrite mulr0n eqxx.
by move=> _; rewrite sq_padd.
Qed.

Lemma okB_lin_supp k k' (f : cB -> chB) (x : chB) :
  okB k x -> (forall c, size (sqB c) = k -> okB k' (f c)) -> okB k' (lin f x).
Proof.
move=> hx hf; rewrite /lin; apply: okB_sum => c _.
case: (altP (x c =P 0)) => [->|hc]; first by rewrite scale0r => y; rewrite ffunE eqxx.
by apply: okB_scale; apply: hf; move: (hx c hc) => [].
Qed.

Lemma okB_nu k x : okB k x -> okB k (nuBp x).
Proof.
move=> hx; apply: (okB_lin_supp hx) => c hc.
have hsz : size [seq shp p_gt0 y | y <- sqB c] = k by rewrite size_map hc.
rewrite /nuB1 -hsz.
apply: okB_cc; rewrite hsz -hc.
exact: size_sqB.
Qed.

Lemma okB_iter_nu j k x : okB k x -> okB k (iter j nuBp x).
Proof. by elim: j => [|j IH] //= hx; apply: okB_nu; exact: IH. Qed.

Lemma okB_DB k x : (k < MM)%N -> okB k x -> okB k.+1 (DBp x).
Proof.
move=> hk hx; apply: (okB_lin_supp hx) => c hc.
have hsz : size (v0 p_gt0 :: sqB c) = k.+1 by rewrite /= hc.
rewrite /DB1 -hsz.
by apply: okB_cc; rewrite hsz.
Qed.

Lemma okB_linL k (g : Lc -> chB) (y : chL) :
  (forall c, okB k (g c)) -> okB k (lin g y).
Proof.
move=> hg; rewrite /lin; apply: okB_sum => c _.
case: (altP (y c =P 0)) => [->|hc]; first by rewrite scale0r => z; rewrite ffunE eqxx.
by apply: okB_scale.
Qed.

Lemma ef_okB d s : (d <= t * p.-1)%N -> okB d.+1 (ef d s).
Proof.
elim: d s => [|d IH] s hd.
  by rewrite /= -[1%N]/(size [:: theta s]); apply: okB_cc.
apply: okB_scale; apply: okB_iter_nu; rewrite /Wstep.
apply: okB_DB; first by rewrite ltnS.
by apply: okB_linL => c; apply: IH; apply: ltnW.
Qed.

(** *** the support of a boundary *)

Lemma Lbd1_supp (s : Lc) (c : Lc) :
  (Lbd1 s : chL) c != 0 -> exists2 iv, Lvalid s iv & c = Lfacet s iv.1 iv.2.
Proof.
rewrite Lbd1_valid => /supp_bigsum[iv hiv hc]; exists iv => //.
move: hc; rewrite scale_ffunE ccE.
by case: (eqVneq c (Lfacet s iv.1 iv.2)) => // _; rewrite mulr0 eqxx.
Qed.

Lemma okL_Lbd1 s c : okL s -> (Lbd1 s : chL) c != 0 -> okL c.
Proof. by move=> hs /Lbd1_supp[iv hiv ->]; exact: okL_facet. Qed.

Lemma Ldim_Lbd1 s c : (Lbd1 s : chL) c != 0 -> Ldim c = (Ldim s).-1.
Proof. by move=> /Lbd1_supp[iv hiv ->]; exact: Ldim_Lfacet. Qed.

(** *** equivariance *)

Lemma ef_sh d s : okL s -> (d <= t * p.-1)%N -> (d = 0%N -> Ldim s = 0%N) ->
  ef d (Lsh p_gt0 s) = (-1) ^+ (esgn p_gt0 s) *: nuBp (ef d s).
Proof.
case: d => [|d] hs hdM hd0.
  have h0 : Ldim s = 0%N by apply: hd0.
  rewrite /= (esgn_dim0 p_gt0 h0) expr0 scale1r nuB_cc /nuB1 sq_padd //.
  by rewrite (theta_Lsh hs h0).
rewrite /= -[Lsh p_gt0 s]/(Lshk 1 s) (repL_shk 1 s) -[Lshk 1 s]/(Lsh p_gt0 s).
rewrite (jofL_shL hs).
set r := repL s; set W := Wstep (ef d) r.
case: (ltnP (jofL s).+1 p) => hj.
  rewrite (modn_small hj) EsgS Lshk_jofL exprD.
  by rewrite iterS nuBZ scalerA [(-1) ^+ esgn p_gt0 s * _]mulrC.
have hje : ((jofL s).+1 = p)%N by apply/eqP; rewrite eqn_leq hj andbT (jofL_lt s).
have hd1 : (d <= t * p.-1)%N by rewrite (leq_trans (leqnSn d)).
have hMM : (d.+1 < MM)%N by rewrite ltnS.
have hW : forall c, W c != 0 -> pad (sqB c) = c.
  move=> c hc.
  have hlin : okB d.+1 (lin (ef d) (Lbd1 r)).
    by apply: okB_linL => c'; exact: ef_okB c' hd1.
  have hok := okB_DB hMM hlin.
  by move: (hok c hc) => [].
rewrite hje modnn Esg0 expr0 scale1r /= nuBZ scalerA -exprD.
have hE : (esgn p_gt0 s + Esg (jofL s) r = Esg p r)%N.
  by rewrite -{2}hje EsgS Lshk_jofL addnC.
rewrite hE -iterS hje (nuB_iter_p p_gt0 hW).
by rewrite -signr_odd Esg_p_even expr0 scale1r.
Qed.

Lemma eta1_sh s : okL s ->
  eta1 (Lsh p_gt0 s) = (-1) ^+ (esgn p_gt0 s) *: nuBp (eta1 s).
Proof.
move=> hs; rewrite /eta1 Ldim_Lsh; apply: ef_sh => //.
by rewrite ltnW // okL_Ldim.
Qed.

Lemma eta_Lnu1 s : okL s -> eta (Lnu1 p_gt0 s) = nuBp (eta1 s).
Proof.
move=> hs; rewrite /Lnu1 /eta linZ lin_cc (eta1_sh hs) scalerA.
by rewrite sign_sqr scale1r.
Qed.

Lemma eta_Lnu (y : chL) : (forall c, y c != 0 -> okL c) ->
  eta (Lnu p_gt0 y) = nuBp (eta y).
Proof.
move=> hy; rewrite {1}/eta /Lnu lin_comp.
have -> : lin (fun c => lin eta1 (Lnu1 p_gt0 c)) y
        = lin (fun c => lin (@nuB1 p MM p_gt0 R) (eta1 c)) y.
  by apply: lin_eq_supp => c hc; move: (eta_Lnu1 (hy c hc)); rewrite /eta /nuB.
by rewrite /nuB /eta lin_comp.
Qed.

Lemma Lbd1_Lsh s :
  Lbd1 (Lsh p_gt0 s) = (-1) ^+ (esgn p_gt0 s) *: Lnu p_gt0 (Lbd1 s) :> chL.
Proof.
have h := Lbd_Lnu p_gt0 (cc s : chL).
move: h; rewrite /Lnu lin_cc /Lnu1 LbdZ Lbd_cc Lbd_cc => h.
by rewrite -h scalerA sign_sqr scale1r.
Qed.

Lemma eta_bd_shift s : okL s ->
  bdBp (eta1 s) = eta (Lbd1 s) ->
  bdBp (eta1 (Lsh p_gt0 s)) = eta (Lbd1 (Lsh p_gt0 s)).
Proof.
move=> hs h; rewrite (eta1_sh hs) bdBZ bdB_nuB h Lbd1_Lsh /eta linZ.
congr (_ *: _).
rewrite -/(eta (Lnu p_gt0 (Lbd1 s))) -/(eta (Lbd1 s)); apply/esym.
by apply: eta_Lnu => c hc; exact: (okL_Lbd1 hs hc).
Qed.

Lemma eta_bd_shk k s : okL s ->
  bdBp (eta1 s) = eta (Lbd1 s) ->
  bdBp (eta1 (Lshk k s)) = eta (Lbd1 (Lshk k s)).
Proof.
move=> hs h; elim: k => [|k IH] //.
by rewrite LshkS; apply: eta_bd_shift => //; rewrite okL_shk.
Qed.

(** *** η_# is a chain map *)

Lemma eta_bd_dim : forall d s, okL s -> Ldim s = d ->
  bdBp (eta1 s) = eta (Lbd1 s).
Proof.
elim=> [|d IH] s hs hd.
  have h0 : Lbd1 s = 0 :> chL.
    rewrite Lbd1_valid big1 // => iv hiv.
    by move: (Lvalid_dim hiv); rewrite hd.
  by rewrite h0 /eta lin0 /eta1 hd /= bdB_cc bdB1_padd.
set r := repL s.
have hr : okL r by rewrite /r okL_repL.
have hdr : Ldim r = d.+1 by rewrite /r /repL Ldim_Lshk.
have hrr : repL r = r.
  by rewrite /r -[repL s]/(Lshk (val (kmin s)) s) repL_shk.
have hj0 : jofL r = 0%N.
  apply: (@Lshk_idx r) => //; first exact: jofL_lt.
  by have := Lshk_jofL r; rewrite hrr => ->.
have hdM : (d.+1 < t * p.-1)%N by rewrite -hdr okL_Ldim.
have hd1 : (d <= t * p.-1)%N by rewrite (leq_trans (leqnSn d)) // ltnW.
have hMM : (d.+1 < MM)%N by rewrite ltnS ltnW.
have hetar : eta1 r = DBp (lin (ef d) (Lbd1 r)).
  by rewrite /eta1 hdr /= hj0 hrr Esg0 expr0 scale1r.
have hz : lin (ef d) (Lbd1 r) = eta (Lbd1 r).
  by apply: lin_eq_supp => c hc; rewrite /eta1 (Ldim_Lbd1 hc) hdr.
have hokz : okB d.+1 (eta (Lbd1 r)).
  by rewrite -hz; apply: okB_linL => c; exact: ef_okB c hd1.
have hbz : bdBp (eta (Lbd1 r)) = 0.
  rewrite /eta /bdB lin_comp.
  have -> : lin (fun c => lin (@bdB1 p MM R) (eta1 c)) (Lbd1 r)
          = lin (fun c => lin eta1 (@Lbd1 t p R c)) (Lbd1 r).
    apply: lin_eq_supp => c hc.
    have hcok := okL_Lbd1 hr hc.
    have hcd : Ldim c = d by rewrite (Ldim_Lbd1 hc) hdr.
    by move: (IH c hcok hcd); rewrite /bdB /eta.
  rewrite -[LHS](lin_comp (@Lbd1 t p R) eta1 (Lbd1 r)).
  have -> : lin (@Lbd1 t p R) (Lbd1 r) = 0 :> chL.
    by rewrite -[Lbd1 r]Lbd_cc -/(Lbd (Lbd (cc r))) Lbd_bd.
  by rewrite lin0.
have haug : d.+1 = 1%N -> augB (eta (Lbd1 r)) = 0.
  move=> hd11; have hd0 : d = 0%N by case: hd11.
  have -> : eta (Lbd1 r) = lin (fun c => cc (pad [:: theta c])) (Lbd1 r).
    by apply: lin_eq_supp => c hc; rewrite /eta1 (Ldim_Lbd1 hc) hdr hd0.
  rewrite /augB aug_lin.
  rewrite (eq_bigr (fun c => (Lbd1 r : chL) c)); last first.
    by move=> c _; rewrite sum_cc_aug mulr1.
  by apply: Lbd1_aug; rewrite hdr hd0.
have hrepbd : bdBp (eta1 r) = eta (Lbd1 r).
  rewrite hetar hz.
  exact: (bdB_DB_hom p_gt0 MM_gt0 hokz (ltn0Sn d) hMM hbz haug).
have := eta_bd_shk (jofL s) hr hrepbd.
by rewrite /r Lshk_jofL.
Qed.

Lemma eta_bd (s : Lc) : okL s -> bdBp (eta1 s) = eta (Lbd1 s).
Proof. by move=> hs; have := eta_bd_dim hs (erefl (Ldim s)). Qed.

Lemma eta_chainmap (x : chL) : (forall c, x c != 0 -> okL c) ->
  bdBp (eta x) = eta (lin Lbd1 x).
Proof.
move=> hx; rewrite {1}/eta /bdB lin_comp.
have -> : lin (fun c => lin (@bdB1 p MM R) (eta1 c)) x
        = lin (fun c => lin eta1 (@Lbd1 t p R c)) x.
  by apply: lin_eq_supp => c hc; move: (eta_bd (hx c hc)); rewrite /bdB /eta.
by rewrite /eta lin_comp.
Qed.

Lemma eta_equivariant (x : chL) : (forall c, x c != 0 -> okL c) ->
  eta (Lnu p_gt0 x) = nuBp (eta x).
Proof. exact: eta_Lnu. Qed.

Lemma eta_vertex (s : Lc) : okL s -> Ldim s = 0%N ->
  eta1 s = cc (pad [:: theta s]).
Proof. by move=> hs h0; rewrite /eta1 h0. Qed.

Lemma eta1_okB (s : Lc) : okB (Ldim s).+1 (eta1 s).
Proof. by rewrite /eta1; apply: ef_okB; exact: Ldim_max. Qed.

Lemma eta_cc (s : Lc) : eta (cc s) = eta1 s.
Proof. exact: lin_cc. Qed.

Lemma etaD x y : eta (x + y) = eta x + eta y. Proof. exact: linD. Qed.
Lemma etaZ a x : eta (a *: x) = a *: eta x. Proof. exact: linZ. Qed.
Lemma eta0 : eta 0 = 0. Proof. exact: lin0. Qed.

Lemma eta_sum (I : finType) (F : I -> chL) :
  eta (\sum_(i : I) F i) = \sum_(i : I) eta (F i).
Proof. by rewrite /eta lin_sum_cond. Qed.

End EtaRing.

End LOrbit.
