(** * ClassicalLemmas.bar — the homogeneous bar complex of ℤ_p

    Stage D of the necklace formalisation.  Meunier (2014) uses the join
    [ℤ_p^{*N}] as the target of [η_#]; we use instead the homogeneous bar
    resolution [EℤZ_p], which is the complex the cochains of
    Hanke–Sanyal–Schultz–Ziegler actually live on (our [salt.v] already states
    them on value sequences, with [delete i] as the face maps).  The gain is
    decisive: [EℤZ_p] is CONTRACTIBLE, with the one-line contraction "prepend
    the neutral element", so the equivariant chain map [C(∂L) → C(EℤZ_p)] can
    be built by a plain induction on the dimension, with no barycentric
    subdivision and no connectivity argument (Meunier's §2.6, Lemmas 2.5–2.7
    and Prop. 2.8 are not needed).

    A [d]-cell is a sequence of [d+1] residues.  To get a [finType] we bound
    the length by [M] and store the sequence in an [M]-tuple padded with
    [None]; [padd] and [sqB] are the two directions of that encoding, and all
    the combinatorics happens on plain sequences. *)

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

        Claude Opus 5       263k tokens   (09-15 12:10 -> 09-15 13:00 UTC)
        TOTAL               263k tokens   of which 104k were output

      Method: the figures are estimated from the logs of the Claude Code
      session of 14-15 September 2026.  For every assistant message they count
      input + cache-creation + output tokens, i.e. the tokens processed anew,
      excluding the cached conversation that is re-read at each turn (772M
      over the project); a message is charged to the file its tool calls were
      acting on.  Three whole-session context rebuilds (compaction or resume),
      1.61M tokens in all, are charged to no file.  Project totals: 4.10M
      tokens of per-file work, 1.61M of context rebuilds, 5.70M overall.

    SOURCES.

      [HSSZ] B. Hanke, R. Sanyal, C. Schultz, G. M. Ziegler, "Combinatorial
             Stokes formulas via minimal resolutions", Journal of Combinatorial
             Theory, Series A 116 (2009) 404-420.  (Reference [9] of [M14].)
             Local copy: classical-lemmas/HankeSSZ-Combinatorial_stokes_formulas-1-s2.0-S0097316508000988-main.pdf

      [M06]  F. Meunier, "A Zq-Fan theorem", technical report, presented at the
             "Topological combinatorics" workshop, Stockholm, December 2006.
             (Reference [11] of [M14].)
             Local copy: classical-lemmas/Meunier2006-zqkyfan.pdf

      [M14]  F. Meunier, "Simplotopal maps and necklace splitting",
             Discrete Mathematics 323 (2014) 14-26.
             Local copy: classical-lemmas/Meunier2014-Simplotopal_Necklace_web.pdf

    WHAT CORRESPONDS TO WHAT.

      The target of the equivariant chain map, and the cochains of item (iii)
      of the proof of [M14, Theorem 3.3] lifted from salt.v to chains.

      DELIBERATE DEPARTURE FROM [M14].  Item (ii) of [M14] sends eta_# into the
      join Z_p^{*(t(p-1)+1)}, which forces the whole of [M14, Sect. 2.6]
      (barycentric subdivision, Lemmas 2.5-2.7, Proposition 2.8) plus a
      connectivity argument, because the join is only (N-2)-connected.  We send
      it instead into the homogeneous bar resolution EZ_p, i.e. the standard
      resolution of [HSSZ, Sect. 3], which is where the cochains of item (iii)
      live in the first place.  It is contractible, so the equivariant chain
      map is obtained by a plain induction on the dimension (see eta.v).
      Nothing downstream changes: the proof of [M14, Theorem 3.3] uses only
      that eta_# is an equivariant chain map and the base case
      "sum_r phi_0(nu^r eta_#(v)) = 1".

      - [HSSZ, Sect. 3], the standard resolution of Z_k (a d-cell is a sequence
        of d+1 residues) and its differential
                                    -> cellB, dels, bdB; bdB_bd is "d o d = 0"
      - the Z_p action on it                 -> nuB, bdB_nuB, nuB_iter_padd
      - the contraction "prepend the neutral element", which replaces
        [M14, Sect. 2.6]
                                    -> DB, bdB_DB_hom
      - [HSSZ, Prop. 3.8] composed with the evaluation u of [HSSZ, Sect. 4]
        (pages 411 and 413), equivalently the e_d of [M06]
                                    -> phi
      - [M06, Appendix, Lemma 2], in the cochain form of [M14], item (iii)
                                    -> phi_bd_even, phi_bd_odd
      - [M14], item (iii), "phi_{0#} is equal to 1 for a unique vertex"
                                    -> phi0_orbit *)

From mathcomp Require Import all_boot all_algebra.
From ClassicalLemmas Require Import necklace.chains necklace.simplotope necklace.salt.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Set SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.

(** ** deleting one entry of a sequence *)

Section Dels.
Variable T : Type.

Definition dels (i : nat) (s : seq T) : seq T := take i s ++ drop i.+1 s.

Lemma dels0 (x : T) s : dels 0 (x :: s) = s.
Proof. by rewrite /dels take0 /= drop0. Qed.

Lemma delsS i (x : T) s : dels i.+1 (x :: s) = x :: dels i s.
Proof. by []. Qed.

Lemma dels_nil i : dels i ([::] : seq T) = [::].
Proof. by rewrite /dels; case: i => [|i] //=; rewrite !take_nil.  Qed.

Lemma size_dels i (s : seq T) : (i < size s)%N -> size (dels i s) = (size s).-1.
Proof.
move=> h; rewrite /dels size_cat size_take h size_drop addnBA //.
by rewrite addnC subnS addnK.
Qed.

Lemma size_dels_leq i (s : seq T) : (size (dels i s) <= size s)%N.
Proof.
elim: s i => [|x s IH] i; first by rewrite dels_nil.
case: i => [|i]; first by rewrite dels0 /= leqW.
by rewrite delsS /= ltnS IH.
Qed.

(** the simplicial identity *)
Lemma dels_dels i j (s : seq T) :
  (i <= j)%N -> dels j (dels i s) = dels i (dels j.+1 s).
Proof.
elim: s i j => [|x s IH] i j hij; first by rewrite !dels_nil.
case: i hij => [|i] hij.
  by rewrite dels0 delsS dels0.
case: j hij => [//|j] hij.
by rewrite !delsS IH.
Qed.

End Dels.

Section Bar.
Variables (p M : nat).
Hypothesis p_gt0 : (0 < p)%N.
Hypothesis M_gt0 : (0 < M)%N.

Definition cellB := (M.-tuple (option 'I_p))%type.

Definition sqB (c : cellB) : seq 'I_p := pmap id (val c).

Definition padd (s : seq 'I_p) : cellB :=
  insubd ([tuple of nseq M None] : M.-tuple (option 'I_p))
         (take M ([seq Some x | x <- s] ++ nseq M None)).

Lemma pmap_id_map (s : seq 'I_p) : pmap id [seq Some x | x <- s] = s.
Proof. by elim: s => //= x s ->. Qed.

Lemma pmap_id_nseq k : pmap id (nseq k (None : option 'I_p)) = [::].
Proof. by elim: k. Qed.

Lemma val_padd s : (size s <= M)%N ->
  val (padd s) = [seq Some x | x <- s] ++ nseq (M - size s) None.
Proof.
move=> h; rewrite /padd val_insubd.
have hsz : size (take M ([seq Some x | x <- s] ++ nseq M None)) = M.
  rewrite size_take size_cat size_map size_nseq.
  by case: ifP => // /negbT; rewrite -leqNgt => h2;
     apply/eqP; rewrite eqn_leq h2 leq_addl.
rewrite hsz eqxx take_cat size_map ltnNge h /= take_nseq //.
by rewrite leq_subr.
Qed.

Lemma sq_padd s : (size s <= M)%N -> sqB (padd s) = s.
Proof.
move=> h; rewrite /sqB val_padd // pmap_cat pmap_id_map pmap_id_nseq cats0.
by [].
Qed.

Lemma size_sqB c : (size (sqB c) <= M)%N.
Proof.
rewrite /sqB size_pmap -[X in (_ <= X)%N](size_tuple c).
exact: count_size.
Qed.


Lemma padd_inj s s' : (size s <= M)%N -> (size s' <= M)%N -> padd s = padd s' -> s = s'.
Proof. by move=> h h' e; rewrite -(sq_padd h) e sq_padd. Qed.

Definition iM (k : nat) : 'I_M := insubd (Ordinal M_gt0) k.

Lemma val_iM k : (k < M)%N -> val (iM k) = k.
Proof. by move=> h; rewrite /iM val_insubd h. Qed.

Definition v0 : 'I_p := Ordinal p_gt0.

Lemma dels_map (T U : Type) (f : T -> U) i (s : seq T) :
  [seq f x | x <- dels i s] = dels i [seq f x | x <- s].
Proof. by rewrite /dels map_cat map_take map_drop. Qed.

(** ** the chain complex *)

Section Ring.
Variable R : comNzRingType.
Local Notation chainB := {ffun cellB -> R^o}.

Definition bterm (s : seq 'I_p) (i : nat) : chainB :=
  (-1) ^+ i *: cc (padd (dels i s)).

Definition bdB1 (c : cellB) : chainB :=
  if (1 < size (sqB c))%N
  then \sum_(i < M | (i < size (sqB c))%N) bterm (sqB c) i else 0.

Definition bdB : chainB -> chainB := lin bdB1.

Lemma bdBD x y : bdB (x + y) = bdB x + bdB y. Proof. exact: linD. Qed.
Lemma bdBZ a x : bdB (a *: x) = a *: bdB x. Proof. exact: linZ. Qed.
Lemma bdB_cc c : bdB (cc c) = bdB1 c. Proof. exact: lin_cc. Qed.
Lemma bdB0 : bdB 0 = 0. Proof. exact: lin0. Qed.

Lemma bdB1_padd s : (size s <= M)%N ->
  bdB1 (padd s) =
  if (1 < size s)%N then \sum_(i < M | (i < size s)%N) bterm s i else 0.
Proof. by move=> h; rewrite /bdB1 sq_padd. Qed.

Lemma bdB_bd1 c : bdB (bdB1 c) = 0.
Proof.
set s := sqB c; have hs : (size s <= M)%N := size_sqB c.
rewrite /bdB1 -/s; case: ifP => hn; last exact: lin0.
rewrite /bdB lin_sum_cond.
have hdel : forall i : 'I_M, (i < size s)%N ->
    lin bdB1 (bterm s i)
    = if (1 < (size s).-1)%N
      then \sum_(j < M | (j < (size s).-1)%N)
             (-1) ^+ (val i + val j) *: cc (padd (dels j (dels i s)))
      else 0.
  move=> i hi; rewrite /bterm linZ lin_cc bdB1_padd; last first.
    by rewrite (leq_trans (size_dels_leq _ _)).
  rewrite (size_dels hi); case: ifP => hd; last by rewrite scaler0.
  rewrite scaler_sumr; apply: eq_bigr => j _.
  by rewrite /bterm scalerA exprD.
rewrite (eq_bigr _ hdel).
case hd : (1 < (size s).-1)%N; last by rewrite big1.
rewrite pair_big /=.
pose tau (q : 'I_M * 'I_M) : 'I_M * 'I_M :=
  if (val q.2 < val q.1)%N then (q.2, iM (val q.1).-1) else (iM (val q.2).+1, q.1).
have hsp : (0 < size s)%N by apply: leq_trans hn.
have hb1 : forall b : nat, (b < (size s).-1)%N -> (b.+1 < size s)%N.
  by move=> b hb; rewrite -[size s]prednK // ltnS.
have iM_val : forall i : 'I_M, iM (val i) = i.
  by move=> i; apply/val_inj; rewrite val_iM // ltn_ord.
apply: (@sum_invol _ _ _ tau).
- move=> [x y] /andP[hx hy] /=; rewrite /tau /=.
  have hy1M : ((val y).+1 < M)%N by rewrite (leq_trans _ hs) // hb1.
  case: ifP => hxy /=.
    have hxM1 : ((val x).-1 < M)%N by rewrite (leq_ltn_trans (leq_pred _)) // ltn_ord.
    rewrite (val_iM hxM1) (leq_trans hy) ?leq_pred //=.
    by rewrite -subn1 -[X in (_ < X)%N]subn1 ltn_sub2r.
  rewrite (val_iM hy1M) hb1 //=.
  by rewrite (leq_ltn_trans _ hy) // leqNgt hxy.
- move=> [x y] /andP[hx hy] /=; rewrite /tau /=.
  have hy1M : ((val y).+1 < M)%N by rewrite (leq_trans _ hs) // hb1.
  have hxM1 : ((val x).-1 < M)%N by rewrite (leq_ltn_trans (leq_pred _)) // ltn_ord.
  case hxy : (val y < val x)%N => /=.
    have hx0 : (0 < val x)%N by apply: leq_ltn_trans hxy.
    rewrite !val_iM //.
    have -> : ((val x).-1 < val y)%N = false by rewrite ltnNge -ltnS prednK // hxy.
    by rewrite prednK // iM_val.
  rewrite !val_iM //.
  have -> : (val x < (val y).+1)%N = true by rewrite ltnS leqNgt hxy.
  by rewrite iM_val.
- move=> [x y] /andP[hx hy] /=; rewrite /tau /=.
  have hy1M : ((val y).+1 < M)%N by rewrite (leq_trans _ hs) // hb1.
  have hxM1 : ((val x).-1 < M)%N by rewrite (leq_ltn_trans (leq_pred _)) // ltn_ord.
  case hxy : (val y < val x)%N => /=.
    have hx0 : (0 < val x)%N by apply: leq_ltn_trans hxy.
    rewrite !val_iM //.
    have -> : dels (val x).-1 (dels (val y) s) = dels (val y) (dels (val x) s).
      by rewrite (dels_dels s (i := val y) (j := (val x).-1)) ?prednK // -ltnS prednK.
    have -> : (val x + val y = (val y + (val x).-1).+1)%N.
      by rewrite addnC -addnS prednK.
    by rewrite exprS mulN1r scaleNr opprK.
  rewrite !val_iM //.
  have -> : dels (val x) (dels (val y).+1 s) = dels (val y) (dels (val x) s).
    by rewrite (dels_dels s (i := val x) (j := val y)) // leqNgt hxy.
  have -> : ((val y).+1 + val x = (val x + val y).+1)%N by rewrite addSn addnC.
  by rewrite exprS mulN1r scaleNr.
- move=> [x y] /andP[hx hy] /=; rewrite /tau /=.
  have hy1M : ((val y).+1 < M)%N by rewrite (leq_trans _ hs) // hb1.
  case hxy : (val y < val x)%N => /=.
    by apply/eqP => -[e1 e2]; move: hxy; rewrite e1 ltnn.
  apply/eqP => -[e1 e2].
  have e : ((val y).+1 = val y)%N by rewrite -(val_iM hy1M) e1 e2.
  by move: (ltnSn (val y)); rewrite {2}e ltnn.
Qed.

Lemma bdB_bd x : bdB (bdB x) = 0.
Proof.
rewrite {1}/bdB lin_comp /lin big1 // => c _.
by rewrite -/(lin bdB1 (bdB1 c)) -/(bdB (bdB1 c)) bdB_bd1 scaler0.
Qed.

(** ** the cyclic ℤ_p action *)

Definition nuB1 (c : cellB) : chainB := cc (padd [seq shp p_gt0 x | x <- sqB c]).
Definition nuB : chainB -> chainB := lin nuB1.

Lemma nuBD x y : nuB (x + y) = nuB x + nuB y. Proof. exact: linD. Qed.
Lemma nuBZ a x : nuB (a *: x) = a *: nuB x. Proof. exact: linZ. Qed.
Lemma nuB_cc c : nuB (cc c) = nuB1 c. Proof. exact: lin_cc. Qed.
Lemma nuB0 : nuB 0 = 0. Proof. exact: lin0. Qed.

Lemma bdB_nuB1 c : bdB (nuB1 c) = nuB (bdB1 c).
Proof.
set s := sqB c; have hs : (size s <= M)%N := size_sqB c.
have hms : (size [seq shp p_gt0 x | x <- s] <= M)%N by rewrite size_map.
rewrite /nuB1 -/s bdB_cc (bdB1_padd hms) size_map /bdB1 -/s.
case: ifP => hn; last by rewrite nuB0.
rewrite /nuB lin_sum_cond; apply: eq_bigr => i hi.
rewrite /bterm linZ lin_cc /nuB1 sq_padd; last first.
  by rewrite (leq_trans (size_dels_leq _ _)).
by rewrite dels_map.
Qed.

Lemma bdB_nuB x : bdB (nuB x) = nuB (bdB x).
Proof.
apply: (chain_ext (F := fun y => bdB (nuB y)) (G := fun y => nuB (bdB y))).
- by move=> c1 c2; rewrite nuBD bdBD.
- by move=> a c; rewrite nuBZ bdBZ.
- by move=> c1 c2; rewrite bdBD nuBD.
- by move=> a c; rewrite bdBZ nuBZ.
- by move=> c; rewrite nuB_cc bdB_cc bdB_nuB1.
Qed.

(** ** the contraction: prepend the neutral element *)

Definition DB1 (c : cellB) : chainB := cc (padd (v0 :: sqB c)).
Definition DB : chainB -> chainB := lin DB1.

Lemma DBD x y : DB (x + y) = DB x + DB y. Proof. exact: linD. Qed.
Lemma DBZ a x : DB (a *: x) = a *: DB x. Proof. exact: linZ. Qed.
Lemma DB_cc c : DB (cc c) = DB1 c. Proof. exact: lin_cc. Qed.
Lemma DB0 : DB 0 = 0. Proof. exact: lin0. Qed.

Definition cterm (s : seq 'I_p) (i : nat) : chainB :=
  (-1) ^+ i *: cc (padd (v0 :: dels i s)).

Lemma bdB_DB1 s : (0 < size s)%N -> (size s < M)%N ->
  bdB (DB1 (padd s)) = cc (padd s) - \sum_(i < M | (i < size s)%N) cterm s i.
Proof.
move=> h0 hM; have hs : (size s <= M)%N by exact: ltnW.
have hvs : (size (v0 :: s) <= M)%N by rewrite /= hM.
rewrite /DB1 sq_padd // bdB_cc (bdB1_padd hvs) /=.
rewrite ltnS h0 -(big_ord_widen _ (fun i => bterm (v0 :: s) i) hM).
rewrite big_ord_recl /bterm dels0 expr0 scale1r; congr (_ + _).
rewrite -(big_ord_widen _ (fun i => cterm s i) hs) -sumrN.
apply: eq_bigr => i _; rewrite /bterm /cterm /bump /=.
by rewrite delsS exprS mulN1r scaleNr.
Qed.

Lemma DB_bd1 s : (size s <= M)%N ->
  DB (bdB1 (padd s))
  = if (1 < size s)%N then \sum_(i < M | (i < size s)%N) cterm s i else 0.
Proof.
move=> hs; rewrite bdB1_padd //; case: ifP => hn; last by rewrite DB0.
rewrite /DB lin_sum_cond; apply: eq_bigr => i hi.
rewrite /bterm linZ lin_cc /DB1 sq_padd //.
by rewrite (leq_trans (size_dels_leq _ _)).
Qed.

Lemma bdB_DB_padd s : (0 < size s)%N -> (size s < M)%N ->
  bdB (DB1 (padd s)) + DB (bdB1 (padd s))
  = cc (padd s) - (if size s == 1%N then cc (padd [:: v0]) else 0).
Proof.
move=> h0 hM; rewrite (bdB_DB1 h0 hM) (DB_bd1 (ltnW hM)).
case hn : (1 < size s)%N.
  have -> : (size s == 1%N) = false by rewrite eqn_leq leqNgt hn.
  by rewrite subr0 addrNK.
have hs1 : size s = 1%N.
  by apply/eqP; rewrite eqn_leq h0 andbT leqNgt hn.
rewrite hs1 eqxx addr0; congr (_ - _).
rewrite -(big_ord_widen _ (fun i => cterm s i) M_gt0) big_ord_recl big_ord0 addr0.
rewrite /cterm expr0 scale1r.
have hd : dels 0 s = [::] by move: hs1 h0 hM hn; case: s => [//|x [|y s']].
by rewrite hd.
Qed.

(** ** the action has order [p] *)

Lemma val_shp_iter r (x : 'I_p) : val (iter r (shp p_gt0) x) = ((val x + r) %% p)%N.
Proof.
elim: r => [|r IH] /=; first by rewrite addn0 modn_small.
rewrite /shp /= IH.
by rewrite -addn1 modnDml addn1 addnS.
Qed.

Lemma shp_iter_p (x : 'I_p) : iter p (shp p_gt0) x = x.
Proof. by apply/val_inj; rewrite val_shp_iter modnDr modn_small // ltn_ord. Qed.

Lemma nuB_iter_padd r s : (size s <= M)%N ->
  iter r nuB (cc (padd s)) = cc (padd [seq iter r (shp p_gt0) x | x <- s]).
Proof.
move=> h; elim: r => [|r IH]; first by rewrite /= map_id.
rewrite iterS IH nuB_cc /nuB1 sq_padd ?size_map // -map_comp.
by congr (cc (padd _)); apply: eq_map => x /=.
Qed.

Lemma iter_nuB_lin r (x : chainB) :
  iter r nuB x = lin (fun c => iter r nuB (cc c)) x.
Proof.
apply: (chain_ext (F := fun y => iter r nuB y)
                  (G := fun y => lin (fun c => iter r nuB (cc c)) y)) => //.
- by elim: r => [|r IH] c1 c2 //=; rewrite IH nuBD.
- by elim: r => [|r IH] a c //=; rewrite IH nuBZ.
- by move=> c1 c2; exact: linD.
- by move=> a c; exact: linZ.
- by move=> c; rewrite lin_cc.
Qed.

Lemma nuB_iter_p (x : chainB) :
  (forall c, x c != 0 -> padd (sqB c) = c) -> iter p nuB x = x.
Proof.
move=> hx; rewrite iter_nuB_lin -[RHS]lin_cc_id.
apply: lin_eq_supp => c hc; rewrite -(hx c hc) nuB_iter_padd ?size_sqB //.
by rewrite (eq_map shp_iter_p) map_id.
Qed.

(** ** the contraction kills homogeneous cycles *)

Definition augB (x : chainB) : R := \sum_(c : cellB) x c.

Lemma bdB_DB_hom (x : chainB) (k : nat) :
  (forall c, x c != 0 -> padd (sqB c) = c /\ size (sqB c) = k) ->
  (0 < k)%N -> (k < M)%N -> bdB x = 0 -> (k = 1%N -> augB x = 0) ->
  bdB (DB x) = x.
Proof.
move=> hx h0 hM hbd haug.
rewrite {1}/DB /bdB lin_comp.
have hstep : lin (fun c => lin bdB1 (DB1 c)) x
           = lin (fun c => cc c - (if k == 1%N then cc (padd [:: v0]) else 0)
                           - lin DB1 (bdB1 c)) x.
  apply: lin_eq_supp => c hc; have [hn hk] := hx c hc.
  have h1 : (0 < size (sqB c))%N by rewrite hk.
  have h2 : (size (sqB c) < M)%N by rewrite hk.
  move: (bdB_DB_padd h1 h2); rewrite hn hk => e.
  by rewrite -/(bdB _) -/(DB _) -e addrK.
rewrite hstep.
rewrite (_ : lin _ x = lin cc x
             - lin (fun _ : cellB => if k == 1%N then cc (padd [:: v0]) else 0) x
             - lin (fun c => lin DB1 (bdB1 c)) x); last first.
  rewrite /lin -!sumrB; apply: eq_bigr => c _.
  by rewrite !scalerBr.
rewrite lin_cc_id -lin_comp.
have -> : lin bdB1 x = 0 by exact: hbd.
rewrite lin0 subr0.
case hk1 : (k == 1%N); last first.
  by rewrite /lin big1 ?subr0 // => c _; rewrite scaler0.
rewrite (_ : lin _ x = augB x *: cc (padd [:: v0])); last first.
  by rewrite /lin /augB scaler_suml.
by rewrite haug ?scale0r ?subr0 //; apply/eqP.
Qed.

(** ** the HSSZ co-hemisphere cochains, on the bar complex

    [salt.v] states them on value sequences with [delete i] as face maps, which
    is exactly the bar complex; here they become genuine cochains and the two
    Stokes relations become chain-level identities. *)

Definition natseq (c : cellB) : seq nat := [seq val x | x <- sqB c].

Definition phi (d : nat) (x : chainB) : R :=
  \sum_(c : cellB) x c * (Phi p d (natseq c))%:R.

Lemma size_natseq c : size (natseq c) = size (sqB c).
Proof. exact: size_map. Qed.

Lemma all_natseq c : all (fun y => (y < p)%N) (natseq c).
Proof. by apply/allP => y /mapP[x _ ->]; rewrite ltn_ord. Qed.

Lemma natseq_padd s : (size s <= M)%N -> natseq (padd s) = [seq val x | x <- s].
Proof. by move=> h; rewrite /natseq sq_padd. Qed.

Lemma phiD d x y : phi d (x + y) = phi d x + phi d y.
Proof.
by rewrite /phi -big_split; apply: eq_bigr => c _; rewrite ffunE mulrDl.
Qed.

Lemma phiZ d a x : phi d (a *: x) = a * phi d x.
Proof.
rewrite /phi mulr_sumr; apply: eq_bigr => c _.
by rewrite scale_ffunE mulrA.
Qed.

Lemma phi0 d : phi d 0 = 0.
Proof. by rewrite -(scale0r 0) phiZ mul0r. Qed.

Lemma phi_cc d c : phi d (cc c) = (Phi p d (natseq c))%:R.
Proof.
rewrite /phi (bigD1 c) //= ccE eqxx mul1r big1 ?addr0 // => c' hc'.
by rewrite ccE (negbTE hc') mul0r.
Qed.

Lemma phi_sum d (I : finType) (P : pred I) (F : I -> chainB) :
  phi d (\sum_(i | P i) F i) = \sum_(i | P i) phi d (F i).
Proof.
rewrite /phi exchange_big /=; apply: eq_bigr => c _.
by rewrite sum_ffunE mulr_suml.
Qed.

Lemma phi_lin d (f : cellB -> chainB) (x : chainB) :
  phi d (lin f x) = \sum_(c : cellB) x c * phi d (f c).
Proof.
rewrite /lin phi_sum; apply: eq_bigr => c _.
by rewrite phiZ.
Qed.

Lemma delsE i (u : seq nat) : dels i u = delete i u.
Proof. by []. Qed.

Lemma val_shp_sh (x : 'I_p) : val (shp p_gt0 x) = sh p (val x).
Proof.
rewrite /shp /sh /=; case: ifP => h; first by rewrite modn_small.
have e : ((val x).+1 = p)%N by apply/eqP; rewrite eqn_leq ltn_ord /= leqNgt h.
by rewrite e modnn.
Qed.

Lemma natseq_nuB1 c : natseq (padd [seq shp p_gt0 x | x <- sqB c])
                    = [seq sh p y | y <- natseq c].
Proof.
rewrite natseq_padd ?size_map ?size_sqB // /natseq -!map_comp.
by apply: eq_map => x /=; exact: val_shp_sh.
Qed.

Lemma phi_nuB1 d c : phi d (nuB1 c) = (Phi p d [seq sh p y | y <- natseq c])%:R.
Proof. by rewrite /nuB1 phi_cc natseq_nuB1. Qed.

Lemma phi_iter_nuB d r c :
  phi d (iter r nuB (cc c)) = (Phi p d (shiftv p r (natseq c)))%:R.
Proof.
elim: r c => [|r IH] c; first by rewrite /= phi_cc.
rewrite iterSr nuB_cc /nuB1 IH natseq_nuB1.
by rewrite /shiftv iterSr.
Qed.

Lemma phi_bdB1 d c :
  phi d (bdB1 c) =
  if (1 < size (sqB c))%N
  then \sum_(i < M | (i < size (sqB c))%N)
         (-1) ^+ (val i) * (Phi p d (delete i (natseq c)))%:R
  else 0.
Proof.
rewrite /bdB1; case: ifP => hn; last exact: phi0.
rewrite phi_sum; apply: eq_bigr => i hi.
rewrite /bterm phiZ phi_cc natseq_padd; last first.
  by rewrite (leq_trans (size_dels_leq _ _)) // size_sqB.
by rewrite /natseq dels_map.
Qed.

(** the two Stokes relations, on a basis cell *)

Lemma phi_bd_even_cc l c : ((2 * l).+2 <= M)%N ->
  phi (2 * l) (bdB1 c) = phi (2 * l).+1 (nuB1 c) - phi (2 * l).+1 (cc c).
Proof.
move=> hM; set n := size (sqB c).
have hns : size (natseq c) = n by rewrite size_natseq.
case hn2 : (n == (2 * l).+2).
  have hn : (1 < n)%N by rewrite (eqP hn2).
  rewrite phi_bdB1 -/n hn phi_nuB1 phi_cc.
  rewrite -(big_ord_widen _
     (fun i => (-1) ^+ i * (Phi p (2 * l) (delete i (natseq c)))%:R));
    last by rewrite -/n (eqP hn2).
  have hnn : n = (2 * l).+2 by apply/eqP.
  rewrite hnn.
  have hns2 : size (natseq c) = (2 * l).+2 by rewrite hns hnn.
  by rewrite (Phi_bd_even p_gt0 R hns2 (all_natseq c)).
have hne : size (natseq c) != (2 * l).+2 by rewrite hns hn2.
have hne2 : size [seq sh p y | y <- natseq c] != (2 * l).+2 by rewrite size_map.
rewrite phi_nuB1 phi_cc (Phi_size p hne) (Phi_size p hne2) subrr.
rewrite phi_bdB1 -/n; case: ifP => hn; last by [].
rewrite big1 // => i hi.
have hd : size (delete i (natseq c)) != (2 * l).+1.
  rewrite -delsE size_dels ?hns //; apply/eqP => e.
  by move: hn2; rewrite -(prednK (_ : (0 < n)%N)) ?e ?eqxx // (leq_trans _ hn).
by rewrite (Phi_size p hd) mulr0.
Qed.

Lemma phi_bd_odd_cc l c : ((2 * l).+3 <= M)%N ->
  phi (2 * l).+1 (bdB1 c) = \sum_(r < p) phi (2 * l).+2 (iter r nuB (cc c)).
Proof.
move=> hM; set n := size (sqB c).
have hns : size (natseq c) = n by rewrite size_natseq.
rewrite (eq_bigr (fun r : 'I_p => (Phi p (2 * l).+2 (shiftv p r (natseq c)))%:R));
  last by move=> r _; rewrite phi_iter_nuB.
case hn3 : (n == (2 * l).+3).
  have hn : (1 < n)%N by rewrite (eqP hn3).
  rewrite phi_bdB1 -/n hn.
  rewrite -(big_ord_widen _
     (fun i => (-1) ^+ i * (Phi p (2 * l).+1 (delete i (natseq c)))%:R));
    last by rewrite -/n (eqP hn3).
  have hnn : n = (2 * l).+3 by apply/eqP.
  rewrite hnn.
  have hns3 : size (natseq c) = (2 * l).+3 by rewrite hns hnn.
  by rewrite (Phi_bd_odd p_gt0 R hns3 (all_natseq c)).
rewrite big1; last first.
  move=> r _.
  have hsz : size (shiftv p r (natseq c)) != (2 * l).+3 by rewrite size_shiftv hns hn3.
  by rewrite (Phi_size p hsz).
rewrite phi_bdB1 -/n; case: ifP => hn; last by [].
rewrite big1 // => i hi.
have hd : size (delete i (natseq c)) != (2 * l).+2.
  rewrite -delsE size_dels ?hns //; apply/eqP => e.
  by move: hn3; rewrite -(prednK (_ : (0 < n)%N)) ?e ?eqxx // (leq_trans _ hn).
by rewrite (Phi_size p hd) mulr0.
Qed.

(** the two Stokes relations, on chains *)

Lemma phi_bd_even l x : ((2 * l).+2 <= M)%N ->
  phi (2 * l) (bdB x) = phi (2 * l).+1 (nuB x) - phi (2 * l).+1 x.
Proof.
move=> hM; rewrite -{3}[x]lin_cc_id /bdB /nuB !phi_lin -sumrB.
apply: eq_bigr => c _.
by rewrite -mulrBr (phi_bd_even_cc c hM).
Qed.

Lemma phi_bd_odd l x : ((2 * l).+3 <= M)%N ->
  phi (2 * l).+1 (bdB x) = \sum_(r < p) phi (2 * l).+2 (iter r nuB x).
Proof.
move=> hM; rewrite /bdB phi_lin.
rewrite [RHS](eq_bigr (fun r : 'I_p =>
   \sum_(c : cellB) x c * phi (2 * l).+2 (iter r nuB (cc c)))); last first.
  by move=> r _; rewrite (iter_nuB_lin r x) phi_lin.
rewrite exchange_big /=; apply: eq_bigr => c _.
by rewrite (phi_bd_odd_cc c hM) mulr_sumr.
Qed.

(** the base case *)

Lemma phi0_orbit c : (size (sqB c) = 1)%N ->
  \sum_(r < p) phi 0 (iter r nuB (cc c)) = 1.
Proof.
move=> h1; have : size (natseq c) = 1%N by rewrite size_natseq.
case hc : (natseq c) => [|v [|w u]] // _.
rewrite (eq_bigr (fun r : 'I_p => (Phi p 0 (shiftv p r (natseq c)))%:R));
  last by move=> r _; rewrite phi_iter_nuB.
rewrite hc; apply: (Phi0_shift p_gt0 R).
by have := all_natseq c; rewrite hc /= andbT.
Qed.

End Ring.
End Bar.
