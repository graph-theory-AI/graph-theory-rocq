(** * ClassicalLemmas.salt — strongly alternating patterns (HSSZ, Def. 3.5)

    The combinatorial core of the co-hemisphere cochains of
    Hanke–Sanyal–Schultz–Ziegler, "Combinatorial Stokes formulas via minimal
    resolutions" (JCTA 2009), §3, evaluated at the neutral element of ℤ_p.

    A pattern is a sequence [a = a_1 … a_{2s}] of residues (naturals [< p]);
    it is strongly alternating when [a_{2i+1} + a_{2i+2} >= p] for all [i].
    A bar element [g^{s_0}[g^{a_1}|…|g^{a_r}]] corresponds to the value
    sequence [s_0, s_1, …, s_r] with [a_i = (s_i - s_{i-1}) mod p]; removing
    the vertex [s_i] (a face of the simplex) mergeats [a_i] and [a_{i+1}].

    This file proves the two purely arithmetic identities that Prop. 3.8 of
    HSSZ boils down to once the group ring is evaluated at [e]:
    - [salt_merge_sum]: the alternating sum of [salt] over the mergeatd
      patterns telescopes;
    - [sigma_count]: the counting identity behind [σ_{a+b} = σ_a + g^a σ_b]
      and [σ_{a+b} - σ_{(a+b) mod p} = [a+b >= p] σ]. *)

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

        Claude Fable 5.1    355k tokens   (09-14 21:58 -> 09-14 22:46 UTC)
        Claude Opus 4.8      73k tokens   (09-14 22:48 -> 09-15 04:31 UTC)
        Claude Opus 5       186k tokens   (09-15 11:56 -> 09-15 15:19 UTC)
        TOTAL               615k tokens   of which 296k were output

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

      Stage A of the development: the cochains of item (iii) of the proof of
      [M14, Theorem 3.3], and their two Stokes relations.  [M14] obtains them
      from [HSSZ] ("phi_d = u o f_d where u is defined page 413 and f_d is
      defined page 411") or, alternatively, from the cochains e_d of [M06].
      Here they are built on value sequences (sequences of residues), which is
      what later lets bar.v replace the join by the bar resolution.

      - [M06, Appendix, Lemma 1], "if <e_k, sigma> is nonzero then
        sigma_i /= sigma_{i+1} for all i", and the "strongly alternating label
        patterns" counted by [HSSZ, Theorem 5.4]
                                    -> dmod, diffs, salt, salt3, sigma_count,
                                       salt_merge_sum
      - the face maps of a simplex of the standard resolution ([HSSZ, Sect. 3])
                                    -> delete, mergeat
      - [HSSZ, Prop. 3.8] and the evaluation u of [HSSZ, Sect. 4] (pages 411
        and 413, the pages [M14] points to), equivalently the e_d of [M06]
                                    -> Phi d
      - [M06, Appendix, Lemma 2], "delta e_{2l} = (nu# - nu#^-1) e_{2l+1}" and
        "delta e_{2l+1} = (id + nu + ... + nu^{q-1}) e_{2l+2}", in the dual
        (cochain) form in which [M14] states them in item (iii):
        "phi_{(2l+1)#} o (id - nu) = phi_{(2l)#} o d" and
        "phi_{(2l+2)#} o (sum_r nu^r) = phi_{(2l+1)#} o d"
                                    -> Phi_bd_even, Phi_bd_odd
      - [M14], item (iii), "phi_{0#} is equal to 1 for a unique vertex ... and
        0 elsewhere", used as the base case of the induction
                                    -> Phi0_shift *)

From mathcomp Require Import all_boot all_algebra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.

Section Salt.
Variable p : nat.
Hypothesis p_gt0 : 0 < p.

(** [(y - x) mod p] for residues [x y < p]. *)
Definition dmod (x y : nat) : nat := ((y + p) - x) %% p.

(** Consecutive differences of a value sequence. *)
Fixpoint diffs (s : seq nat) : seq nat :=
  if s is x :: s' then (if s' is y :: _ then dmod x y :: diffs s' else [::])
  else [::].

(** Strongly alternating (pairs [(a_1,a_2), (a_3,a_4), …]; a trailing odd
    element is ignored). *)
Fixpoint salt (a : seq nat) : bool :=
  if a is x :: y :: a' then (p <= x + y) && salt a' else true.

(** Merge positions [i] and [i+1] into their sum mod [p]. *)
Definition mergeat (i : nat) (a : seq nat) : seq nat :=
  take i a ++ ((nth 0 a i + nth 0 a i.+1) %% p) :: drop i.+2 a.

Lemma dmod_lt x y : dmod x y < p.
Proof. exact: ltn_pmod. Qed.

Lemma size_diffs s : size (diffs s) = (size s).-1.
Proof. by elim: s => [|x [|y s] IH] //=; rewrite IH. Qed.

Lemma mergeat_cons2 i x y a : mergeat i.+2 (x :: y :: a) = x :: y :: mergeat i a.
Proof. by []. Qed.

Lemma salt_cons2 x y a : salt (x :: y :: a) = (p <= x + y) && salt a.
Proof. by []. Qed.

(** The three-variable identity (as naturals, booleans coerced). *)
Lemma salt3 x y z :
  x < p -> y < p -> z < p ->
  (p <= (x + y) %% p + z) + (p <= x + y) = (p <= x + (y + z) %% p) + (p <= y + z).
Proof.
move=> xp yp zp.
have xy2 : x + y < p + p by apply: leq_trans (leq_add xp yp); rewrite addSn addnS.
have yz2 : y + z < p + p by apply: leq_trans (leq_add yp zp); rewrite addSn addnS.
have modB m : p <= m -> m < p + p -> m %% p = m - p.
  by move=> hm hm2; rewrite -{1}(subnK hm) modnDr modn_small // ltn_subLR.
have [hxy|hxy] := leqP p (x + y); have [hyz|hyz] := leqP p (y + z).
- by rewrite !modB // addnBAC // addnBA // addnA.
- rewrite modB // (modn_small hyz) addnBAC // addnA.
  have h2 : x + y + z < p + p.
    by rewrite -addnA; apply: leq_trans (leq_add xp hyz); rewrite addSn addnS.
  have -> : (p <= x + y + z - p) = false.
    by rewrite leqNgt ltn_subLR ?h2 // (leq_trans hxy (leq_addr _ _)).
  by rewrite (leq_trans hxy (leq_addr _ _)).
- rewrite (modn_small hxy) modB // addnBA // addnA.
  have h2 : x + y + z < p + p.
    by apply: leq_trans (leq_add hxy zp); rewrite addSn addnS.
  have -> : (p <= x + y + z - p) = false.
    by rewrite leqNgt ltn_subLR ?h2 // -addnA (leq_trans hyz (leq_addl _ _)).
  by rewrite -addnA (leq_trans hyz (leq_addl _ _)).
- by rewrite !modn_small // addnA.
Qed.

(** The telescoping identity: for a pattern of odd length [2s+1],
    [Σ_{i<2s} (-1)^i salt (mergeat i a) = salt (behead a) - salt (take 2s a)]. *)
Lemma salt_merge_sum (R : nzRingType) (s : nat) (a : seq nat) :
  size a = (2 * s).+1 -> all (fun x => x < p) a ->
  (\sum_(i < 2 * s) (-1) ^+ i * (salt (mergeat i a))%:R
  = (salt (behead a))%:R - (salt (take (2 * s) a))%:R :> R)%R.
Proof.
elim: s a => [|s IH] a.
  case: a => [|x [|y a]] //= _ _.
  by rewrite muln0 big_ord0 /= subrr.
case: a => [|x [|y [|z a]]] // sz alla.
  by move: sz; rewrite mulnS !addSn add0n.
case/and3P: alla => xp yp /andP [zp alla].
have sza : size a = 2 * s by move: sz; rewrite /= mulnS !addSn add0n => -[].
rewrite mulnS !addSn add0n; set n := 2 * s in IH *.
have mergeat0 u v (l : seq nat) : mergeat 0 (u :: v :: l) = (u + v) %% p :: l.
  by rewrite /mergeat /= drop0.
have mergeat1 u v w (l : seq nat) :
    mergeat 1 (u :: v :: w :: l) = u :: (v + w) %% p :: l.
  by rewrite /mergeat /= drop0.
have take2 m u v (l : seq nat) : take m.+2 (u :: v :: l) = u :: v :: take m l.
  by [].
rewrite 2!big_ord_recl expr0 expr1 mul1r mulN1r mergeat0 mergeat1 take2.
have -> : behead [:: x, y, z & a] = [:: y, z & a] by [].
rewrite !salt_cons2.
have -> : (\sum_(i < n) (-1) ^+ (lift ord0 (lift ord0 i))
             * (salt (mergeat (lift ord0 (lift ord0 i)) [:: x, y, z & a]))%:R
   = (p <= x + y)%N%:R * (\sum_(i < n) (-1) ^+ i * (salt (mergeat i (z :: a)))%:R)
     :> R)%R.
  rewrite mulr_sumr; apply: eq_bigr => i _.
  rewrite !lift0 mergeat_cons2 salt_cons2 -mulnb natrM !exprS !mulN1r opprK.
  by rewrite !mulrA; congr (_ * _)%R; rewrite mulr_natr mulr_natl.
rewrite IH; first [by rewrite /= sza | by rewrite /= zp | idtac].
rewrite [behead _]/= -!mulnb !natrM mulrBr.
have h3 := salt3 xp yp zp.
have hR : ((p <= (x + y) %% p + z)%:R + (p <= x + y)%:R
           = (p <= x + (y + z) %% p)%:R + (p <= y + z)%:R :> R)%R.
  by rewrite -!natrD h3.
rewrite !addrA; congr (_ - _)%R; rewrite -mulrBl -mulrDl; congr (_ * _)%R.
by rewrite addrAC hR addrAC subrr add0r.
Qed.

(** The counting identity behind the σ-part:
    [[(m - x) mod p < y] + [m < x] = [m < (x + y) mod p] + [x + y >= p]]. *)
Lemma sigma_count m x y :
  m < p -> x < p -> y < p ->
  (dmod x m < y) + (m < x) = (m < (x + y) %% p) + (p <= x + y).
Proof.
move=> mp xp yp.
have xy2 : x + y < p + p by apply: leq_trans (leq_add xp yp); rewrite addSn addnS.
have modB k : p <= k -> k < p + p -> k %% p = k - p.
  by move=> hk hk2; rewrite -{1}(subnK hk) modnDr modn_small // ltn_subLR.
have xmp : x <= m + p := leq_trans (ltnW xp) (leq_addl _ _).
have [hmx|hmx] := ltnP m x; have [hxy|hxy] := leqP p (x + y).
- have dm : dmod x m = m + p - x by rewrite /dmod modn_small // ltn_subLR ?ltn_add2r.
  by rewrite dm modB // ltn_subLR // ltn_subRL [p + m]addnC.
- have dm : dmod x m = m + p - x by rewrite /dmod modn_small // ltn_subLR ?ltn_add2r.
  rewrite dm (modn_small hxy).
  have -> : (m + p - x < y) = false.
    by rewrite ltn_subLR // ltnNge (leq_trans (ltnW hxy) (leq_addl _ _)).
  by rewrite (leq_trans hmx (leq_addr _ _)).
- have dm : dmod x m = m - x.
    by rewrite /dmod -addnBAC // modnDr modn_small // (leq_ltn_trans (leq_subr _ _) mp).
  rewrite dm modB // (ltn_subLR _ hmx).
  have -> : (m < x + y - p) = false.
    by rewrite ltnNge (leq_trans _ hmx) // leq_subLR [p + x]addnC leq_add2l ltnW.
  by rewrite (leq_trans mp hxy).
- have dm : dmod x m = m - x.
    by rewrite /dmod -addnBAC // modnDr modn_small // (leq_ltn_trans (leq_subr _ _) mp).
  by rewrite dm (modn_small hxy) (ltn_subLR _ hmx).
Qed.


(** ** Value sequences, deletion, shifts ***********************************)

(** Explicit form of [dmod] on residues. *)
Lemma dmodE x y : x < p -> y < p -> dmod x y = if x <= y then y - x else y + p - x.
Proof.
move=> xp yp; rewrite /dmod; case: leqP => hxy.
- by rewrite -addnBAC // modnDr modn_small // (leq_ltn_trans (leq_subr _ _) yp).
- rewrite modn_small // ltn_subLR ?ltn_add2r // (leq_trans (ltnW xp)) //.
  exact: leq_addl.
Qed.

Lemma dmod_add x y z :
  x < p -> y < p -> z < p -> (dmod x y + dmod y z) %% p = dmod x z.
Proof.
move=> xp yp zp; rewrite !dmodE //.
have xzp : x <= z + p := leq_trans (ltnW xp) (leq_addl _ _).
have yzp : y <= z + p := leq_trans (ltnW yp) (leq_addl _ _).
have xyp : x <= y + p := leq_trans (ltnW xp) (leq_addl _ _).
case: (leqP x y) => hxy; case: (leqP y z) => hyz.
- by rewrite (leq_trans hxy hyz) addnBAC // subnKC // modn_small // (leq_ltn_trans (leq_subr _ _) zp).
- rewrite addnBAC // subnKC //.
  case: (leqP x z) => hxz.
  + by rewrite -addnBAC // modnDr modn_small // (leq_ltn_trans (leq_subr _ _) zp).
  + by rewrite modn_small // ltn_subLR ?ltn_add2r.
- rewrite addnBAC // addnAC subnKC //.
  case: (leqP x z) => hxz.
  + by rewrite -addnBAC // modnDr modn_small // (leq_ltn_trans (leq_subr _ _) zp).
  + by rewrite modn_small // ltn_subLR ?ltn_add2r.
- have hxz : z < x := ltn_trans hyz hxy.
  rewrite leqNgt hxz /= addnBAC // addnAC subnKC // -addnBAC // modnDr modn_small //.
  by rewrite ltn_subLR ?ltn_add2r.
Qed.

(** The cyclic shift [v ↦ v+1 mod p] on residues, without [%%]. *)
Definition sh (v : nat) : nat := if v.+1 < p then v.+1 else 0.

Lemma sh_lt v : sh v < p.
Proof. by rewrite /sh; case: ifP. Qed.

Lemma dmod_sh x y : x < p -> y < p -> dmod (sh x) (sh y) = dmod x y.
Proof.
move=> xp yp; rewrite /sh; case: ltnP => hx; case: ltnP => hy.
- by rewrite /dmod addSn subSS.
- have ey : y.+1 = p by apply/eqP; rewrite eqn_leq yp hy.
  have xy : x <= y by rewrite -ltnS ey.
  by rewrite /dmod -ey add0n subSS -addnBAC // modnDr.
- have ex : x.+1 = p by apply/eqP; rewrite eqn_leq xp hx.
  rewrite /dmod -ex subn0 modnDr addnS subSn ?leq_addl // addnK.
  by rewrite modn_small ?ex.
- have ex : x.+1 = p by apply/eqP; rewrite eqn_leq xp hx.
  have ey : y.+1 = p by apply/eqP; rewrite eqn_leq yp hy.
  have exy : x = y by apply: succn_inj; rewrite ex ey.
  by rewrite /dmod exy add0n subn0 modnn addnC addnK modnn.
Qed.

Definition shiftv (r : nat) (s : seq nat) : seq nat := iter r (map sh) s.

Lemma diffs_map_sh s : all (fun x => x < p) s -> diffs (map sh s) = diffs s.
Proof.
elim: s => [|x [|y s] IH] //= /andP [xp /andP [yp alls]].
rewrite dmod_sh //; congr (_ :: _); apply: IH.
by rewrite /= yp alls.
Qed.

Lemma all_map_sh s : all (fun x => x < p) s -> all (fun x => x < p) (map sh s).
Proof. by move=> _; apply/allP => v /mapP [w _ ->]; exact: sh_lt. Qed.

Lemma diffs_shiftv r s : all (fun x => x < p) s -> diffs (shiftv r s) = diffs s.
Proof.
elim: r => //= r IH alls; rewrite diffs_map_sh ?IH //.
by elim: r {IH} => //= r IH; apply: all_map_sh.
Qed.

Definition delete (i : nat) (s : seq nat) : seq nat := take i s ++ drop i.+1 s.

Lemma delete0 s : delete 0 s = behead s.
Proof. by case: s => [|x s] //; rewrite /delete /= drop0. Qed.

Lemma deleteS i x s : delete i.+1 (x :: s) = x :: delete i s.
Proof. by []. Qed.

Lemma size_delete i s : i < size s -> size (delete i s) = (size s).-1.
Proof.
move=> hi; have hk : 0 < size s - i by rewrite subn_gt0.
rewrite size_cat size_take size_drop hi subnS -{2}(subnKC (ltnW hi)).
by rewrite -(prednK hk) addnS.
Qed.

Lemma mergeat_cons1 i x a : mergeat i.+1 (x :: a) = x :: mergeat i a.
Proof. by []. Qed.

Lemma diffs_cons2 u v (l : seq nat) :
  diffs (u :: v :: l) = dmod u v :: diffs (v :: l).
Proof. by []. Qed.

Lemma mergeat0 u v (l : seq nat) : mergeat 0 (u :: v :: l) = (u + v) %% p :: l.
Proof. by rewrite /mergeat /= drop0. Qed.

Lemma diffs_delete_mid i s :
  0 < i -> i.+1 < size s -> all (fun x => x < p) s ->
  diffs (delete i s) = mergeat i.-1 (diffs s).
Proof.
elim: i s => // i IH [|x [|y [|z s]]] // _ hi alls.
have /and3P [xp yp alls'] : [&& x < p, y < p & all (fun x => x < p) (z :: s)] := alls.
have /andP [zp alls''] : (z < p) && all (fun x => x < p) s := alls'.
case: i IH hi => [|i] IH hi.
  rewrite deleteS delete0.
  have -> : behead [:: y, z & s] = z :: s by [].
  by rewrite !diffs_cons2 mergeat0 dmod_add.
rewrite !deleteS !diffs_cons2 mergeat_cons1; congr (_ :: _).
rewrite -deleteS IH //.
by rewrite /= yp zp alls''.
Qed.

Lemma diffs_delete_last s n :
  size s = n.+2 -> diffs (delete n.+1 s) = take n (diffs s).
Proof.
elim: n s => [|n IH] [|x [|y s]] // sz.
  have sz' : size s = 0 by move: sz => /= [].
  by rewrite (size0nil sz') deleteS delete0 take0.
have sz' : size s = n.+1 by move: sz => /= [].
rewrite !deleteS diffs_cons2 -deleteS IH; first [by rewrite /= sz' | idtac].
by rewrite diffs_cons2.
Qed.

Lemma head_delete i s : 0 < i -> head 0 (delete i s) = head 0 s.
Proof. by case: i s => // i [|x s] //= _; rewrite deleteS. Qed.

Lemma delete_last s n : size s = n.+1 -> delete n s = take n s.
Proof.
move=> sz; rewrite /delete -{2}(cats0 (take n s)); congr (_ ++ _).
by apply/size0nil; rewrite size_drop sz subnn.
Qed.

Lemma iter_sh r v : v < p -> iter r sh v = (v + r) %% p.
Proof.
move=> vp; elim: r => [|r IH] /=; first by rewrite addn0 modn_small.
rewrite IH /sh addnS.
have e : (v + r).+1 %% p = ((v + r) %% p).+1 %% p by rewrite -addn1 -modnDml addn1.
rewrite e; case: ltnP => h; first by rewrite (modn_small h).
have hp : ((v + r) %% p).+1 = p by apply/eqP; rewrite eqn_leq h ltn_pmod.
by rewrite hp modnn.
Qed.

Lemma size_shiftv r s : size (shiftv r s) = size s.
Proof. by elim: r => //= r IH; rewrite size_map IH. Qed.

Lemma all_shiftv r s :
  all (fun x => x < p) s -> all (fun x => x < p) (shiftv r s).
Proof. by elim: r => //= r IH alls; apply: all_map_sh; apply: IH. Qed.

Lemma shiftv_nil r : shiftv r [::] = [::].
Proof. by elim: r => //= r ->. Qed.

Lemma shiftv_cons r x s : shiftv r (x :: s) = iter r sh x :: shiftv r s.
Proof. by elim: r => //= r ->. Qed.

Lemma head_shiftv r x s : head 0 (shiftv r (x :: s)) = iter r sh x.
Proof. by rewrite shiftv_cons. Qed.

Lemma all_diffs s : all (fun x => x < p) (diffs s).
Proof. by elim: s => [|x [|y s] IH] //=; rewrite dmod_lt. Qed.

Lemma all_behead s : all (fun x => x < p) s -> all (fun x => x < p) (behead s).
Proof. by case: s => //= x s /andP []. Qed.

(** Exactly one cyclic shift of a residue is [0]. *)
Lemma count_shift0 (R : comNzRingType) v :
  v < p -> (\sum_(r < p) ((v + r) %% p == 0)%N%:R = 1 :> R)%R.
Proof.
move=> vp; pose r0 := Ordinal (ltn_pmod (p - v) p_gt0) : 'I_p.
have hr0 : (v + r0) %% p = 0 by rewrite /= modnDmr subnKC ?modnn // ltnW.
rewrite (bigD1 r0) //= hr0 eqxx big1 ?addr0 // => r hr.
suff -> : ((v + r) %% p == 0) = false by [].
apply/negbTE; apply: contra hr => /eqP h.
apply/eqP/val_inj => /=; apply/eqP.
rewrite -(modn_small (ltn_ord r)) -(@modn_small ((p - v) %% p) p (ltn_pmod _ p_gt0)).
by rewrite -(eqn_modDl v) h [in X in _ == X]/= hr0.
Qed.

(** The residue [(s_0 - s_1) mod p] is [dmod s_1 0] shifted by [dmod s_0 0]. *)
Lemma dmod_a1 s0 s1 :
  s0 < p -> s1 < p -> dmod (dmod s0 s1) (dmod s0 0) = dmod s1 0.
Proof.
move=> s0p s1p.
rewrite (dmodE (dmod_lt s0 s1) (dmod_lt s0 0)) (dmodE s0p s1p) (dmodE s0p p_gt0).
rewrite (dmodE s1p p_gt0).
case: (posnP s0) => [-> | s0_gt0]; first by rewrite !leq0n /= !subn0.
rewrite [s0 <= 0]leqNgt s0_gt0 /= add0n.
case: (leqP s0 s1) => h01.
  rewrite (leq_sub2r s0 (ltnW s1p)) (subnBA _ h01) (subnK (ltnW s0p)).
  by rewrite [s1 <= 0]leqNgt (leq_trans s0_gt0 h01).
case: (posnP s1) => [-> | s1_gt0]; first by rewrite add0n leqnn subnn subn0.
have -> : (s1 + p - s0 <= p - s0) = false.
  by rewrite -(addnBA _ (ltnW s0p)) leqNgt -{1}[p - s0]add0n ltn_add2r s1_gt0.
rewrite [s1 <= 0]leqNgt s1_gt0 /= -(addnBA _ (ltnW s0p)) subnDA subnAC.
by rewrite [p - s0 + p]addnC addnK.
Qed.

(** The counting identity behind the [(ν - id)] relation. *)
Lemma shift_count s0 s1 :
  s0 < p -> s1 < p ->
  (dmod (sh s0) 0 < dmod s0 s1) + (s0 == 0) = (dmod s0 0 < dmod s0 s1) + (s1 == 0).
Proof.
move=> s0p s1p; rewrite (dmodE s0p s1p) (dmodE s0p p_gt0) (dmodE (sh_lt s0) p_gt0) /sh.
case: (posnP s0) => [-> | s0_gt0].
  rewrite !leq0n /= !subn0; case: (ltnP 1 p) => hp1.
    rewrite /= add0n [p - 1 < s1]ltnNge subn1 -ltnS (prednK p_gt0) s1p /= add0n.
    by rewrite eqn0Ngt; case: (0 < s1).
  by have -> : s1 = 0 by apply/eqP; rewrite -leqn0 -ltnS (leq_trans s1p hp1).
rewrite [s0 <= 0]leqNgt s0_gt0 /= add0n addn0.
case: (ltnP s0.+1 p) => h1.
  rewrite ltn0; case: (leqP s0 s1) => h01.
    have hs1 : s1 <= p.-1 by rewrite -ltnS prednK.
    have h1' : s1 - s0 <= p - s0.+1 by rewrite subnS predn_sub leq_sub2r.
    rewrite ltnNge h1' /= ltnNge (leq_sub2r s0 (ltnW s1p)) /=.
    by rewrite eqn0Ngt (leq_trans s0_gt0 h01).
  rewrite -(addnBA _ (ltnW s0p)).
  have -> : p - s0.+1 < s1 + (p - s0).
    by rewrite subnS; apply: leq_trans (leq_addl s1 _); rewrite ltn_predL subn_gt0.
  by rewrite -{1}[p - s0]add0n ltn_add2r eqn0Ngt; case: (0 < s1).
have ep : s0.+1 = p by apply/eqP; rewrite eqn_leq s0p h1.
rewrite leqnn subnn -ep subSnn; case: (leqP s0 s1) => h01.
  have es : s1 = s0 by apply/eqP; rewrite eqn_leq h01 -ltnS ep s1p.
  by rewrite es subnn ltnn ltn0 eqn0Ngt s0_gt0.
rewrite addnS (subSn (leq_addl s1 s0)) addnK ltn0Sn ltnS eqn0Ngt.
by case: (0 < s1).
Qed.

(** ** The co-hemisphere cochains, at the level of value sequences *********)

(** [Phi d s]: the value of the cochain [φ_d] on the ordered simplex whose
    vertices carry the residues [s = s_0 … s_d] (HSSZ [u ∘ f_d ∘ h]). *)
Definition Phi (d : nat) (s : seq nat) : bool :=
  (size s == d.+1) &&
  (if odd d then (dmod (head 0 s) 0 < head 0 (diffs s)) && salt (behead (diffs s))
   else (head 0 s == 0) && salt (diffs s)).


Lemma odd2l l : odd (2 * l) = false.
Proof. by rewrite mul2n odd_double. Qed.

Lemma Phi_evenE d s :
  odd d = false -> size s = d.+1 -> Phi d s = (head 0 s == 0) && salt (diffs s).
Proof. by move=> od sz; rewrite /Phi sz eqxx od. Qed.

Lemma Phi_oddE d s :
  odd d -> size s = d.+1 ->
  Phi d s = (dmod (head 0 s) 0 < head 0 (diffs s)) && salt (behead (diffs s)).
Proof. by move=> od sz; rewrite /Phi sz eqxx od. Qed.

Lemma Phi_size d s : size s != d.+1 -> Phi d s = false.
Proof. by move=> h; rewrite /Phi (negbTE h). Qed.

Lemma natr_and (R : comNzRingType) (b1 b2 : bool) :
  ((b1 && b2)%:R = b1%:R * b2%:R :> R)%R.
Proof. by rewrite -mulnb natrM. Qed.

(** The relation [φ_{2l} ∘ ∂ = φ_{2l+1} ∘ (ν - id)] on value sequences. *)
Lemma Phi_bd_even (R : comNzRingType) l s :
  size s = (2 * l).+2 -> all (fun x => x < p) s ->
  (\sum_(i < (2 * l).+2) (-1) ^+ i * (Phi (2 * l) (delete i s))%:R
   = (Phi (2 * l).+1 (map sh s))%:R - (Phi (2 * l).+1 s)%:R :> R)%R.
Proof.
case: s => [|s0 [|s1 s']] // sz alls.
have /and3P [s0p s1p alls'] : [&& s0 < p, s1 < p & all (fun x => x < p) s'] := alls.
have oddn : odd (2 * l) = false := odd2l l.
set n := 2 * l in sz oddn *.
set a := diffs [:: s0, s1 & s'].
have sza : size a = n.+1 by rewrite /a size_diffs sz.
have aE : a = dmod s0 s1 :: diffs (s1 :: s') by [].
have alla : all (fun x => x < p) a := all_diffs _.
have term0 : Phi n (delete 0 [:: s0, s1 & s']) = (s1 == 0) && salt (behead a).
  by rewrite delete0 (Phi_evenE oddn) // size_behead sz.
have termL : Phi n (delete n.+1 [:: s0, s1 & s']) = (s0 == 0) && salt (take n a).
  rewrite (Phi_evenE oddn) ?size_delete ?sz //.
  by rewrite head_delete // (diffs_delete_last (n := n)) ?sz.
have termM i : i < n ->
    Phi n (delete i.+1 [:: s0, s1 & s']) = (s0 == 0) && salt (mergeat i a).
  move=> hi; rewrite (Phi_evenE oddn) ?size_delete ?sz //;
    first [by rewrite head_delete // diffs_delete_mid ?sz // !ltnS | exact: leqW hi].
rewrite big_ord_recl big_ord_recr expr0 mul1r term0.
rewrite !lift0 termL.
rewrite -[((-1) ^+ ord_max.+1)%R]signr_odd /= oddn expr1 mulN1r.
under eq_bigr => i _ do
  rewrite -[bump 0 i]/(i.+1) (termM _ (ltn_ord i)) natr_and exprS mulN1r mulNr mulrCA.
rewrite sumrN -mulr_sumr (salt_merge_sum R sza alla) -/n.
rewrite !(Phi_oddE (d := n.+1)) //= ?oddn ?size_map ?sz //.
have e1 : (match s' with | [::] => [::] | y :: _ => dmod s1 y :: diffs s' end)
          = diffs (s1 :: s') by [].
have e2 : (match [seq sh i | i <- s'] with
           | [::] => [::] | y :: _ => dmod (sh s1) y :: diffs [seq sh i | i <- s'] end)
          = diffs (s1 :: s').
  by rewrite -[LHS]/(diffs (map sh (s1 :: s'))) diffs_map_sh //= s1p.
rewrite e1 e2 (dmod_sh s0p s1p) !natr_and.
have hR : ((dmod (sh s0) 0 < dmod s0 s1)%:R + (s0 == 0)%:R
           = (dmod s0 0 < dmod s0 s1)%:R + (s1 == 0)%:R :> R)%R.
  by rewrite -!natrD shift_count.
rewrite mulrBr opprB addrAC subrr sub0r -!mulrBl; congr (_ * _)%R.
have -> : ((s1 == 0)%:R = (dmod (sh s0) 0 < dmod s0 s1)%:R + (s0 == 0)%:R
                           - (dmod s0 0 < dmod s0 s1)%:R :> R)%R.
  by rewrite hR [((dmod s0 0 < dmod s0 s1)%:R + _)%R]addrC addrK.
by rewrite addrAC addrK.
Qed.

(** The relation [φ_{2l+1} ∘ ∂ = φ_{2l+2} ∘ (Σ_r ν^r)] on value sequences. *)
Lemma Phi_bd_odd (R : comNzRingType) l s :
  size s = (2 * l).+3 -> all (fun x => x < p) s ->
  (\sum_(i < (2 * l).+3) (-1) ^+ i * (Phi (2 * l).+1 (delete i s))%:R
   = \sum_(r < p) (Phi (2 * l).+2 (shiftv r s))%:R :> R)%R.
Proof.
case: s => [|s0 [|s1 [|s2 s']]] // sz alls.
have /and4P [s0p s1p s2p alls'] :
    [&& s0 < p, s1 < p, s2 < p & all (fun x => x < p) s'] := alls.
have oddn : odd (2 * l) = false := odd2l l.
set n := 2 * l in sz oddn *.
set a := diffs [:: s0, s1, s2 & s'].
have sza : size a = n.+2 by rewrite /a size_diffs sz.
have aE : a = dmod s0 s1 :: dmod s1 s2 :: diffs (s2 :: s') by [].
have alla : all (fun x => x < p) a := all_diffs _.
have szb : size (behead a) = n.+1 by rewrite size_behead sza.
have allb : all (fun x => x < p) (behead a) := all_behead alla.
have oddn1 : odd n.+1 by rewrite /= oddn.
have oddn2 : odd n.+2 = false by rewrite /= oddn.
have term0 : Phi n.+1 (delete 0 [:: s0, s1, s2 & s'])
             = (dmod s1 0 < dmod s1 s2) && salt (diffs (s2 :: s')).
  by rewrite delete0 (Phi_oddE oddn1) // size_behead sz.
have term1 : Phi n.+1 (delete 1 [:: s0, s1, s2 & s'])
             = (dmod s0 0 < (dmod s0 s1 + dmod s1 s2) %% p) && salt (diffs (s2 :: s')).
  rewrite (Phi_oddE oddn1) ?size_delete ?sz //.
  by rewrite head_delete // (diffs_delete_mid (i := 1)) ?sz // -/a aE mergeat0.
have termM i : i < n -> Phi n.+1 (delete i.+2 [:: s0, s1, s2 & s'])
             = (dmod s0 0 < dmod s0 s1) && salt (mergeat i (behead a)).
  move=> hi; rewrite (Phi_oddE oddn1) ?size_delete ?sz //;
    first [by rewrite head_delete // diffs_delete_mid ?sz // -/a aE mergeat_cons1 | exact: leqW hi].
have termL : Phi n.+1 (delete n.+2 [:: s0, s1, s2 & s'])
             = (dmod s0 0 < dmod s0 s1) && salt (take n (behead a)).
  rewrite (Phi_oddE oddn1) ?size_delete ?sz //.
  by rewrite head_delete // (diffs_delete_last (n := n.+1)) ?sz // -/a aE.
rewrite 2!big_ord_recl big_ord_recr expr0 mul1r expr1 mulN1r term0 !lift0 term1.
rewrite termL -[((-1) ^+ ord_max.+2)%R]signr_odd /= oddn expr0 mul1r.
under eq_bigr => i _ do
  rewrite -[bump 0 (bump 0 i)]/(i.+2) (termM _ (ltn_ord i)) natr_and
          !exprS !mulN1r opprK mulrCA.
rewrite -mulr_sumr (salt_merge_sum R szb allb) -/n.
have eD : (match s' with | [::] => [::] | y :: _ => dmod s2 y :: diffs s' end)
          = diffs (s2 :: s') by [].
have eBB : behead (behead a) = diffs (s2 :: s') by rewrite aE.
rewrite !eD eBB -[dmod s1 s2 :: diffs (s2 :: s')]/(behead a).
under [in RHS]eq_bigr => r _ do
  rewrite (Phi_evenE oddn2) ?size_shiftv ?sz // (diffs_shiftv _ alls) -/a
          shiftv_cons /= iter_sh // natr_and.
rewrite -mulr_suml count_shift0 // mul1r eD !natr_and mulrBr subrK.
have hR : ((dmod s1 0 < dmod s1 s2)%:R + (dmod s0 0 < dmod s0 s1)%:R
           = (dmod s0 0 < (dmod s0 s1 + dmod s1 s2) %% p)%:R
             + (p <= dmod s0 s1 + dmod s1 s2)%:R :> R)%R.
  by rewrite -!natrD -(dmod_a1 s0p s1p) sigma_count // dmod_lt.
rewrite addrA -mulNr -!mulrDl; congr (_ * _)%R.
by rewrite addrAC hR addrAC subrr add0r.
Qed.

(** The base case: [Σ_r φ_0(ν^r v) = 1] for every vertex. *)
Lemma Phi0_shift (R : comNzRingType) v :
  v < p -> (\sum_(r < p) (Phi 0 (shiftv r [:: v]))%:R = 1 :> R)%R.
Proof.
move=> vp; rewrite -[RHS](count_shift0 R vp); apply: eq_bigr => r _.
by rewrite shiftv_cons shiftv_nil /Phi /= iter_sh // andbT.
Qed.

End Salt.
