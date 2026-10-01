(** * Directed low-arc Hamilton construction for k=7, C12

    This module is an opacity boundary for the constructive cycle splice:
    an oriented arc between the two low endpoints yields a Hamilton ordering
    ending at its tail. *)

From HB Require Import structures.
From mathcomp Require Import all_boot zify.
From Stdlib Require Import Lia.
From Digraph Require Import
  prelude digraph oriented dipath ckpath_cycle_tools ckpath_even_gateway
  ckpath_kernel_prefix_adapters ckpath_k7_c12_low_hand.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section C12LowArcHamilton.
Variable D : orientedDigraph.
Variables (c : seq D) (S : {set D}) (v0 v1 : D).

Hypothesis Hreg : forall v : D, outdeg v = 7.
Hypothesis Hell : ell D = 13.
Hypothesis Hprefix : ckpath_prefix2_data c S v0 v1.
Hypothesis Hcycle : dicycle c.
Hypothesis Hcsize : size c = 12.
Hypothesis HScard : #|S| = 7.

Local Notation C := (ckpath_cycle_set c).
Local Notation R := (ckpath_outside c).
Local Notation Q := (C :\: S).
Local Notation Low := (c12_k7_low_endpoints c).
Local Notation B := (ckpath_successor_set c S).

Theorem c12_k7_low_arc_hamilton
    (Hcard : #|Low| = 2) q0 r0 :
  q0 \in Low -> r0 \in Low -> q0 != r0 -> q0 --> r0 ->
  c12_k7_hamilton_from c B q0.
Proof.
have LowSub := c12_k7_low_subset_complement Hreg Hprefix.
move=> q0Low r0Low q0Dr0 aq0r0.
have q0C : q0 \in C.
  by move: q0Low; rewrite (c12_k7_low_endpointP c Hreg) => /andP[].
have r0C : r0 \in C.
  by move: r0Low; rewrite (c12_k7_low_endpointP c Hreg) => /andP[].
have q0c : q0 \in c by move: q0C; rewrite /C /ckpath_cycle_set inE.
have q0deg := c12_k7_low_internal_eq1 Hreg Hell Hprefix Hcycle Hcsize HScard
  Hcard q0Low.
have r0deg := c12_k7_low_internal_eq1 Hreg Hell Hprefix Hcycle Hcsize HScard
  Hcard r0Low.
have uc : uniq c by case/and3P: Hcycle.
have SpN0 : S :\ prev c q0 != set0.
  apply/negP=> /eqP Sp0.
  have h := cardsD1 (prev c q0) S.
  move: h; rewrite Sp0 cards0 HScard.
  by case: (prev c q0 \in S).
move/set0Pn: SpN0 => [p pRest].
have pDprev : p != prev c q0.
  by move: pRest; rewrite !inE => /andP[].
have pS : p \in S.
  move: pRest; rewrite inE => /andP[_ pS].
  exact pS.
have q0Q := subsetP LowSub q0 q0Low.
have r0Q := subsetP LowSub r0 r0Low.
have q0NS : q0 \notin S by move: q0Q; rewrite /Q !inE => /andP[].
have r0NS : r0 \notin S by move: r0Q; rewrite /Q !inE => /andP[].
have pDq0 : p != q0.
  apply/eqP=> pq0; subst p.
  by move: q0NS; rewrite pS.
have pDr0 : p != r0.
  apply/eqP=> pr0; subst p.
  by move: r0NS; rewrite pS.
have SsubC : S \subset C := prefix2_S_subset Hprefix.
have pC := subsetP SsubC p pS.
have pc : p \in c by move: pC; rewrite /C /ckpath_cycle_set inE.
set x := next c p.
have xc : x \in c by rewrite /x mem_next.
have q0Dx : q0 != x.
  apply/negP=> /eqP q0x.
  have pEq : p == prev c q0.
    apply/eqP.
    rewrite q0x /x.
    exact: esym (prev_next uc p).
  by move: pDprev; rewrite pEq.
have [s [ps szs cover _ lastE]] := dicycle_unroll Hcycle xc.
have lastp : last x s = p.
  move: lastE.
  by rewrite /x (prev_next uc p).
have q0full : q0 \in x :: s by rewrite cover q0c.
have q0ins : q0 \in s.
  move: q0full.
  by rewrite inE (negbTE q0Dx).
case splitE : _ / (splitPr q0ins) => [a t].
have tNnil : t != [::].
  apply/eqP=> tnil.
  have q0p : q0 = p.
    move: lastp.
    by rewrite splitE tnil cats1 last_rcons.
  by move: pDq0; rewrite -q0p eqxx.
case: t tNnil splitE => [|y b] //= _ splitE.
have hpath := dipath_path ps.
have /and4P[hpa haq0 aq0y hyb] :
    [&& path arc x a, last x a --> q0, q0 --> y & path arc y b].
  by move: hpath; rewrite splitE cat_path /=.
have lastyb : last y b = p.
  move: lastp.
  by rewrite splitE last_cat /=.
have yfull : y \in x :: s.
  have ytail : y \in q0 :: y :: b by rewrite inE mem_head orbT.
  have ys : y \in s by rewrite splitE mem_cat ytail orbT.
  by rewrite inE ys orbT.
have yc : y \in c by move: yfull; rewrite cover.
have yC : y \in C by move: yc; rewrite /C /ckpath_cycle_set inE.
have yE : y = r0 :=
  c12_k7_one_internal_outneighbor q0deg yC r0C aq0y aq0r0.
subst y.
have bNnil : b != [::].
  apply/eqP=> bnil.
  have r0p : r0 = p by move: lastyb; rewrite bnil.
  by move: pDr0; rewrite -r0p eqxx.
case: b bNnil hyb lastyb splitE => [|z d] //= _ hyb lastyb splitE.
move: hyb => /= /andP[ar0z hzd].
have zrd : z \in r0 :: z :: d by rewrite inE mem_head orbT.
have ztail : z \in q0 :: r0 :: z :: d by rewrite inE zrd orbT.
have zfull : z \in x :: s.
  have zs : z \in s by rewrite splitE mem_cat ztail orbT.
  by rewrite inE zs orbT.
have zc : z \in c by move: zfull; rewrite cover.
have zC : z \in C by move: zc; rewrite /C /ckpath_cycle_set inE.
have last_mem (x0 : D) (s0 : seq D) : last x0 s0 \in x0 :: s0.
  case: s0 => [|u s0] /=.
  - exact: mem_head.
  - rewrite inE; apply/orP; right.
    exact: mem_last.
have hpre : last x a \in x :: a := last_mem x a.
have hfull : last x a \in x :: s.
  rewrite splitE -cat_cons mem_cat.
  apply/orP; left.
  exact hpre.
have hc : last x a \in c by move: hfull; rewrite cover.
have hC : last x a \in C by move: hc; rewrite /C /ckpath_cycle_set inE.
have up := dipath_uniq ps.
have dis : ~~ has (mem (x :: a)) (q0 :: r0 :: z :: d).
  move: up.
  rewrite splitE -cat_cons cat_uniq.
  move=> /and3P[_ hdis _].
  exact: hdis.
have zNpre : z \notin x :: a.
  apply/negP=> zpre.
  have zhas : has (mem (x :: a)) (q0 :: r0 :: z :: d).
    apply/hasP; exists z; first exact ztail.
    exact zpre.
  by move: dis; rewrite zhas.
have hDz : last x a != z.
  apply/eqP=> hz.
  by move: zNpre; rewrite -hz hpre.
have hDr0 : last x a != r0.
  apply/eqP=> hr0.
  move: haq0.
  by rewrite hr0 (arc_asymm _ _ aq0r0).
have ar0hF : r0 --> last x a = false.
  apply/negP=> ar0h.
  have zh := c12_k7_one_internal_outneighbor
    r0deg zC hC ar0z ar0h.
  by move: hDz; rewrite eq_sym zh eqxx.
have har0 : last x a --> r0.
  have /orP[har0|ar0h] :=
    c12_k7_low_cycle_total Hreg Hprefix Hcycle Hcsize HScard
      Hcard hC r0C hDr0.
  - exact har0.
  - by move: ar0hF; rewrite ar0h.
have apq0 : p --> q0.
  have /orP[apq0|aq0p] :=
    c12_k7_low_cycle_total Hreg Hprefix Hcycle Hcsize HScard
      Hcard pC q0C pDq0.
  - exact apq0.
  - have rp := c12_k7_one_internal_outneighbor
      q0deg r0C pC aq0r0 aq0p.
    by move: pDr0; rewrite -rp eqxx.
have ps' : dipath x (a ++ q0 :: r0 :: z :: d) by rewrite -splitE.
have lastarc : last r0 (z :: d) --> q0.
  change (last z d --> q0).
  by rewrite lastyb apq0.
have prot : dipath x (a ++ r0 :: rcons (z :: d) q0).
  exact: c12_k7_skip_append_dipath ps' har0 lastarc.
have tailperm :
    perm_eq (a ++ r0 :: rcons (z :: d) q0)
            (a ++ q0 :: r0 :: z :: d).
  rewrite perm_cat2l -cats1.
  by rewrite -cat_cons -cat1s perm_catC.
have fullperm :
    perm_eq (x :: (a ++ r0 :: rcons (z :: d) q0)) (x :: s).
  rewrite perm_cons splitE.
  exact tailperm.
exists x, (a ++ r0 :: rcons (z :: d) q0).
split.
- rewrite /B /ckpath_successor_set /x.
  apply/imsetP; exists p => //.
- split.
  + exact prot.
  + by rewrite last_cat /= last_rcons.
  + rewrite (perm_size tailperm) -splitE.
    move: szs.
    by rewrite Hcsize.
  + move=> w.
    by rewrite (perm_mem fullperm) cover.
Qed.

End C12LowArcHamilton.
