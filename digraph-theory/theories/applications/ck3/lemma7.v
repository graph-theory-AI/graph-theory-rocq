(** * Digraph.lemma7 — the Cheng–Keevash kernel (dossier §2), uniform in δ

    The proof internals of Cheng–Keevash Lemma 7 (arXiv:2402.16776 §4) in
    the kernel setting KS: H oriented, strong, δ-outregular (δ ≥ 1),
    nonempty, with ℓ(H) ≤ 2δ−1. A maximum path of maximum cycle bound
    (= minimum back-arc index a) is chosen once; the file proves a ≥ 1,
    a ≤ ℓ−δ (K-D), Claim 11 (K-11), the A/B partition (K-AB), the
    predecessor set B⁻ (K-B⁻), Claim 12 (K-12) and the geometric count
    (K-count), packaged as [kernel_full]. Outside the section:
    - [lemma7]   : Cheng–Keevash Lemma 7, for any oriented digraph;
    - [ck_theorem4_oriented] : ℓ(D) ≥ 2δ − (δ−1)./2 (≥ ⌈3δ/2⌉);
    - [ck_conj1_delta2] : Conjecture 1 at δ = 2.

    All dossier IDs cited per lemma. *)

From HB Require Import structures.
From mathcomp Require Import all_boot.
From Digraph Require Import prelude digraph oriented dipath strong.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Ordinal segment cardinality (counting helper) *)

Lemma card_ord_ltn n k : k <= n -> #|[set i : 'I_n | i < k]| = k.
Proof.
move=> kn.
have winj : injective (widen_ord kn).
  by move=> i j /(congr1 val) /= ij; apply: val_inj.
rewrite -[RHS]card_ord -[RHS]cardsT -(card_imset _ winj).
apply: eq_card => i; rewrite inE.
apply/idP/imsetP=> [ilt|[j _ ->]]; last by rewrite /= ltn_ord.
by exists (Ordinal ilt); rewrite ?inE //; apply: val_inj.
Qed.

Lemma card_ord_seg n lo hi : lo <= hi -> hi <= n ->
  #|[set i : 'I_n | lo <= i < hi]| = hi - lo.
Proof.
move=> lohi hin.
have -> : [set i : 'I_n | lo <= i < hi]
          = [set i : 'I_n | i < hi] :\: [set i : 'I_n | i < lo].
  by apply/setP=> i; rewrite !inE -leqNgt andbC.
rewrite cardsD.
have -> : [set i : 'I_n | i < hi] :&: [set i : 'I_n | i < lo]
          = [set i : 'I_n | i < lo].
  apply/setP=> i; rewrite !inE andb_idl //.
  by move=> ilo; exact: leq_trans ilo lohi.
by rewrite !card_ord_ltn // (leq_trans lohi hin).
Qed.

(** ** The derived objects of the kernel (usable outside the section) *)

Section CKDefs.
Variables (D : diGraphType).

(** The endpoint cycle as a seq: the suffix of the path from index a. *)
Definition ckC (x : D) s (a : nat) : seq D := drop a (x :: s).

(** Its vertex set. *)
Definition ckCset x s a : {set D} := [set z in ckC x s a].

(** A = the out-neighbours of [v_(a-1)] in the path prefix. *)
Definition ckA (x : D) s (a : nat) : {set D} :=
  [set z in take a (x :: s) | nth x (x :: s) a.-1 --> z].

(** B = the out-neighbours of v_{a-1} on the cycle. *)
Definition ckB x s a : {set D} :=
  [set z in ckC x s a | nth x (x :: s) a.-1 --> z].

(** S = B⁻, the C-predecessors of B. *)
Definition ckS x s a : {set D} :=
  [set prev (ckC x s a) z | z in ckB x s a].

End CKDefs.

(** In an oriented graph, the two final vertices of the prefix cannot be
    out-neighbours of [v_(a-1)]: one is [v_(a-1)] itself, and the other
    sends the preceding path arc into it. *)
Lemma ck_path_prefix_out_card (H : orientedDigraph) (x : H) (s : seq H)
    (a : nat) :
  dipath x s -> 1 <= a -> a < size (x :: s) ->
  #|ckA x s a| <= a.-2.
Proof.
move=> ps a_ge1 a_lt.
rewrite /ckA.
pose P := x :: s.
pose w := nth x P a.-1.
pose A : {set H} := [set z in take a P | w --> z].
have uP : uniq P by exact: dipath_uniq ps.
have sub : A \subset [set z in take a.-2 P].
  apply/subsetP=> z; rewrite !inE => /andP[zt az].
  have zP : z \in P by exact: mem_take zt.
  have iz_lt : index z P < a by exact: index_ltn zt.
  have iz_ne_last : index z P != a.-1.
    apply/eqP=> izE.
    have zE : z = w.
      rewrite /w -izE.
      by rewrite nth_index.
    by move: az; rewrite zE arc_irrefl.
  have a_ge2 : 2 <= a.
    move: a_ge1; rewrite leq_eqVlt => /orP[/eqP aE|a2]; last exact: a2.
    move: iz_lt iz_ne_last; rewrite -aE /=.
    by case: (x == z).
  have ale_s : a <= size s by move: a_lt; rewrite /P /= ltnS.
  have ap1pos : 0 < a.-1 by rewrite ltn_predRL.
  have ap2p1 : a.-2 < a.-1 by rewrite ltn_predL ap1pos.
  have ap1_lt_s : a.-1 < size s.
    rewrite -ltnS (prednK a_ge1) ltnS.
    exact: ale_s.
  have ia : a.-2 < size s := ltn_trans ap2p1 ap1_lt_s.
  have arc_prev : nth x P a.-2 --> w.
    have h := dipath_arc_nth (dipath_path ps) (i := a.-2).
    have h2 := h ia.
    have succE : (a.-2).+1 = a.-1 by exact: prednK ap1pos.
    by rewrite /w -succE.
  have iz_ne_prev : index z P != a.-2.
    apply/eqP=> izE.
    have zE : z = nth x P a.-2.
      rewrite -izE.
      by rewrite nth_index.
    by move: az; rewrite zE (arc_asymm _ _ arc_prev).
  have iz_lt_pred : index z P < a.-1.
    rewrite ltn_neqAle; apply/andP; split; first exact: iz_ne_last.
    by rewrite -ltnS (prednK a_ge1).
  have iz_small : index z P < a.-2.
    rewrite ltn_neqAle; apply/andP; split; first exact: iz_ne_prev.
    by rewrite -ltnS (prednK ap1pos).
  rewrite in_take //.
have leA := subset_leq_card sub.
rewrite /A /P /w in leA.
rewrite /P in leA.
suff hcard : #|[set z in take a.-2 (x :: s)]| <= a.-2.
  exact: leq_trans leA hcard.
rewrite cardsE.
have utake : uniq (take a.-2 (x :: s))
  by exact: take_uniq _ (dipath_uniq ps).
rewrite (card_uniqP utake) size_takel //.
exact: leq_trans (leq_pred (a.-1))
  (leq_trans (leq_pred a) (ltnW a_lt)).
Qed.

(** ** The kernel section (KS) *)

Section Kernel.
Variables (H : orientedDigraph) (delta : nat).
Hypothesis Hreg : forall v : H, outdeg v = delta.
Hypothesis Hd : 0 < delta.
Hypothesis Hn : 0 < #|H|.
Hypothesis Hstr : strongb H.
Hypothesis Hell : ell H < 2 * delta.

Local Notation L := (ell H).

Let nbig : 2 * delta + 1 <= #|H|.
Proof. by apply: oriented_card => // v; rewrite Hreg. Qed.

(** *** The choice: a maximum path with minimum back-arc index *)

Let mptype : predArgType := (H * L.-tuple H)%type.
Let isMP (p : mptype) := dipath p.1 p.2.
Let aidx (p : mptype) := find [pred z | last p.1 p.2 --> z] (p.1 :: p.2).

Let exMP : exists p : mptype, isMP p.
Proof.
have [x [s [ps sE]]] := ellP Hn.
by exists (x, tcast sE (in_tuple s)); rewrite /isMP /= val_tcast.
Qed.

Let mp0 : mptype := xchoose exMP.
Let pstar : mptype := [arg min_(p < mp0 | isMP p) aidx p].

Let pstarMP : isMP pstar.
Proof. by rewrite /pstar; case: arg_minnP => //; exact: (xchooseP exMP). Qed.

Let pstar_min (q : mptype) : isMP q -> aidx pstar <= aidx q.
Proof.
move=> hq; rewrite /pstar.
by case: arg_minnP => [|p _ pmin]; [exact: (xchooseP exMP) | exact: pmin].
Qed.

Let x : H := pstar.1.
Let s : seq H := pstar.2.
Let y : H := last x s.
Let a : nat := aidx pstar.

Let ps : dipath x s. Proof. exact: pstarMP. Qed.
Let sL : size s = L. Proof. by rewrite /s size_tuple. Qed.
Let uP : uniq (x :: s). Proof. exact: dipath_uniq ps. Qed.

(** K-A specialized to the chosen path. *)
Let endclosure z : y --> z -> z \in x :: s.
Proof. exact: maxpath_endclosure ps sL. Qed.

(** *** Position bookkeeping for the back-arcs of y *)

Let aE : a = find [pred z | y --> z] (x :: s).
Proof. by []. Qed.

Let has_back : has [pred z | y --> z] (x :: s).
Proof.
have : 0 < outdeg y by rewrite Hreg.
rewrite /outdeg card_gt0 => /set0Pn[z]; rewrite inE => az.
by apply/hasP; exists z => //; exact: endclosure.
Qed.

Let a_lt : a < size (x :: s).
Proof. by rewrite aE -has_find has_back. Qed.

Let arc_y_a : y --> nth x (x :: s) a.
Proof. by have := nth_find x has_back; rewrite -aE. Qed.

Let a_min i : i < a -> y --> nth x (x :: s) i = false.
Proof. by rewrite aE => ia; have := before_find x ia. Qed.

(** K-a1: a ≥ 1. *)
Let a_ge1 : 1 <= a.
Proof.
rewrite lt0n; apply/eqP=> a0.
have nle : (size s).+2 <= #|H|.
  apply: leq_trans nbig; rewrite sL addn1 !ltnS.
  exact: Hell.
have := maxpath_no_loopback Hstr ps sL nle.
by have := arc_y_a; rewrite a0 /= => ->.
Qed.

(** K-D: a ≤ L − δ. *)
Let a_le : a + delta <= L.
Proof.
pose P := x :: s.
pose Iset := [set i : 'I_(size P) | y --> nth x P i].
have nth_inj : injective (fun i : 'I_(size P) => nth x P i).
  move=> i j eq_n; apply: val_inj.
  by apply/eqP; rewrite -(nth_uniq x (ltn_ord i) (ltn_ord j) uP) eq_n.
have cardI : #|Iset| = delta.
  rewrite -[RHS](Hreg y) /outdeg -(card_imset _ nth_inj).
  apply: eq_card => z; apply/imsetP/idP=> [[i]|az].
    by rewrite !inE => az ->.
  rewrite inE in az.
  have zP : z \in P by exact: endclosure.
  have ilt : index z P < size P by rewrite index_mem.
  exists (Ordinal ilt); last by rewrite /= nth_index.
  by rewrite inE /= nth_index.
have Isub : Iset \subset [set i : 'I_(size P) | a <= i < L].
  apply/subsetP=> i; rewrite !inE => ai.
  apply/andP; split.
    by rewrite leqNgt; apply/negP=> ia; rewrite a_min in ai.
  have iLe : (i : nat) <= L.
    by have := ltn_ord i; move: (nat_of_ord i) => m /=; rewrite sL ltnS.
  rewrite ltn_neqAle iLe andbT.
  apply/eqP=> iL; move: ai.
  have yE : y = nth x P (ell H) by rewrite /y (last_nth x) sL.
  move=> ai; rewrite iL -yE in ai.
  by move: ai; rewrite arc_irrefl.
have := subset_leq_card Isub.
rewrite cardI card_ord_seg ?leq_subLR //.
- have aL : a <= L by have := a_lt; rewrite /= sL ltnS.
  move=> h2.
  by rewrite -(subnKC aL) leq_add2l.
- by have := a_lt; rewrite /= sL ltnS.
- by rewrite /= sL leqnSn.
Qed.

(** *** The endpoint cycle *)

Let Cs : seq H := ckC x s a.
Let CsE : Cs = drop a (x :: s). Proof. by []. Qed.

Let dcC : dicycle Cs.
Proof. exact: dicycle_suffix ps a_lt arc_y_a. Qed.

Let szC : size Cs = L.+1 - a.
Proof. by rewrite CsE size_drop /= sL. Qed.

Let uC : uniq Cs.
Proof. by case/and3P: dcC. Qed.

(** Splitting V(P): prefix + cycle. *)
Let prefC : x :: s = take a (x :: s) ++ Cs.
Proof. by rewrite CsE cat_take_drop. Qed.

(** *** v_{a−1} and the sets A, B, S *)

Let w : H := nth x (x :: s) a.-1.

Let wP : w \in x :: s.
Proof. by rewrite mem_nth // (leq_ltn_trans (leq_pred a) a_lt). Qed.

(** The path arc v_{a−1} --> v_a. *)
Let arc_w_a : w --> nth x (x :: s) a.
Proof.
have := dipath_arc_nth (dipath_path ps) (i := a.-1).
rewrite (prednK a_ge1) => h; apply: h.
by rewrite -ltnS; exact: a_lt.
Qed.

(** K-11 / Claim 11: out-neighbours of v_{a−1} are on P. *)
Let claim11 z : w --> z -> z \in x :: s.
Proof.
move=> arc_wz.
case zxs : (z \in x :: s) => //; exfalso.
pose A1 : {set H} := [set u : H | u \notin x :: s].
have zA1 : z \in A1 by rewrite inE zxs.
pose Z : induced_digraph A1 := Sub z zA1.
have [t1 em] := endmax_ex Z.
have pt1 : dipath Z t1 by exact: endmax_dipath.
pose t1' : seq H := map val t1.
have pt1' : dipath z t1'.
  have h := dipath_map (f := fun u : induced_digraph A1 => val u) val_inj.
  have := h _ _ _ pt1.
  move=> happ; rewrite /t1' -[z]/(val Z).
  by apply: happ => u v0; rewrite sub_arcE.
have memA1 : forall u, u \in z :: t1' -> u \notin x :: s.
  move=> u; rewrite inE => /orP[/eqP->|ut]; first by rewrite zxs.
  case/mapP: ut => U Ut1 ->.
  by have := valP U; rewrite inE.
have takeE : x :: take a.-1 s = take a (x :: s).
  by rewrite -{2}(prednK a_ge1).
have pp : dipath x (take a.-1 s) by exact: dipath_take.
have lastpp : last x (take a.-1 s) = w.
  apply: take_path_last.
  by have := a_lt; rewrite /= ltnS => h2; exact: leq_trans (leq_pred a) h2.
have aless : a <= size s by have := a_lt; rewrite /= ltnS.
have disjA : ~~ has (mem (x :: take a.-1 s)) (z :: t1').
  apply/hasPn=> u uin /=; rewrite takeE.
  apply/negP=> utake.
  have := memA1 u uin.
  by rewrite {1}prefC mem_cat utake.
have glueA : dipath x (take a.-1 s ++ z :: t1').
  by apply: cat_dipath => //; rewrite lastpp.
pose wm : H := last z t1'.
have lastA : last x (take a.-1 s ++ z :: t1') = wm.
  by rewrite last_cat.
pose M := size (take a.-1 s ++ z :: t1').
have ME : M = a + size t1'.
  rewrite /M size_cat size_takel /=; last exact: leq_trans (leq_pred a) aless.
  by rewrite addnS -addSn prednK.
have M_ge1 : 1 <= M by rewrite ME (leq_trans a_ge1) // leq_addr.
have step1 : forall u, u \in Cs -> wm --> u = false.
  move=> u uCs; case au : (wm --> u) => //; exfalso.
  have [su [psu szsu covu au2 lastu]] := dicycle_unroll dcC uCs.
  have disjB : ~~ has (mem (x :: take a.-1 s ++ z :: t1')) (u :: su).
    apply/hasPn=> r rin /=.
    have rCs : r \in Cs by rewrite -covu.
    have := uP; rewrite {1}prefC cat_uniq => /and3P[_ /hasPn hno _].
    apply/negP; rewrite inE mem_cat => /or3P[/eqP rx|rtake|rzt].
    - by have := hno r rCs; rewrite -takeE rx mem_head.
    - by have := hno r rCs; rewrite -takeE inE rtake orbT.
    - have := memA1 r rzt.
      by rewrite {1}prefC mem_cat rCs orbT.
  have glueB : dipath x ((take a.-1 s ++ z :: t1') ++ u :: su).
    by apply: cat_dipath => //; rewrite lastA.
  have := ell_max glueB.
  rewrite size_cat /= -/M szsu szC ME.
  rewrite leqNgt => /negP; apply.
  have szpos : 0 < (ell H).+1 - a.
    by rewrite subn_gt0 ltnS (leq_trans (leq_addr delta a) a_le).
  rewrite (prednK szpos).
  have aleL1 : a <= (ell H).+1.
    by exact: leqW (leq_trans (leq_addr delta a) a_le).
  rewrite [a + size t1']addnC -addnA (subnKC aleL1).
  by rewrite addnS ltnS leq_addl.
have step2 : forall u, wm --> u -> u \in x :: (take a.-1 s ++ z :: t1').
  move=> u arcu.
  case uxs : (u \in x :: s).
    move: uxs; rewrite {1}prefC mem_cat => /orP[utake|uCs]; last first.
      by rewrite (step1 _ uCs) in arcu.
    by rewrite -cat_cons mem_cat takeE utake.
  have uA1 : u \in A1 by rewrite inE uxs.
  have wmE : wm = val (last Z t1).
    have zE : z = val Z by rewrite SubK.
    by rewrite /wm /t1' zE; exact: last_map.
  have arcZ : (last Z t1) --> (Sub u uA1 : induced_digraph A1).
    by rewrite sub_arcE SubK -wmE.
  have := endmax_closure em arcZ.
  rewrite inE => /orP[/eqP UE|Ut1].
    have -> : u = z.
      by rewrite -[u]/(val (Sub u uA1 : induced_digraph A1)) UE SubK.
    by rewrite -cat_cons mem_cat mem_head orbT.
  have ut' : u \in t1'.
    by apply/mapP; exists (Sub u uA1) => //.
  rewrite -cat_cons mem_cat.
  by rewrite [u \in z :: t1']inE ut' orbT orbT.
pose PA := x :: (take a.-1 s ++ z :: t1').
have szPA : size PA = M.+1 by [].
have uPA : uniq PA by exact: dipath_uniq glueA.
have nthinjA : injective (fun i : 'I_(size PA) => nth x PA i).
  move=> i j eq_n; apply: val_inj.
  by apply/eqP; rewrite -(nth_uniq x (ltn_ord i) (ltn_ord j) uPA) eq_n.
pose J := [set i : 'I_(size PA) | wm --> nth x PA i].
have cardJ : #|J| = delta.
  rewrite -[RHS](Hreg wm) /outdeg -(card_imset _ nthinjA).
  apply: eq_card => u; apply/imsetP/idP=> [[i]|au].
    by rewrite !inE => au ->.
  rewrite inE in au.
  have uPA' : u \in PA by exact: step2.
  have ilt : index u PA < size PA by rewrite index_mem.
  exists (Ordinal ilt); last by rewrite /= nth_index.
  by rewrite inE /= nth_index.
have wmnth : wm = nth x PA M.
  by rewrite -lastA /PA (last_nth x).
have Jhi : forall i : 'I_(size PA), i \in J -> (i : nat) < M.-1.
  move=> i; rewrite inE => ai.
  have iM : (i : nat) <> M.
    by move=> iE; rewrite iE -wmnth arc_irrefl in ai.
  have iM1 : (i : nat) <> M.-1.
    move=> iE.
    have parc := dipath_arc_nth (dipath_path glueA) (i := M.-1).
    rewrite (prednK M_ge1) in parc.
    have parc2 : nth x PA M.-1 --> wm.
      by rewrite wmnth; apply: parc; rewrite -/M.
    by rewrite iE (arc_asymm _ _ parc2) in ai.
  have iltM : (i : nat) < M.
    rewrite ltn_neqAle; apply/andP; split; last first.
      by have := ltn_ord i; move: (nat_of_ord i) => m /=; rewrite -/M ltnS.
    exact/eqP.
  rewrite ltn_neqAle; apply/andP; split; first exact/eqP.
  by rewrite -ltnS (prednK M_ge1).
pose j0 := find [pred u | wm --> u] PA.
have hasJ0 : has [pred u | wm --> u] PA.
  have : 0 < outdeg wm by rewrite Hreg.
  rewrite /outdeg card_gt0 => /set0Pn[u0]; rewrite inE => au0.
  by apply/hasP; exists u0 => //; exact: step2.
have j0lt : j0 < size PA by rewrite /j0 -has_find.
have arcj0 : wm --> nth x PA j0 by have := nth_find x hasJ0.
have JN0 : 0 < #|J| by rewrite cardJ.
case/card_gt0P: JN0 => i0 i0J.
have j0M : j0 < M.-1.
  apply: leq_ltn_trans (Jhi _ i0J).
  rewrite leqNgt; apply/negP=> lt0.
  have := before_find x lt0.
  by move=> /= pf; move: i0J; rewrite inE pf.
have Jsub : J \subset [set i : 'I_(size PA) | j0 <= i < M.-1].
  apply/subsetP=> i iJ; rewrite inE (Jhi _ iJ) andbT.
  rewrite leqNgt; apply/negP=> lt0.
  have := before_find x lt0.
  by move=> /= pf; move: iJ; rewrite inE pf.
have dle2 : delta <= M.-1 - j0.
  have := subset_leq_card Jsub.
  rewrite cardJ card_ord_seg //; first exact: ltnW.
  by rewrite szPA (leq_trans (leq_pred M)) // leqnSn.
pose C1 := drop j0 PA.
have dC1 : dicycle C1.
  by apply: dicycle_suffix glueA j0lt _; rewrite lastA.
have szC1 : size C1 = M.+1 - j0 by rewrite /C1 size_drop szPA.
have szC1ge : delta + 2 <= size C1.
  rewrite szC1 -(prednK M_ge1) !subSn ?(ltnW j0M) //.
    by rewrite addn2 !ltnS dle2.
  by rewrite (leq_trans (ltnW j0M)) // leqnSn.
have disjC1 : [disjoint C1 & Cs].
  rewrite disjoint_has; apply/hasPn=> r rCs /=.
  apply/negP=> rC1.
  have rPA : r \in PA by exact: mem_drop rCs.
  have := uP; rewrite {1}prefC cat_uniq => /and3P[_ /hasPn hno _].
  move: rPA; rewrite inE mem_cat => /or3P[/eqP rx|rtake|rzt].
  - by have := hno r rC1; rewrite -takeE rx mem_head.
  - by have := hno r rC1; rewrite -takeE inE rtake orbT.
  - have := memA1 r rzt.
    by rewrite {1}prefC mem_cat rC1 orbT.
have szCge : delta + 1 <= size Cs.
  rewrite szC leq_subRL; last first.
    by rewrite (leq_trans (leq_addr delta a)) // leqW.
  by rewrite addnA addn1 ltnS a_le.
have := disjoint_cycles_path Hstr dC1 dcC disjC1.
rewrite leqNgt => /negP; apply.
have sum_ge : delta + 2 + (delta + 1) - 1 <= size C1 + size Cs - 1.
  by rewrite leq_sub2r // leq_add.
apply: leq_trans sum_ge.
have -> : delta + 2 + (delta + 1) - 1 = 2 * delta + 2.
  by rewrite mul2n -addnn !addn2 !addn1 addnS addSn /= subn1.
by apply: ltn_trans Hell _; rewrite -addn2 -[X in X < _]addn0 ltn_add2l.
Qed.

(** K-AB. *)
Let Aset : {set H} := ckA x s a.
Let Bset : {set H} := ckB x s a.

Let BsetE : Bset = [set z in Cs | w --> z]. Proof. by []. Qed.

Let AB_part : #|Aset| + #|Bset| = delta.
Proof.
have NE : [set z | w --> z] = Aset :|: Bset.
  apply/setP=> z; rewrite BsetE !inE.
  case az: (w --> z); rewrite ?andbF ?andbT //=.
  have zP : z \in x :: s by exact: claim11.
  by move: zP; rewrite {1}prefC mem_cat.
have dis : [disjoint Aset & Bset].
  rewrite disjoints_subset; apply/subsetP=> z; rewrite BsetE !inE.
  case/andP=> zt _; apply/negP=> /andP[zc _].
  have := uP; rewrite {1}prefC cat_uniq => /and3P[_ /hasPn hno _].
  by have := hno z zc; rewrite zt.
have i0 : Aset :&: Bset = set0 by apply: disjoint_setI0.
have := cardsUI Aset Bset.
rewrite i0 cards0 addn0 -NE => <-.
by rewrite -[RHS](Hreg w).
Qed.

Let A_le2 : #|Aset| <= a.-2.
Proof.
exact: ck_path_prefix_out_card ps a_ge1 a_lt.
Qed.

Let A_le : #|Aset| <= a.-1.
Proof.
exact: leq_trans A_le2 (leq_pred (a.-1)).
Qed.

Let va_B : nth x (x :: s) a \in Bset.
Proof.
rewrite BsetE !inE arc_w_a andbT CsE.
apply/(nthP x); exists 0; first by rewrite size_drop subn_gt0.
by rewrite nth_drop addn0.
Qed.

(** K-B⁻. *)
Let Sset : {set H} := ckS x s a.

Let S_card : #|Sset| = #|Bset|.
Proof. exact: card_imset (can_inj (next_prev uC)). Qed.

Let S_sub_C z : z \in Sset -> z \in Cs.
Proof.
case/imsetP=> b bB ->.
by rewrite mem_prev; move: bB; rewrite inE => /andP[].
Qed.

Let yS : y \in Sset.
Proof.
have szpos : 0 < size Cs.
  by rewrite szC subn_gt0 ltnS (leq_trans _ a_le) // leq_addr.
have hE : head y Cs = nth x (x :: s) a.
  rewrite -nth0 CsE nth_drop addn0.
  by apply: set_nth_default; exact: a_lt.
have lastE2 : last y Cs = y.
  have dropE : Cs = drop a.-1 s by rewrite CsE -(prednK a_ge1).
  case Edrop: (drop a.-1 s) => [|h t].
    by move: szpos; rewrite dropE Edrop.
  have lxs : last x s = last h t.
    by rewrite -(cat_take_drop a.-1 s) last_cat Edrop.
  by rewrite dropE Edrop /= -lxs.
have := imset_f (prev Cs) va_B.
by rewrite -hE prev_head // lastE2.
Qed.

(** K-12 / Claim 12. *)
Let claim12 b z : b \in Sset -> b --> z -> z \in Cs.
Proof.
case/imsetP=> bp bpB bE arc_bz.
have bpCs : bp \in Cs by move: bpB; rewrite inE => /andP[].
have arc_w_bp : w --> bp by move: bpB; rewrite inE => /andP[].
have bCs : b \in Cs by rewrite bE mem_prev.
have [t [pt szt cov abt lastEt]] := dicycle_unroll dcC bpCs.
have lastb : last bp t = b by rewrite lastEt bE.
have takeE : x :: take a.-1 s = take a (x :: s).
  by rewrite -{2}(prednK a_ge1).
have pp : dipath x (take a.-1 s) by exact: dipath_take.
have lastpp : last x (take a.-1 s) = w.
  apply: take_path_last.
  by have := a_lt; rewrite /= ltnS => h; exact: leq_trans (leq_pred a) h.
have disj1 : ~~ has (mem (x :: take a.-1 s)) (bp :: t).
  apply/hasPn=> u ut /=.
  have uCs : u \in Cs by rewrite -cov.
  rewrite takeE; apply/negP=> utake.
  have := uP; rewrite {1}prefC cat_uniq => /and3P[_ /hasPn hno _].
  by have := hno u uCs; rewrite utake.
have G1 : dipath x (take a.-1 s ++ bp :: t).
  by apply: cat_dipath => //; rewrite lastpp.
have aless : a <= size s by have := a_lt; rewrite /= ltnS.
have szG1 : size (take a.-1 s ++ bp :: t) = L.
  rewrite size_cat size_takel /=; last exact: leq_trans (leq_pred a) aless.
  rewrite szt szC.
  have aleL : a <= L by exact: leq_trans (leq_addr _ _) a_le.
  by rewrite subSn //= addnS -addSn prednK // addnC subnK.
have lastG1 : last x (take a.-1 s ++ bp :: t) = b.
  by rewrite last_cat /= lastb.
have memG1 : forall u, u \in x :: (take a.-1 s ++ bp :: t) -> u \in x :: s.
  move=> u; rewrite inE mem_cat => /or3P[/eqP->|ut|ubt].
  - by rewrite mem_head.
  - by rewrite inE (mem_take ut) orbT.
  - have : u \in Cs by rewrite -cov.
    by rewrite CsE => /mem_drop.
case zxs : (z \in x :: s); last first.
  exfalso.
  have ext : dipath x (rcons (take a.-1 s ++ bp :: t) z).
    rewrite dipath_rcons G1 lastG1 arc_bz /=.
    by apply/negP=> zin; have := memG1 _ zin; rewrite zxs.
  by have := ell_max ext; rewrite size_rcons szG1 ltnn.
move: (zxs); rewrite {1}prefC mem_cat => /orP[ztake|zCs]; last by [].
exfalso.
pose q : mptype := (x, tcast szG1 (in_tuple (take a.-1 s ++ bp :: t))).
have qMP : isMP q by rewrite /isMP /= val_tcast.
have zmem : z \in x :: (take a.-1 s ++ bp :: t).
  by rewrite -cat_cons mem_cat takeE ztake.
have idxlt : index z (x :: (take a.-1 s ++ bp :: t)) < a.
  rewrite -cat_cons index_cat takeE ztake.
  have : index z (take a (x :: s)) < size (take a (x :: s)).
    by rewrite index_mem.
  by rewrite size_takel // ltnW.
have find_le_ind (p0 : pred H) (l : seq H) (u : H) :
    u \in l -> p0 u -> find p0 l <= index u l.
  move=> ul pu; rewrite leqNgt; apply/negP=> lt.
  by have := before_find x lt; rewrite nth_index // pu.
have aqE : aidx q = find [pred u | b --> u] (x :: (take a.-1 s ++ bp :: t)).
  by rewrite /aidx /q /= val_tcast lastG1.
have aq : aidx q <= index z (x :: (take a.-1 s ++ bp :: t)).
  by rewrite aqE; apply: find_le_ind => //=.
have age := pstar_min qMP.
by have := leq_ltn_trans (leq_trans age aq) idxlt; rewrite ltnn.
Qed.

(** K-count. *)
Let countA v : v \in Sset ->
  #|Sset| + delta - outdeg_in Sset v <= #|ckCset x s a|.
Proof.
move=> vS.
pose NN := [set z : H | v --> z].
have cardNN : #|NN| = delta by rewrite -[RHS](Hreg v).
have dle : outdeg_in Sset v <= delta.
  by rewrite -[X in _ <= X](Hreg v); exact: outdeg_in_le.
have NNsub : NN \subset ckCset x s a.
  apply/subsetP=> z; rewrite !inE => az.
  exact: claim12 vS az.
have Ssub : Sset \subset ckCset x s a.
  by apply/subsetP=> z zS; rewrite inE S_sub_C.
have Usub : Sset :|: (NN :\: Sset) \subset ckCset x s a.
  rewrite subUset Ssub /=.
  by apply: subset_trans (subsetDl _ _) NNsub.
have cardU : #|Sset :|: (NN :\: Sset)| = #|Sset| + (delta - outdeg_in Sset v).
  rewrite cardsU.
  have -> : Sset :&: (NN :\: Sset) = set0.
    by apply/setP=> z; rewrite !inE; case: (z \in Sset); rewrite ?andbF.
  rewrite cards0 subn0 cardsD.
  have -> : NN :&: Sset = [set z in Sset | v --> z].
    by apply/setP=> z; rewrite !inE andbC.
  by rewrite cardNN.
rewrite -addnBA // -cardU.
exact: subset_leq_card.
Qed.

Let countB v : v \in Sset -> 2 * delta - L <= outdeg_in Sset v.
Proof.
move=> vS.
have dle : outdeg_in Sset v <= delta.
  by rewrite -[X in _ <= X](Hreg v); exact: outdeg_in_le.
have cC : #|ckCset x s a| = L.+1 - a.
  by rewrite cardsE (card_uniqP uC) szC.
have hA := countA vS.
rewrite cC in hA.
rewrite leq_subLR.
rewrite -addnBA // in hA.
have aleL1 : a <= L.+1 by exact: leqW (leq_trans (leq_addr delta a) a_le).
have step := leq_add (leqnn a) hA.
rewrite subnKC // in step.
have aA : #|Aset| + 1 <= a by rewrite addn1 -(prednK a_ge1) ltnS A_le.
have step2 := leq_trans
  (leq_add aA (leqnn (#|Sset| + (delta - outdeg_in Sset v)))) step.
move: step2.
rewrite S_card addnAC addn1 ltnS addnA AB_part addnBA // => h2.
by move: h2; rewrite leq_subLR mul2n -addnn addnC.
Qed.

(** *** The package *)

Theorem kernel_full :
  exists (x0 : H) (s0 : seq H) (a0 : nat),
  [/\ [/\ dipath x0 s0, size s0 = L, 1 <= a0 & a0 + delta <= L],
      [/\ dicycle (ckC x0 s0 a0), size (ckC x0 s0 a0) = L.+1 - a0
        & #|ckCset x0 s0 a0| = L.+1 - a0],
      [/\ #|ckS x0 s0 a0| = #|ckB x0 s0 a0|, #|ckB x0 s0 a0| <= delta,
          delta <= #|ckB x0 s0 a0| + a0.-1 & last x0 s0 \in ckS x0 s0 a0],
      (forall b z, b \in ckS x0 s0 a0 -> b --> z -> z \in ckC x0 s0 a0)
    & (forall v, v \in ckS x0 s0 a0 ->
         [/\ #|ckS x0 s0 a0| + delta - outdeg_in (ckS x0 s0 a0) v
               <= #|ckCset x0 s0 a0|
           & 2 * delta - L <= outdeg_in (ckS x0 s0 a0) v]) ].
Proof.
exists x, s, a; split.
- by split.
- split=> //.
  by rewrite cardsE (card_uniqP uC) szC.
- split=> //.
  + by rewrite -(AB_part) leq_addl.
  + by rewrite -(AB_part) addnC leq_add2l A_le.
- exact: claim12.
- by move=> v vS; split; [exact: countA | exact: countB].
Qed.

(** The full kernel package together with the exact A/B partition and the
    oriented-prefix improvement [|A| <= a.-2].  This is a separate API so
    clients of [kernel_full] keep their existing destruct patterns. *)
Theorem kernel_full_AB :
  exists (x0 : H) (s0 : seq H) (a0 : nat),
  [/\ #|ckA x0 s0 a0| + #|ckB x0 s0 a0| = delta,
      #|ckA x0 s0 a0| <= a0.-2
    & [/\ [/\ dipath x0 s0, size s0 = L, 1 <= a0 & a0 + delta <= L],
          [/\ dicycle (ckC x0 s0 a0), size (ckC x0 s0 a0) = L.+1 - a0
            & #|ckCset x0 s0 a0| = L.+1 - a0],
          [/\ #|ckS x0 s0 a0| = #|ckB x0 s0 a0|,
              #|ckB x0 s0 a0| <= delta,
              delta <= #|ckB x0 s0 a0| + a0.-1
            & last x0 s0 \in ckS x0 s0 a0],
          (forall b z, b \in ckS x0 s0 a0 -> b --> z ->
             z \in ckC x0 s0 a0)
        & (forall v, v \in ckS x0 s0 a0 ->
             [/\ #|ckS x0 s0 a0| + delta -
                    outdeg_in (ckS x0 s0 a0) v <= #|ckCset x0 s0 a0|
               & 2 * delta - L <= outdeg_in (ckS x0 s0 a0) v]) ] ].
Proof.
exists x, s, a; split.
- exact: AB_part.
- exact: A_le2.
- split.
  + by split.
  + split=> //.
    by rewrite cardsE (card_uniqP uC) szC.
  + split=> //.
    * by rewrite -(AB_part) leq_addl.
    * by rewrite -(AB_part) addnC leq_add2l A_le.
  + exact: claim12.
  + by move=> v vS; split; [exact: countA | exact: countB].
Qed.

(** The bare Lemma 7 witness. *)
Theorem kernel_S :
  exists S : {set H},
    [/\ S != set0, #|S| <= delta
      & forall v, v \in S -> 2 * delta - L <= outdeg_in S v].
Proof.
exists Sset; split.
- by apply/set0Pn; exists y.
- by rewrite S_card -(AB_part) leq_addl.
- exact: countB.
Qed.

End Kernel.

(** ** Lemma 7 (Cheng–Keevash), in full generality *)

Theorem lemma7 (D : orientedDigraph) (delta : nat) :
  0 < #|D| -> (forall v : D, delta <= outdeg v) ->
  2 * delta <= ell D \/
  exists S : {set D},
    [/\ S != set0, #|S| <= delta
      & forall v, v \in S -> 2 * delta - ell D <= outdeg_in S v].
Proof.
move=> n0 dmin.
case: (leqP (2 * delta) (ell D)) => [|lt]; first by left.
right.
have Hd : 0 < delta.
  by case: (delta) lt => //; rewrite muln0 ltn0.
have [W [hn0 hstr hreg hell hcard]] := reduction n0 dmin.
set HH := induced_oriented W in hn0 hstr hreg hell hcard.
have hell2 : ell HH < 2 * delta by exact: leq_ltn_trans hell lt.
have [S' [S'n0 S'le S'deg]] := kernel_S hreg Hd hn0 hstr hell2.
pose f (u : HH) : D := val u.
have finj : injective f by exact: val_inj.
pose S : {set D} := [set f u | u in S'].
exists S; split.
- case/set0Pn: S'n0 => u0 u0S.
  by apply/set0Pn; exists (f u0); exact: imset_f.
- by rewrite (card_imset _ finj).
move=> v /imsetP[u uS' ->].
have le2 : outdeg_in S' u <= outdeg_in S (f u).
  rewrite /outdeg_in -(card_imset [set w0 in S' | u --> w0] finj).
  apply: subset_leq_card; apply/subsetP=> ww.
  case/imsetP=> w0; rewrite inE => /andP[w0S aw0] ->.
  rewrite inE; apply/andP; split; first exact: imset_f.
  have := aw0; rewrite sub_arcE => aw1.
  exact: (outsel_arc_sub aw1).
apply: leq_trans le2.
apply: leq_trans (S'deg u uS').
by rewrite leq_sub2l.
Qed.

(** ** Theorem 4 (oriented case) and the δ = 2 case of Conjecture 1 *)

Theorem ck_theorem4_oriented (D : orientedDigraph) (delta : nat) :
  0 < #|D| -> (forall v : D, delta <= outdeg v) ->
  2 * delta - (delta - 1)./2 <= ell D.
Proof.
move=> n0 dmin.
case: (lemma7 n0 dmin) => [le2d|[S [Sn0 Sle Sdeg]]].
  by apply: leq_trans le2d; exact: leq_subr.
have [xx xxS xxle] := oriented_avg_bound Sn0.
have h1 : 2 * delta - ell D <= (delta - 1)./2.
  apply: leq_trans (Sdeg _ xxS) (leq_trans xxle _).
  by apply: half_leq; rewrite leq_sub2r.
by rewrite leq_subLR addnC -leq_subLR.
Qed.

Corollary ck_conj1_delta2 (D : orientedDigraph) :
  0 < #|D| -> (forall v : D, 2 <= outdeg v) -> 4 <= ell D.
Proof.
move=> n0 dmin.
exact: (ck_theorem4_oriented n0 dmin).
Qed.
