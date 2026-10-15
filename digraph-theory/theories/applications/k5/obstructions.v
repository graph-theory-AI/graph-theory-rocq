(** * Digraph.obstructions — the 20 infeasible cell-sets

    Paper §5.4(a): a backedge clique of the key order cannot meet certain
    sets of cells. The 20 sets share seven proof shapes:
    - [triple_A] (sets 1–8): cells (X, zero, X), X ∈ {Hi, Lo} outer band;
    - [triple_B] (sets 9–10): cells (zero, X, zero) — opposite arcs;
    - [quad_A] (set 11), [quad_B] (12), [quad_C] (13), [quad_D] (14);
    - [square] (sets 15–20): outer bands alternate — equal-block branches
      give opposite arcs, the distinct branch contradicts H17.

    [no_obstruction] packages all twenty: the cell-occupancy bits of a
    backedge clique never satisfy the obstruction pattern [obstrb]
    (consumed together with coverage.v's 256-case check). *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_fingroup all_algebra.
From Digraph Require Import prelude interop_graph_theory digraph tournament order.
From Digraph Require Import omegabar critical domination.
From Digraph Require Import automorphism product cayley circulant transitive substitution.
From Digraph Require Import acn_arc_facts acn_base in_neighbourhood cells.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Set SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.

(** The 20-disjunct obstruction pattern over the 8 cell-occupancy bits. *)
Definition obstrb (b0 b1 b2 b3 b4 b5 b6 b7 : bool) : bool :=
  [|| b0 && b2 && b3, b1 && b2 && b4, b0 && b2 && b6, b1 && b2 && b7,
      b0 && b5 && b6, b1 && b5 && b7, b3 && b5 && b6, b4 && b5 && b7,
      b2 && b3 && b5, b2 && b4 && b5,
      b0 && b1 && b3 && b5, b1 && b3 && b4 && b5,
      b2 && b3 && b4 && b6, b2 && b4 && b6 && b7,
      b0 && b1 && b3 && b4, b0 && b1 && b3 && b7, b0 && b1 && b6 && b7,
      b0 && b4 && b6 && b7, b1 && b3 && b4 && b6 | b3 && b4 && b6 && b7].

Section Obstructions.
Variable m' : nat.
Local Notation m := m'.+1.
Local Notation n := (m.*2.+1).
Local Notation ACm := (AC m').
Local Notation T5 := (lexprod_tournament ACm ACm).

Lemma nat_n_split : n = (m.+1 + m)%N.
Proof. by rewrite addSn addnn. Qed.

(** Pure-nat helper, kept 'Z_n-free. *)
Let dbl_lt_addr (k x : nat) : (k < x)%N -> (k.*2 < x + k)%N.
Proof. by move=> h; rewrite -addnn ltn_add2r. Qed.

(** ** Membership computations for cross-band differences *)

Lemma mem_sub_Lo_Hi1 (p q : 'Z_n) :
  (0 < val p <= m)%N -> val q = m.+1 ->
  (p - q \in ACset m') = (val p == 1%N).
Proof.
case/andP=> ppos ple vq.
have plt : (val p < val q)%N by rewrite vq ltnS.
rewrite AC_mem_val (val_sub_gt plt) vq.
have step : (n - (m.+1 - val p))%N = (m + val p)%N.
  rewrite subnBA ?(leq_trans ple (leqnSn m)) //.
  move: (val p) => vp.
  by rewrite nat_n_split -addnA addKn.
rewrite step.
have ge : (m < m + val p)%N by rewrite -{1}[m]addn0 ltn_add2l.
rewrite (leq_gtF (ltnW ge)) andbF /=.
by rewrite -[m'.+2]addn1 eqn_add2l.
Qed.

Lemma mem_sub_Hi1_Lo (q r : 'Z_n) :
  val q = m.+1 -> (0 < val r <= m)%N ->
  (q - r \in ACset m') = (2 <= val r)%N.
Proof.
move=> vq /andP[rpos rle].
have rlt : (val r <= val q)%N by rewrite vq (leq_trans rle) // leqnSn.
rewrite AC_mem_val (val_sub_le rlt) vq.
have pos : (0 < m.+1 - val r)%N by rewrite subn_gt0 ltnS.
rewrite pos /=.
have -> : ((m.+1 - val r)%N == m.+1) = false.
  apply/negbTE; rewrite -(eqn_add2r (val r)) subnK //.
    by rewrite -{1}[m'.+2]addn0 eqn_add2l eq_sym; exact: lt0n_neq0.
  by apply: (leq_trans rle); rewrite (leq_trans (leqnSn m)) ?leqnSn.
rewrite orbF ltn_subLR; last first.
  by apply: (leq_trans rle); rewrite (leq_trans (leqnSn m)) ?leqnSn.
by rewrite addnS ltnS -[m'.+2]/((2 + m')%N) leq_add2r.
Qed.

Lemma mem_sub_Hi_m (q r : 'Z_n) :
  (m < val q)%N -> val r = m ->
  (q - r \in ACset m') = (val q < m.*2)%N.
Proof.
move=> hq vr.
have rlt : (val r <= val q)%N by rewrite vr ltnW.
rewrite AC_mem_val (val_sub_le rlt) vr.
rewrite subn_gt0 hq /=.
have hru : (val q <= m.*2)%N by rewrite -ltnS ltn_ord.
have -> : ((val q - m)%N == m.+1) = false.
  apply/negbTE; rewrite -(eqn_add2r m) subnK ?(ltnW hq) //.
  apply/eqP=> e.
  by move: hru; rewrite e addSn addnn ltnn.
rewrite orbF ltn_subLR ?(ltnW hq) //.
by rewrite addnn.
Qed.

Lemma mem_sub_m_Hi (r s : 'Z_n) :
  (m < val r)%N -> val s = m ->
  (s - r \in ACset m') = (val r == m.*2).
Proof.
move=> hr vs.
have slt : (val s < val r)%N by rewrite vs.
rewrite AC_mem_val (val_sub_gt slt) vs.
have hru : (val r <= m.*2)%N by rewrite -ltnS ltn_ord.
have dle : (val r - m <= m)%N.
  by move: (val r) hru => vr hru; rewrite leq_subLR addnn.
have lo : (m < n - (val r - m))%N.
  rewrite ltn_subRL.
  apply: (leq_ltn_trans (leq_add dle (leqnn m))).
  by rewrite addnn ltnSn.
rewrite (leq_gtF (ltnW lo)) andbF /=.
rewrite -(eqn_add2r (val r - m)) subnK; last first.
  rewrite (leq_trans dle) // (leq_trans (leqnSn m)) //.
  by rewrite -[n]/(m.*2.+1) -addnn -addSn leq_addr.
rewrite -[(r : nat)]/(val r : nat).
move: (val r) hr dle => vr hr dle.
rewrite nat_n_split eqn_add2l eq_sym.
rewrite -(eqn_add2r m) subnK ?(ltnW hr) //.
by rewrite addnn.
Qed.

(** Opposite residues cannot both be connection elements. *)
Lemma opp_arcs_contra (x y : 'Z_n) :
  x - y \in ACset m' -> y - x \in ACset m' -> False.
Proof.
move=> h1 h2; apply: (oppA_disjoint h1).
by rewrite opprB.
Qed.

(** ** Reps: band data from cell indices, beat conditions *)

Section WithClique.
Variables (K : {set backedge (qk m')}).
Hypothesis Kcl : forall u v : backedge (qk m'),
  u \in K -> v \in K -> u != v -> u -- v.

Let A1 (u : backedge (qk m')) : 'Z_n := ((u : T5).1 : 'Z_n).

Lemma repA_band (u : backedge (qk m')) (i : nat) :
  cidx (u : T5) = i -> band (A1 u) = ((i %% 3).+1)%N.
Proof.
by move=> e; have [_ d] := cidx_decode (u : T5); rewrite /A1 d e.
Qed.

Lemma rep_Hi (u : backedge (qk m')) (i : nat) :
  cidx (u : T5) = i -> (i %% 3)%N = 0%N -> (m < val (A1 u))%N.
Proof.
move=> e h; have := repA_band e; rewrite h => d.
by rewrite -band1P d.
Qed.

Lemma rep_Lo (u : backedge (qk m')) (i : nat) :
  cidx (u : T5) = i -> (i %% 3)%N = 1%N -> (0 < val (A1 u) <= m)%N.
Proof.
move=> e h; have := repA_band e; rewrite h => d.
by rewrite -band2P d.
Qed.

Lemma rep_Z (u : backedge (qk m')) (i : nat) :
  cidx (u : T5) = i -> (i %% 3)%N = 2%N -> A1 u = 0.
Proof.
move=> e h; have := repA_band e; rewrite h => d.
apply: val_inj => /=.
by apply/eqP; rewrite -band3P d.
Qed.

Lemma beatc (u v : backedge (qk m')) (i j : nat) :
  u \in K -> v \in K -> cidx (u : T5) = i -> cidx (v : T5) = j ->
  (i < j)%N -> A1 u != A1 v -> A1 u - A1 v \in ACset m'.
Proof.
move=> uK vK eu ev ij aD.
have kuv : (key (u : T5) < key (v : T5))%N.
  by apply: cidx_mono; rewrite eu ev.
exact: (beat_blocks Kcl uK vK kuv aD).
Qed.

Lemma bands_neq (u v : backedge (qk m')) (i j : nat) :
  cidx (u : T5) = i -> cidx (v : T5) = j ->
  (i %% 3 != j %% 3)%N -> A1 u != A1 v.
Proof.
move=> eu ev hb; apply/eqP=> e.
move/eqP: hb; apply.
have := repA_band eu; have := repA_band ev.
by rewrite -e => -> [->].
Qed.

(** ** The seven core obstruction shapes *)

(* (X, zero, X) triples — paper sets 1–8 *)
Lemma triple_A (u v w : backedge (qk m')) (i j k : nat) :
  u \in K -> v \in K -> w \in K ->
  cidx (u : T5) = i -> cidx (v : T5) = j -> cidx (w : T5) = k ->
  (i < j)%N -> (j < k)%N -> (j %% 3)%N = 2%N ->
  ((i %% 3 == 0) && (k %% 3 == 0))%N || ((i %% 3 == 1) && (k %% 3 == 1))%N ->
  False.
Proof.
move=> uK vK wK eu ev ew ij jk hj hik.
have vz : A1 v = 0 := rep_Z ev hj.
have neq_v (t : backedge (qk m')) : (0 < val (A1 t))%N -> A1 t != A1 v.
  move=> pos; rewrite vz; apply/eqP=> e.
  by move: pos; rewrite e.
case/orP: hik => /andP[/eqP hi /eqP hk].
- (* Hi mirror *)
  have hu := rep_Hi eu hi.
  have hw := rep_Hi ew hk.
  have hu0 : (0 < val (A1 u))%N := leq_ltn_trans (leq0n m) hu.
  have hw0 : (0 < val (A1 w))%N := leq_ltn_trans (leq0n m) hw.
  have hmem1 := beatc uK vK eu ev ij (neq_v u hu0).
  rewrite vz subr0 in hmem1.
  have vu1 : val (A1 u) = m.+1.
    by apply/eqP; rewrite -(AC_mem_Hi hu).
  have vDw : A1 v != A1 w by rewrite eq_sym (neq_v w hw0).
  have hmem2 := beatc vK wK ev ew jk vDw.
  rewrite vz sub0r in hmem2.
  have vw : (m.+2 <= val (A1 w))%N.
    by rewrite -(AC_mem_Hi_opp hw).
  have uDw : A1 u != A1 w.
    apply/eqP=> e; move: vw.
    by rewrite -e vu1 ltnn.
  have hmem3 := beatc uK wK eu ew (ltn_trans ij jk) uDw.
  have ulw : (val (A1 u) < val (A1 w))%N.
    by rewrite vu1; exact: vw.
  have gap : (val (A1 w) - val (A1 u) < m)%N.
    rewrite vu1 ltn_subLR; last exact: leq_trans (leqnSn m.+1) vw.
    by rewrite -nat_n_split ltn_ord.
  by move: hmem3; rewrite (AC_wrapF ulw gap).
- (* Lo mirror *)
  have hu := rep_Lo eu hi.
  have hw := rep_Lo ew hk.
  case/andP: (hu) => hup hul; case/andP: (hw) => hwp hwl.
  have hmem1 := beatc uK vK eu ev ij (neq_v u hup).
  rewrite vz subr0 in hmem1.
  have vum : (val (A1 u) < m)%N.
    by rewrite -(AC_mem_Lo hu).
  have vDw : A1 v != A1 w by rewrite eq_sym (neq_v w hwp).
  have hmem2 := beatc vK wK ev ew jk vDw.
  rewrite vz sub0r in hmem2.
  have vwm : val (A1 w) = m.
    by apply/eqP; rewrite -(AC_mem_Lo_opp hw).
  have uDw : A1 u != A1 w.
    apply/eqP=> e; move: vum.
    by rewrite e vwm ltnn.
  have hmem3 := beatc uK wK eu ew (ltn_trans ij jk) uDw.
  have ulw : (val (A1 u) < val (A1 w))%N by rewrite vwm.
  have gap : (val (A1 w) - val (A1 u) < m)%N.
    by rewrite vwm ltn_subrL hup.
  by move: hmem3; rewrite (AC_wrapF ulw gap).
Qed.

(* (zero, X, zero) triples — paper sets 9–10 *)
Lemma triple_B (u v w : backedge (qk m')) (i j k : nat) :
  u \in K -> v \in K -> w \in K ->
  cidx (u : T5) = i -> cidx (v : T5) = j -> cidx (w : T5) = k ->
  (i < j)%N -> (j < k)%N ->
  (i %% 3)%N = 2%N -> (k %% 3)%N = 2%N -> (j %% 3 != 2)%N ->
  False.
Proof.
move=> uK vK wK eu ev ew ij jk hi hk hj.
have uz : A1 u = 0 := rep_Z eu hi.
have wz : A1 w = 0 := rep_Z ew hk.
have band0 : band (0 : 'Z_n) = 3 by [].
have vDz : A1 v != 0.
  apply/eqP=> e.
  have := repA_band ev; rewrite e band0 => -[e2].
  by move/eqP: hj; rewrite -e2.
have uDv : A1 u != A1 v by rewrite uz eq_sym.
have hmem1 := beatc uK vK eu ev ij uDv.
rewrite uz sub0r in hmem1.
have vDw : A1 v != A1 w by rewrite wz.
have hmem2 := beatc vK wK ev ew jk vDw.
rewrite wz subr0 in hmem2.
exact: (oppA_disjoint hmem2 hmem1).
Qed.

(* quad 11: pattern (Hi, Lo, Hi, zero) *)
Lemma quad_A (p q r s : backedge (qk m')) (i1 i2 i3 i4 : nat) :
  p \in K -> q \in K -> r \in K -> s \in K ->
  cidx (p : T5) = i1 -> cidx (q : T5) = i2 ->
  cidx (r : T5) = i3 -> cidx (s : T5) = i4 ->
  (i1 < i2)%N -> (i2 < i3)%N -> (i3 < i4)%N ->
  (i1 %% 3)%N = 0%N -> (i2 %% 3)%N = 1%N ->
  (i3 %% 3)%N = 0%N -> (i4 %% 3)%N = 2%N -> False.
Proof.
move=> pK qK rK sK e1 e2 e3 e4 i12 i23 i34 h1 h2 h3 h4.
have sz : A1 s = 0 := rep_Z e4 h4.
have hp := rep_Hi e1 h1.
have hr := rep_Hi e3 h3.
have neq_s (t : backedge (qk m')) : (0 < val (A1 t))%N -> A1 t != A1 s.
  by move=> pos; rewrite sz; apply/eqP=> e; move: pos; rewrite e.
have hp0 : (0 < val (A1 p))%N := leq_ltn_trans (leq0n m) hp.
have hr0 : (0 < val (A1 r))%N := leq_ltn_trans (leq0n m) hr.
have hmemp := beatc pK sK e1 e4 (ltn_trans i12 (ltn_trans i23 i34)) (neq_s p hp0).
rewrite sz subr0 in hmemp.
have hmemr := beatc rK sK e3 e4 i34 (neq_s r hr0).
rewrite sz subr0 in hmemr.
have vp1 : val (A1 p) = m.+1 by apply/eqP; rewrite -(AC_mem_Hi hp).
have vr1 : val (A1 r) = m.+1 by apply/eqP; rewrite -(AC_mem_Hi hr).
have epr : A1 p = A1 r by apply: val_inj; rewrite /= vp1 vr1.
have pDq : A1 p != A1 q.
  by apply: bands_neq e1 e2 _; rewrite h1 h2.
have qDr : A1 q != A1 r.
  by apply: bands_neq e2 e3 _; rewrite h2 h3.
have hB1 := beatc pK qK e1 e2 i12 pDq.
have hB2 := beatc qK rK e2 e3 i23 qDr.
rewrite -epr in hB2.
exact: (opp_arcs_contra hB1 hB2).
Qed.

(* quad 12: pattern (Lo, Hi, Lo, zero) *)
Lemma quad_B (p q r s : backedge (qk m')) (i1 i2 i3 i4 : nat) :
  p \in K -> q \in K -> r \in K -> s \in K ->
  cidx (p : T5) = i1 -> cidx (q : T5) = i2 ->
  cidx (r : T5) = i3 -> cidx (s : T5) = i4 ->
  (i1 < i2)%N -> (i2 < i3)%N -> (i3 < i4)%N ->
  (i1 %% 3)%N = 1%N -> (i2 %% 3)%N = 0%N ->
  (i3 %% 3)%N = 1%N -> (i4 %% 3)%N = 2%N -> False.
Proof.
move=> pK qK rK sK e1 e2 e3 e4 i12 i23 i34 h1 h2 h3 h4.
have sz : A1 s = 0 := rep_Z e4 h4.
have hp := rep_Lo e1 h1.
have hq := rep_Hi e2 h2.
have hr := rep_Lo e3 h3.
case/andP: (hp) => hp0 _.
case/andP: (hr) => hr0 hrle.
have neq_s (t : backedge (qk m')) : (0 < val (A1 t))%N -> A1 t != A1 s.
  by move=> pos; rewrite sz; apply/eqP=> e; move: pos; rewrite e.
have hq0 : (0 < val (A1 q))%N := leq_ltn_trans (leq0n m) hq.
have hmemq := beatc qK sK e2 e4 (ltn_trans i23 i34) (neq_s q hq0).
rewrite sz subr0 in hmemq.
have vq1 : val (A1 q) = m.+1 by apply/eqP; rewrite -(AC_mem_Hi hq).
have pDq : A1 p != A1 q.
  by apply: bands_neq e1 e2 _; rewrite h1 h2.
have hB1 := beatc pK qK e1 e2 i12 pDq.
have vp1 : val (A1 p) = 1%N.
  by apply/eqP; rewrite -(mem_sub_Lo_Hi1 hp vq1).
have qDr : A1 q != A1 r.
  by apply: bands_neq e2 e3 _; rewrite h2 h3.
have hB2 := beatc qK rK e2 e3 i23 qDr.
have vr2 : (2 <= val (A1 r))%N.
  by rewrite -(mem_sub_Hi1_Lo vq1 hr).
have pDr : A1 p != A1 r.
  by apply/eqP=> e; move: vr2; rewrite -e vp1.
have hB3 := beatc pK rK e1 e3 (ltn_trans i12 i23) pDr.
have plr : (val (A1 p) < val (A1 r))%N by rewrite vp1.
have gap : (val (A1 r) - val (A1 p) < m)%N.
  by rewrite vp1 ltn_subLR ?hr0 //; exact: hrle.
by move: hB3; rewrite (AC_wrapF plr gap).
Qed.

(* quad 13: pattern (zero, Hi, Lo, Hi) *)
Lemma quad_C (p q r s : backedge (qk m')) (i1 i2 i3 i4 : nat) :
  p \in K -> q \in K -> r \in K -> s \in K ->
  cidx (p : T5) = i1 -> cidx (q : T5) = i2 ->
  cidx (r : T5) = i3 -> cidx (s : T5) = i4 ->
  (i1 < i2)%N -> (i2 < i3)%N -> (i3 < i4)%N ->
  (i1 %% 3)%N = 2%N -> (i2 %% 3)%N = 0%N ->
  (i3 %% 3)%N = 1%N -> (i4 %% 3)%N = 0%N -> False.
Proof.
move=> pK qK rK sK e1 e2 e3 e4 i12 i23 i34 h1 h2 h3 h4.
have pz : A1 p = 0 := rep_Z e1 h1.
have hq := rep_Hi e2 h2.
have hr := rep_Lo e3 h3.
have hs := rep_Hi e4 h4.
case/andP: (hr) => hr0 hrle.
have neq_p (t : backedge (qk m')) : (0 < val (A1 t))%N -> A1 p != A1 t.
  by move=> pos; rewrite pz eq_sym; apply/eqP=> e; move: pos; rewrite e.
have hq0 : (0 < val (A1 q))%N := leq_ltn_trans (leq0n m) hq.
have hs0 : (0 < val (A1 s))%N := leq_ltn_trans (leq0n m) hs.
have hmq := beatc pK qK e1 e2 i12 (neq_p q hq0).
rewrite pz sub0r in hmq.
have hmr := beatc pK rK e1 e3 (ltn_trans i12 i23) (neq_p r hr0).
rewrite pz sub0r in hmr.
have hms := beatc pK sK e1 e4 (ltn_trans (ltn_trans i12 i23) i34) (neq_p s hs0).
rewrite pz sub0r in hms.
have vq2 : (m.+2 <= val (A1 q))%N by rewrite -(AC_mem_Hi_opp hq).
have vrm : val (A1 r) = m by apply/eqP; rewrite -(AC_mem_Lo_opp hr).
have vs2 : (m.+2 <= val (A1 s))%N by rewrite -(AC_mem_Hi_opp hs).
have qDr : A1 q != A1 r.
  by apply: bands_neq e2 e3 _; rewrite h2 h3.
have hB1 := beatc qK rK e2 e3 i23 qDr.
have hqgt : (m < val (A1 q))%N := leq_trans (leqnSn m.+1) vq2.
have vqlt : (val (A1 q) < m.*2)%N.
  by rewrite -(mem_sub_Hi_m hqgt vrm).
have rDs : A1 r != A1 s.
  apply/eqP=> e; move: vs2.
  by rewrite -e vrm leqNgt (ltn_trans (ltnSn m) (ltnSn m.+1)).
have hB2 := beatc rK sK e3 e4 i34 rDs.
have hsgt : (m < val (A1 s))%N := leq_trans (leqnSn m.+1) vs2.
have vs2m : val (A1 s) = m.*2.
  by apply/eqP; rewrite -(mem_sub_m_Hi hsgt vrm).
have qDs : A1 q != A1 s.
  by apply/eqP=> e; move: vqlt; rewrite e vs2m ltnn.
have hB3 := beatc qK sK e2 e4 (ltn_trans i23 i34) qDs.
have qls : (val (A1 q) < val (A1 s))%N by rewrite vs2m.
have gap : (val (A1 s) - val (A1 q) < m)%N.
  rewrite vs2m ltn_subLR; last exact: ltnW vqlt.
  exact: (dbl_lt_addr hqgt).
by move: hB3; rewrite (AC_wrapF qls gap).
Qed.

(* quad 14: pattern (zero, Lo, Hi, Lo) *)
Lemma quad_D (p q r s : backedge (qk m')) (i1 i2 i3 i4 : nat) :
  p \in K -> q \in K -> r \in K -> s \in K ->
  cidx (p : T5) = i1 -> cidx (q : T5) = i2 ->
  cidx (r : T5) = i3 -> cidx (s : T5) = i4 ->
  (i1 < i2)%N -> (i2 < i3)%N -> (i3 < i4)%N ->
  (i1 %% 3)%N = 2%N -> (i2 %% 3)%N = 1%N ->
  (i3 %% 3)%N = 0%N -> (i4 %% 3)%N = 1%N -> False.
Proof.
move=> pK qK rK sK e1 e2 e3 e4 i12 i23 i34 h1 h2 h3 h4.
have pz : A1 p = 0 := rep_Z e1 h1.
have hq := rep_Lo e2 h2.
have hr := rep_Hi e3 h3.
have hs := rep_Lo e4 h4.
case/andP: (hq) => hq0 _; case/andP: (hs) => hs0 _.
have hr0 : (0 < val (A1 r))%N := leq_ltn_trans (leq0n m) hr.
have neq_p (t : backedge (qk m')) : (0 < val (A1 t))%N -> A1 p != A1 t.
  by move=> pos; rewrite pz eq_sym; apply/eqP=> e; move: pos; rewrite e.
have hmq := beatc pK qK e1 e2 i12 (neq_p q hq0).
rewrite pz sub0r in hmq.
have hmr := beatc pK rK e1 e3 (ltn_trans i12 i23) (neq_p r hr0).
rewrite pz sub0r in hmr.
have hms := beatc pK sK e1 e4 (ltn_trans (ltn_trans i12 i23) i34) (neq_p s hs0).
rewrite pz sub0r in hms.
have vqm : val (A1 q) = m by apply/eqP; rewrite -(AC_mem_Lo_opp hq).
have vsm : val (A1 s) = m by apply/eqP; rewrite -(AC_mem_Lo_opp hs).
have qDr : A1 q != A1 r.
  by apply: bands_neq e2 e3 _; rewrite h2 h3.
have hB1 := beatc qK rK e2 e3 i23 qDr.
have vr2m : val (A1 r) = m.*2.
  by apply/eqP; rewrite -(mem_sub_m_Hi hr vqm).
have rDs : A1 r != A1 s.
  by apply: bands_neq e3 e4 _; rewrite h3 h4.
have hB2 := beatc rK sK e3 e4 i34 rDs.
move: hB2; rewrite (mem_sub_Hi_m hr vsm).
by rewrite vr2m ltnn.
Qed.

(* squares 15–20: outer bands alternate *)
Lemma square (p q r s : backedge (qk m')) (i1 i2 i3 i4 : nat) :
  p \in K -> q \in K -> r \in K -> s \in K ->
  cidx (p : T5) = i1 -> cidx (q : T5) = i2 ->
  cidx (r : T5) = i3 -> cidx (s : T5) = i4 ->
  (i1 < i2)%N -> (i2 < i3)%N -> (i3 < i4)%N ->
  ((i1 %% 3 == 0) && (i2 %% 3 == 1) && (i3 %% 3 == 0) && (i4 %% 3 == 1))%N
  || ((i1 %% 3 == 1) && (i2 %% 3 == 0) && (i3 %% 3 == 1) && (i4 %% 3 == 0))%N ->
  False.
Proof.
move=> pK qK rK sK e1 e2 e3 e4 i12 i23 i34 pat.
have pDq : A1 p != A1 q.
  apply: bands_neq e1 e2 _.
  by case/orP: pat => /andP[/andP[/andP[/eqP-> /eqP->] _] _].
have qDr : A1 q != A1 r.
  apply: bands_neq e2 e3 _.
  by case/orP: pat => /andP[/andP[/andP[_ /eqP->] /eqP->] _].
have rDs : A1 r != A1 s.
  apply: bands_neq e3 e4 _.
  by case/orP: pat => /andP[/andP[_ /eqP->] /eqP->].
have pDs : A1 p != A1 s.
  apply: bands_neq e1 e4 _.
  by case/orP: pat => /andP[/andP[/andP[/eqP-> _] _] /eqP->].
case: (eqVneq (A1 p) (A1 r)) => [epr|pDr].
- have hB1 := beatc pK qK e1 e2 i12 pDq.
  have hB2 := beatc qK rK e2 e3 i23 qDr.
  rewrite -epr in hB2.
  exact: (opp_arcs_contra hB1 hB2).
case: (eqVneq (A1 q) (A1 s)) => [eqs|qDs].
- have hB2 := beatc qK rK e2 e3 i23 qDr.
  have hB3 := beatc rK sK e3 e4 i34 rDs.
  rewrite -eqs in hB3.
  exact: (opp_arcs_contra hB2 hB3).
have C1 := beatc pK rK e1 e3 (ltn_trans i12 i23) pDr.
have C2 := beatc qK rK e2 e3 i23 qDr.
have C3 := beatc pK sK e1 e4 (ltn_trans (ltn_trans i12 i23) i34) pDs.
have C4 := beatc qK sK e2 e4 (ltn_trans i23 i34) qDs.
case/orP: pat => /andP[/andP[/andP[/eqP h1 /eqP h2] /eqP h3] /eqP h4].
- exact: (H17_no_mixed (rep_Hi e1 h1) (rep_Lo e2 h2)
            (rep_Hi e3 h3) (rep_Lo e4 h4) C1 C2 C3 C4).
- exact: (H17_no_mixed (rep_Hi e2 h2) (rep_Lo e1 h1)
            (rep_Hi e4 h4) (rep_Lo e3 h3) C4 C3 C2 C1).
Qed.

(** ** Packaging: the occupancy bits never match an obstruction *)

Lemma occ_and3F (i j k : nat) :
  (forall u v w : backedge (qk m'), u \in K -> v \in K -> w \in K ->
     cidx (u : T5) = i -> cidx (v : T5) = j -> cidx (w : T5) = k -> False) ->
  occ K i && occ K j && occ K k = false.
Proof.
move=> h; apply/negbTE/negP.
case/andP=> /andP[/occP[u uK eu] /occP[v vK ev]] /occP[w wK ew].
exact: (h u v w uK vK wK eu ev ew).
Qed.

Lemma occ_and4F (i j k l : nat) :
  (forall p q r s : backedge (qk m'), p \in K -> q \in K -> r \in K -> s \in K ->
     cidx (p : T5) = i -> cidx (q : T5) = j ->
     cidx (r : T5) = k -> cidx (s : T5) = l -> False) ->
  occ K i && occ K j && occ K k && occ K l = false.
Proof.
move=> h; apply/negbTE/negP.
case/andP=> /andP[/andP[/occP[p pK ep] /occP[q qK eq2]] /occP[r rK er]]
            /occP[s sK es].
exact: (h p q r s pK qK rK sK ep eq2 er es).
Qed.

Lemma no_obstruction :
  obstrb (occ K 0) (occ K 1) (occ K 2) (occ K 3)
         (occ K 4) (occ K 5) (occ K 6) (occ K 7) = false.
Proof.
rewrite /obstrb.
rewrite (occ_and3F (i:=0) (j:=2) (k:=3)
  (fun u v w uK vK wK eu ev ew =>
     triple_A uK vK wK eu ev ew isT isT (erefl _) isT)).
rewrite (occ_and3F (i:=1) (j:=2) (k:=4)
  (fun u v w uK vK wK eu ev ew =>
     triple_A uK vK wK eu ev ew isT isT (erefl _) isT)).
rewrite (occ_and3F (i:=0) (j:=2) (k:=6)
  (fun u v w uK vK wK eu ev ew =>
     triple_A uK vK wK eu ev ew isT isT (erefl _) isT)).
rewrite (occ_and3F (i:=1) (j:=2) (k:=7)
  (fun u v w uK vK wK eu ev ew =>
     triple_A uK vK wK eu ev ew isT isT (erefl _) isT)).
rewrite (occ_and3F (i:=0) (j:=5) (k:=6)
  (fun u v w uK vK wK eu ev ew =>
     triple_A uK vK wK eu ev ew isT isT (erefl _) isT)).
rewrite (occ_and3F (i:=1) (j:=5) (k:=7)
  (fun u v w uK vK wK eu ev ew =>
     triple_A uK vK wK eu ev ew isT isT (erefl _) isT)).
rewrite (occ_and3F (i:=3) (j:=5) (k:=6)
  (fun u v w uK vK wK eu ev ew =>
     triple_A uK vK wK eu ev ew isT isT (erefl _) isT)).
rewrite (occ_and3F (i:=4) (j:=5) (k:=7)
  (fun u v w uK vK wK eu ev ew =>
     triple_A uK vK wK eu ev ew isT isT (erefl _) isT)).
rewrite (occ_and3F (i:=2) (j:=3) (k:=5)
  (fun u v w uK vK wK eu ev ew =>
     triple_B uK vK wK eu ev ew isT isT (erefl _) (erefl _) isT)).
rewrite (occ_and3F (i:=2) (j:=4) (k:=5)
  (fun u v w uK vK wK eu ev ew =>
     triple_B uK vK wK eu ev ew isT isT (erefl _) (erefl _) isT)).
rewrite (occ_and4F (i:=0) (j:=1) (k:=3) (l:=5)
  (fun p q r s pK qK rK sK e1 e2 e3 e4 =>
     quad_A pK qK rK sK e1 e2 e3 e4 isT isT isT
       (erefl _) (erefl _) (erefl _) (erefl _))).
rewrite (occ_and4F (i:=1) (j:=3) (k:=4) (l:=5)
  (fun p q r s pK qK rK sK e1 e2 e3 e4 =>
     quad_B pK qK rK sK e1 e2 e3 e4 isT isT isT
       (erefl _) (erefl _) (erefl _) (erefl _))).
rewrite (occ_and4F (i:=2) (j:=3) (k:=4) (l:=6)
  (fun p q r s pK qK rK sK e1 e2 e3 e4 =>
     quad_C pK qK rK sK e1 e2 e3 e4 isT isT isT
       (erefl _) (erefl _) (erefl _) (erefl _))).
rewrite (occ_and4F (i:=2) (j:=4) (k:=6) (l:=7)
  (fun p q r s pK qK rK sK e1 e2 e3 e4 =>
     quad_D pK qK rK sK e1 e2 e3 e4 isT isT isT
       (erefl _) (erefl _) (erefl _) (erefl _))).
rewrite (occ_and4F (i:=0) (j:=1) (k:=3) (l:=4)
  (fun p q r s pK qK rK sK e1 e2 e3 e4 =>
     square pK qK rK sK e1 e2 e3 e4 isT isT isT isT)).
rewrite (occ_and4F (i:=0) (j:=1) (k:=3) (l:=7)
  (fun p q r s pK qK rK sK e1 e2 e3 e4 =>
     square pK qK rK sK e1 e2 e3 e4 isT isT isT isT)).
rewrite (occ_and4F (i:=0) (j:=1) (k:=6) (l:=7)
  (fun p q r s pK qK rK sK e1 e2 e3 e4 =>
     square pK qK rK sK e1 e2 e3 e4 isT isT isT isT)).
rewrite (occ_and4F (i:=0) (j:=4) (k:=6) (l:=7)
  (fun p q r s pK qK rK sK e1 e2 e3 e4 =>
     square pK qK rK sK e1 e2 e3 e4 isT isT isT isT)).
rewrite (occ_and4F (i:=1) (j:=3) (k:=4) (l:=6)
  (fun p q r s pK qK rK sK e1 e2 e3 e4 =>
     square pK qK rK sK e1 e2 e3 e4 isT isT isT isT)).
rewrite (occ_and4F (i:=3) (j:=4) (k:=6) (l:=7)
  (fun p q r s pK qK rK sK e1 e2 e3 e4 =>
     square pK qK rK sK e1 e2 e3 e4 isT isT isT isT)).
by [].
Qed.

End WithClique.

End Obstructions.