(** * Digraph.acn_arc_facts — value arithmetic and arc-facts for ACₙ

    The computation kit for the k=5 application (paper Lemma "Arc-facts",
    arXiv-style labels (i)–(iii)): values of differences in 'Z_n, membership
    of the ACₙ connection set by value, and the gap characterizations of
    forward/backward arcs under the value (identity) order. Everything is
    parametric in m (n = 2m+1, m = m'.+1 ≥ 1; the hypotheses m ≥ 3 only
    appear downstream where genuinely needed).

    Conventions: [val] is the canonical value in [0, 2m]; for
    [val i < val j] the *gap* is [d = val j - val i ∈ [1, 2m]]. Then
    - [AC_arc_lt]:  i → j  iff  d < m or d = m+1   (forward arcs);
    - [AC_arc_gt]:  j → i  iff  d = m or d ≥ m+2   (backward arcs);
    - bands: Hi = vals [m+1, 2m], Lo = vals [1, m]; [AC_mem_Hi(_opp)] and
      [AC_mem_Lo(_opp)] are the paper's (i) and (ii); [AC_band_arc] is the
      within-band consequence of (iii): inside a band, arcs follow the value
      order. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_fingroup all_algebra.
From Digraph Require Import prelude interop_graph_theory digraph tournament order.
From Digraph Require Import omegabar critical domination.
From Digraph Require Import automorphism cayley circulant transitive.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Set SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.

Section ArcFacts.
Variable m' : nat.
Local Notation m := m'.+1.
Local Notation n := (m.*2.+1).
Local Notation ACm := (AC m').

(** ** Values of sums, opposites, differences in 'Z_n *)

Lemma val_addE (i j : 'Z_n) : val (i + j) = ((val i + val j) %% n)%N.
Proof. by []. Qed.

Lemma val_oppE (z : 'Z_n) : val (- z) = ((n - val z) %% n)%N.
Proof. by []. Qed.

Lemma val_sub_le (i j : 'Z_n) : (val i <= val j)%N ->
  val (j - i) = (val j - val i)%N.
Proof.
move=> le_ij.
case: (posnP (val i)) => [i0|ipos].
- have -> : i = 0 by apply: val_inj; rewrite i0.
  by rewrite subr0 subn0.
- rewrite val_addE val_oppE /=.
  have -> : ((n - val i) %% n)%N = (n - val i)%N.
    by rewrite modn_small // ltn_subrL ipos.
  rewrite addnC addnBAC ?(ltnW (ltn_ord i)) // -addnBA // modnDl modn_small //.
  by rewrite (leq_ltn_trans (leq_subr _ _)) // ltn_ord.
Qed.

Lemma val_sub_gt (i j : 'Z_n) : (val j < val i)%N ->
  val (j - i) = (n - (val i - val j))%N.
Proof.
move=> lt_ji.
have -> : j - i = - (i - j) by rewrite opprB.
rewrite val_oppE (val_sub_le (ltnW lt_ji)) modn_small //.
by rewrite ltn_subrL subn_gt0 lt_ji.
Qed.

(** ** Connection-set membership by value *)

Lemma AC_mem_val (z : 'Z_n) :
  (z \in ACset m') = ((0 < val z < m)%N || (val z == m.+1)%N).
Proof. by rewrite inE. Qed.

(** ** Gap characterizations under the value order *)

Lemma AC_arc_lt (i j : ACm) : (val i < val j)%N ->
  (i --> j) = ((val j - val i < m)%N || (val j - val i == m.+1)%N).
Proof.
move=> lt; rewrite AC_arcE AC_mem_val (val_sub_le (ltnW lt)).
by rewrite subn_gt0 lt.
Qed.

Lemma AC_arc_gt (i j : ACm) : (val i < val j)%N ->
  (j --> i) = ((val j - val i == m)%N || (m.+2 <= val j - val i)%N).
Proof.
move=> lt; rewrite AC_arcE AC_mem_val (val_sub_gt lt).
set d := (val j - val i)%N.
have dpos : (0 < d)%N by rewrite subn_gt0.
have dle : (d <= m.*2)%N.
  by rewrite (leq_trans (leq_subr _ _)) // -ltnS ltn_ord.
have n_d_pos : (0 < n - d)%N by rewrite subn_gt0 ltnS dle.
rewrite n_d_pos /=.
have -> : (n - d < m)%N = (m.+2 <= d)%N.
  by rewrite ltn_subLR ?(leqW dle) // -addnn addnC -addnS ltn_add2l.
have -> : ((n - d)%N == m.+1) = (d == m).
  rewrite -(eqn_add2r d) subnK ?(leqW dle) //.
  by rewrite -addnn -addSn eqn_add2l eq_sym.
by rewrite orbC.
Qed.

(** Within a band (gap < m), arcs follow the value order — the working form
    of paper (iii). *)
Lemma AC_band_arc (u v : ACm) :
  (val u < val v)%N -> (val v - val u < m)%N -> (u --> v).
Proof. by move=> lt small; rewrite AC_arc_lt // small. Qed.

(** ** The band facts — paper (i) and (ii) *)

Lemma AC_mem_Hi (a : 'Z_n) : (m.+1 <= val a)%N ->
  (a \in ACset m') = (val a == m.+1).
Proof.
move=> hi; rewrite AC_mem_val.
by rewrite (leq_gtF (ltnW hi)) andbF.
Qed.

Lemma AC_mem_Hi_opp (a : 'Z_n) : (m.+1 <= val a)%N ->
  (- a \in ACset m') = (m.+2 <= val a)%N.
Proof.
move=> hi; rewrite AC_mem_val val_oppE /= modn_small; last first.
  by rewrite ltn_subrL (leq_ltn_trans (leq0n m) hi).
have alt : (val a < n)%N := ltn_ord a.
have -> : (((n - val a)%N == m.+1)) = (val a == m).
  rewrite -(eqn_add2r (val a)) subnK ?(ltnW alt) //.
  move: (val a) => v.
  have -> : n = (m.+1 + m)%N by rewrite addSn addnn.
  by rewrite eqn_add2l eq_sym.
have -> : (val a == m) = false by rewrite (gtn_eqF hi).
have -> : (0 < n - val a)%N = true by rewrite subn_gt0 alt.
have -> : (n - val a < m)%N = (m.+2 <= val a)%N.
  rewrite ltn_subLR ?(ltnW alt) //.
  move: (val a) => v.
  have -> : n = (m.+1 + m)%N by rewrite addSn addnn.
  by rewrite ltn_add2r.
by rewrite orbF.
Qed.

Lemma AC_mem_Lo (a : 'Z_n) : (0 < val a <= m)%N ->
  (a \in ACset m') = (val a < m)%N.
Proof.
case/andP=> apos ale; rewrite AC_mem_val apos /=.
case: (ltngtP (val a) m) => [lt|gt|e] //=.
- by move: (leq_ltn_trans ale gt); rewrite ltnn.
- by rewrite e (ltn_eqF (ltnSn m)).
Qed.

Lemma AC_mem_Lo_opp (a : 'Z_n) : (0 < val a <= m)%N ->
  (- a \in ACset m') = (val a == m).
Proof.
case/andP=> apos ale; rewrite AC_mem_val val_oppE /= modn_small; last first.
  by rewrite ltn_subrL apos.
have alt : (val a < n)%N := ltn_ord a.
have -> : ((n - val a)%N == m.+1) = (val a == m).
  rewrite -(eqn_add2r (val a)) subnK ?(ltnW alt) //.
  move: (val a) => v.
  have -> : n = (m.+1 + m)%N by rewrite addSn addnn.
  by rewrite eqn_add2l eq_sym.
have -> : (n - val a < m)%N = false.
  apply/negbTE; rewrite -leqNgt.
  rewrite leq_subRL ?(ltnW alt) //.
  move: (val a) ale => v vle.
  have -> : n = (m + m.+1)%N by rewrite addnS addnn.
  by rewrite addnC leq_add2l (leq_trans vle (leqnSn m)).
by rewrite andbF.
Qed.

End ArcFacts.
