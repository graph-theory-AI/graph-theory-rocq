(** * Shared cycle/path tools for the small Cheng--Keevash cases. *)

From HB Require Import structures.
From mathcomp Require Import all_boot.
From Digraph Require Import prelude digraph oriented dipath.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section CKPathCycleTools.
Variable D : diGraphType.
Implicit Types (x y z u v q : D) (c s : seq D) (A : {set D}).

Lemma dicycle_set_card c :
  dicycle c -> #|[set z in c]| = size c.
Proof.
move=> /and3P[_ _ uc].
have hc : #|c| = size c by exact/card_uniqP.
rewrite -hc.
apply: eq_card => z.
by rewrite inE.
Qed.

Lemma outdeg_split_set A v :
  outdeg v = outdeg_in A v + outdeg_in (~: A) v.
Proof.
rewrite -outdeg_inT !outdeg_in_sumE.
rewrite (bigID (mem A)) /=.
congr (_ + _); apply: eq_bigl => w; by rewrite !inE.
Qed.

(** A path whose first hit of [A] is at least two arcs after its start has
    two consecutive vertices outside [A] immediately before that hit. *)
Lemma path_first_entry_two_outside x s A :
  path arc x s -> x \notin A -> last x s \in A ->
  (forall z, x --> z -> z \notin A) ->
  exists u v z, [&& u \notin A, v \notin A, z \in A,
                    u --> v & v --> z].
Proof.
move=> ps xNA lastA xout.
case: s ps lastA => [|y t] ps lastA.
  by move: lastA; rewrite /= (negbTE xNA).
move: ps => /= /andP[axy pyt].
have yNA : y \notin A by exact: xout y axy.
have aux : forall t (u v : D),
    u \notin A -> v \notin A -> u --> v -> path arc v t ->
    last v t \in A ->
    exists u0 v0 z, [&& u0 \notin A, v0 \notin A, z \in A,
                         u0 --> v0 & v0 --> z].
  elim=> [|z r IH] u v uNA vNA auv /=.
    by move=> _ vA; move: vA; rewrite (negbTE vNA).
  move=> /andP[avz pzr] zrA.
  case zA: (z \in A).
    by exists u, v, z; rewrite uNA vNA zA auv avz.
  apply: (IH v z vNA _ avz pzr zrA).
  by rewrite zA.
apply: (aux t x y xNA yNA axy pyt).
by move: lastA; rewrite /=.
Qed.

(** Two vertices before a directed cycle already make a path one arc
    longer than the cycle. *)
Lemma two_outside_cycle_ell c x y z :
  dicycle c -> z \in c -> x \notin c -> y \notin c -> x != y ->
  x --> y -> y --> z -> size c + 1 <= ell D.
Proof.
move=> dc zc xNc yNc xDy axy ayz.
have cpos : 0 < size c.
  move: dc; rewrite /dicycle /nilp.
  by move=> /and3P[n0 _ _]; rewrite lt0n.
have [s [ps szs cov _ _]] := dicycle_unroll dc zc.
have xNzs : x \notin z :: s by rewrite cov xNc.
have yNzs : y \notin z :: s by rewrite cov yNc.
have pxy : dipath x (y :: z :: s).
  rewrite /dipath /= axy ayz (dipath_path ps).
  rewrite inE negb_or xDy xNzs yNzs.
  by have := dipath_uniq ps.
have := ell_max pxy.
by rewrite /= szs (prednK cpos) addn1.
Qed.

(** Prepending one outside vertex to a Hamilton path around a cycle. *)
Lemma proper_dicycle_ell c x z :
  dicycle c -> z \in c -> x \notin c -> x --> z -> size c <= ell D.
Proof.
move=> dc zc xNc axz.
have cpos : 0 < size c.
  move: dc; rewrite /dicycle /nilp.
  by move=> /and3P[n0 _ _]; rewrite lt0n.
have [s [ps szs cov _ _]] := dicycle_unroll dc zc.
have xNzs : x \notin z :: s by rewrite cov xNc.
have px : dipath x (z :: s).
  rewrite /dipath /= axz (dipath_path ps) xNzs.
  by have := dipath_uniq ps.
have := ell_max px.
by rewrite /= szs (prednK cpos).
Qed.

(** Subdivide the cycle arc [q --> next c q] by a fresh vertex [x]. *)
Lemma dicycle_subdivide c q x :
  dicycle c -> q \in c -> x \notin c -> q --> x -> x --> next c q ->
  exists c', [/\ dicycle c', size c' = (size c).+1,
                 x \in c' &
                 (forall z, (z \in c') = (z == x) || (z \in c))].
Proof.
move=> dc qc xNc aqx axp.
have uc : uniq c by case/and3P: dc.
set p := next c q.
have pc : p \in c by rewrite /p mem_next qc.
have [s [ps szs cov _ lastE]] := dicycle_unroll dc pc.
have lastq : last p s = q by rewrite lastE /p prev_next.
have xNps : x \notin p :: s by rewrite cov xNc.
have pr : dipath p (rcons s x).
  by rewrite dipath_rcons ps lastq aqx xNps.
exists (p :: rcons s x); split.
- apply: (dicycle_suffix pr (i := 0)); first by [].
  by rewrite /= last_rcons /p.
- have cpos : 0 < size c.
    move: dc; rewrite /dicycle /nilp.
    by move=> /and3P[n0 _ _]; rewrite lt0n.
  by rewrite /= size_rcons szs (prednK cpos).
- by rewrite inE mem_rcons inE eqxx !orbT.
- move=> z.
  rewrite inE mem_rcons inE -cov.
  rewrite inE.
  exact: orbCA _ _ _.
Qed.

(** A fresh entry vertex, followed by a once-subdivided cycle, gives a
    path one arc longer than the original cycle. *)
Lemma cycle_sandwich_ell c q x y z :
  dicycle c -> q \in c -> x \notin c -> y \notin c -> y != x ->
  q --> x -> x --> next c q -> z \in c -> y --> z ->
  (size c).+1 <= ell D.
Proof.
move=> dc qc xNc yNc yDx aqx axp zc ayz.
have [c' [dc' szc' _ memE]] := dicycle_subdivide dc qc xNc aqx axp.
have yNc' : y \notin c' by rewrite memE (negbTE yDx) yNc.
have zc' : z \in c' by rewrite memE zc orbT.
have h := proper_dicycle_ell dc' zc' yNc' ayz.
by rewrite szc' in h.
Qed.

(** A nonempty subset of one directed cycle that is closed under the
    cycle successor is the whole cycle. *)
Lemma next_closed_dicycle c A :
  dicycle c -> A != set0 -> A \subset [set z in c] ->
  (forall z, z \in A -> next c z \in A) -> A = [set z in c].
Proof.
move=> dc An0 Asub closed.
have uc : uniq c by case/and3P: dc.
move/set0Pn: An0 => [x xA].
have xC : x \in c.
  have := subsetP Asub x xA.
  by rewrite inE.
have fc : fcycle (next c) c := cycle_next uc.
have orbitE_x : orbit (next c) x = rot (index x c) c :=
  orbitE fc uc xC.
have iterA n : iter n (next c) x \in A.
  elim: n => [|n IH] //=.
  exact: closed _ IH.
apply/setP=> z; apply/idP/idP.
- move=> zA.
  have := subsetP Asub z zA.
  by rewrite inE.
- move=> zC.
  have zorb : z \in orbit (next c) x.
    rewrite orbitE_x mem_rot.
    by move: zC; rewrite inE.
  case/trajectP: zorb => i _ ->.
  exact: iterA.
Qed.

(** Splice distinct outside endpoints around an arbitrary Hamilton
    ordering.  This is the reusable core of the active-gateway argument. *)
Lemma hamilton_splice_ell x s q u v :
  dipath x s -> last x s = q -> u \notin x :: s -> v \notin x :: s ->
  u != v -> q --> u -> v --> x -> (size s).+2 <= ell D.
Proof.
move=> ps lastq uNxs vNxs uDv aqu avx.
have pr : dipath x (rcons s u).
  by rewrite dipath_rcons ps lastq aqu uNxs.
have vDu : v != u by rewrite eq_sym.
have vNfull : v \notin x :: rcons s u.
  move: vNxs.
  by rewrite !inE mem_rcons !negb_or vDu => ->.
have pv : dipath v (x :: rcons s u).
  rewrite /dipath /= avx (dipath_path pr) vNfull.
  by have := dipath_uniq pr.
have := ell_max pv.
by rewrite /= size_rcons.
Qed.

(** If the active outside endpoint itself points to the start of the
    Hamilton ordering, it closes an enlarged cycle.  An entry from a
    second outside vertex then gives the same extremal contradiction. *)
Lemma hamilton_cycle_sandwich_ell x s q u v z :
  dipath x s -> last x s = q -> u \notin x :: s -> v \notin x :: s ->
  u != v -> q --> u -> u --> x -> z \in x :: s -> v --> z ->
  (size s).+2 <= ell D.
Proof.
move=> ps lastq uNxs vNxs uDv aqu aux zP avz.
have pr : dipath x (rcons s u).
  by rewrite dipath_rcons ps lastq aqu uNxs.
have dc' : dicycle (x :: rcons s u).
  apply: (dicycle_suffix pr (i := 0)); first by [].
  by rewrite /= last_rcons.
have vDu : v != u by rewrite eq_sym.
have vNc' : v \notin x :: rcons s u.
  move: vNxs.
  by rewrite !inE mem_rcons !negb_or vDu => ->.
have zc' : z \in x :: rcons s u.
  move: zP.
  rewrite !inE mem_rcons.
  move=> /orP[zx|zs]; apply/orP.
    left; exact: zx.
  right; by rewrite inE zs orbT.
have h := proper_dicycle_ell dc' zc' vNc' avz.
by rewrite /= size_rcons in h.
Qed.

Corollary hamilton_start_omitted x s q u v :
  dipath x s -> last x s = q -> u \notin x :: s -> v \notin x :: s ->
  u != v -> q --> u -> ell D < (size s).+2 -> v --> x = false.
Proof.
move=> ps lastq uNxs vNxs uDv aqu hell.
apply/negP=> avx.
have h := hamilton_splice_ell ps lastq uNxs vNxs uDv aqu avx.
by have := leq_ltn_trans h hell; rewrite ltnn.
Qed.

Corollary hamilton_active_start_omitted x s q u v z :
  dipath x s -> last x s = q -> u \notin x :: s -> v \notin x :: s ->
  u != v -> q --> u -> z \in x :: s -> v --> z ->
  ell D < (size s).+2 -> u --> x = false.
Proof.
move=> ps lastq uNxs vNxs uDv aqu zP avz hell.
apply/negP=> aux.
have h := hamilton_cycle_sandwich_ell
  ps lastq uNxs vNxs uDv aqu aux zP avz.
by have := leq_ltn_trans h hell; rewrite ltnn.
Qed.

End CKPathCycleTools.
