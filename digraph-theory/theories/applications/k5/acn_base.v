(** * Digraph.acn_base — the base facts about ACₙ (paper Prop. "Facts about ACₙ")

    For n = 2m+1, m ≥ 3:
    - [omegabar_AC]  : ω̄(ACₙ) = 3;
    - [omegabar_AC_del] : ω̄(ACₙ − v) = 2 for every v;
    - [AC_kcritical3] : ACₙ is 3-ω̄-critical.

    Upper bounds use the *value order* (realized as a permutation): under it
    every backedge spans a value-gap ≥ m ([backedge_qid_dist] via the
    arc-facts), so a clique embeds injectively into the ⌈(range)/m⌉ buckets
    ([bucket_bound]) — 3 buckets on [0,2m], 2 buckets on [1,2m] after
    deleting 0. The lower bound is the domination route (paper Property 3.2,
    [domnum_le_omegabar]): N₀ = {0} ∪ g has m+1 elements and the
    interval-autocorrelation lemma [autocorr2] gives
    |N₀ ∩ (N₀+t)| ≥ 2 for every t ≠ 0, so two translates of N₀ cover at most
    2(m+1) − 2 = 2m < n vertices and dom(ACₙ) ≥ 3. Criticality follows by
    vertex-transitivity ([vt_kcritical]) plus the directed triangle
    1 → 2 → m+3 → 1 surviving in ACₙ − 0. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_fingroup all_algebra.
From Digraph Require Import prelude interop_graph_theory digraph tournament order.
From Digraph Require Import omegabar critical domination.
From Digraph Require Import automorphism cayley circulant transitive.
From Digraph Require Import acn_arc_facts.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Set SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.

(** ** A pigeonhole principle: sparse values in a bounded range *)

Lemma bucket_bound (T' : finType) (K : {set T'}) (f : T' -> nat) (b w : nat) :
  (0 < w)%N ->
  (forall u, u \in K -> f u < b.+1 * w)%N ->
  ({in K &, forall u v, u != v -> (w <= f u - f v)%N || (w <= f v - f u)%N}) ->
  (#|K| <= b.+1)%N.
Proof.
move=> wpos fbound fdist.
pose g (u : T') : 'I_b.+1 := inord (f u %/ w).
have gE u : u \in K -> g u = (f u %/ w)%N :> nat.
  by move=> uK; rewrite /g inordK // ltn_divLR // fbound.
have bnd a c : (a %/ w = c %/ w)%N -> (a - c < w)%N.
  move=> eac; rewrite (divn_eq a w) (divn_eq c w) eac subnDl.
  by rewrite (leq_ltn_trans (leq_subr _ _)) // ltn_pmod.
have ginj : {in K &, injective g}.
  move=> u v uK vK e.
  have [//|uDv] := eqVneq u v.
  have e' : (f u %/ w = f v %/ w)%N by rewrite -(gE _ uK) -(gE _ vK) e.
  have := fdist _ _ uK vK uDv.
  case/orP=> h.
  - by have := leq_ltn_trans h (bnd _ _ e'); rewrite ltnn.
  - by have := leq_ltn_trans h (bnd _ _ (esym e')); rewrite ltnn.
rewrite -(card_in_imset ginj).
by rewrite (leq_trans (max_card _)) ?card_ord.
Qed.

Section ACBase.
Variable m' : nat.
Local Notation m := m'.+1.
Local Notation n := (m.*2.+1).
Local Notation ACm := (AC m').

(** ** The value order, realized *)

Let rid := [rel i j : ACm | (val i < val j)%N].
Fact rid_irr : irreflexive rid. Proof. by move=> i /=; rewrite ltnn. Qed.
Fact rid_trans : transitive rid. Proof. by move=> a b c /=; apply: ltn_trans. Qed.
Fact rid_total (i j : ACm) : i != j -> rid i j || rid j i.
Proof. by move=> iDj; rewrite /= -neq_ltn val_eqE. Qed.

Let qid : {perm ACm} := realize rid.
Let qidE := ltp_realizeE rid_irr rid_trans rid_total.

(** Every backedge of the value order spans a gap of at least m. *)
Lemma backedge_qid_dist (u v : ACm) :
  ((u : backedge qid) -- v) ->
  (m <= val u - val v)%N || (m <= val v - val u)%N.
Proof.
rewrite backedgeE !qidE /= => /orP[/andP[lt a]|/andP[lt a]].
- apply/orP; right.
  move: a; rewrite (AC_arc_gt lt) => /orP[/eqP->//|h].
  exact: leq_trans (ltnW (ltnSn m)) (ltnW h).
- apply/orP; left.
  move: a; rewrite (AC_arc_gt lt) => /orP[/eqP->//|h].
  exact: leq_trans (ltnW (ltnSn m)) (ltnW h).
Qed.

(** ** Upper bound: ω̄(ACₙ) ≤ 3 *)

Lemma omegab_at_qid_le3 : (omegab_at qid <= 3)%N.
Proof.
rewrite /omegab_at; case: omegaP => K Kmax.
have Kcl := maxclique_clique Kmax.
apply: (@bucket_bound _ K (fun u : ACm => val u) 2 m) => //.
- move=> u _.
  apply: (leq_trans (ltn_ord u)).
  by rewrite mulnSr addn3 -[(Zp_trunc n).+1]/(m'.*2.+2) !ltnS -mul2n leq_mul2r orbT.
- move=> u v uK vK uDv.
  exact/backedge_qid_dist/(Kcl _ _ uK vK uDv).
Qed.

Lemma omegabar_AC_le3 : (ω̄((AC m' : tournament)) <= 3)%N.
Proof. exact: leq_trans (omegabar_min qid) omegab_at_qid_le3. Qed.

(** ** Upper bound after deleting 0: ω̄(ACₙ − 0) ≤ 2 *)

Let z0 : ACm := (0 : 'Z_n).
Local Notation ACdel := (del_tournament z0).

Let r0 := [rel u v : ACdel | (val (val u) < val (val v))%N].
Fact r0_irr : irreflexive r0. Proof. by move=> u /=; rewrite ltnn. Qed.
Fact r0_trans : transitive r0. Proof. by move=> a b c /=; apply: ltn_trans. Qed.
Fact r0_total (u v : ACdel) : u != v -> r0 u v || r0 v u.
Proof. by move=> uDv; rewrite /= -neq_ltn !val_eqE. Qed.

Let q0 : {perm ACdel} := realize r0.
Let q0E := ltp_realizeE r0_irr r0_trans r0_total.

Lemma omegab_at_q0_le2 : (omegab_at q0 <= 2)%N.
Proof.
rewrite /omegab_at; case: omegaP => K Kmax.
have Kcl := maxclique_clique Kmax.
have vpos (w : ACdel) : (0 < val (val w))%N.
  by have := valP w; rewrite !inE lt0n -val_eqE.
have predn_sub (a c : nat) : (0 < a)%N -> (0 < c)%N -> (a.-1 - c.-1)%N = (a - c)%N.
  by case: a c => [|a] [|c] //; rewrite !succnK subSS.
apply: (@bucket_bound _ K (fun u : ACdel => (val (val u)).-1) 1 m) => //.
- move=> u _.
  by rewrite mul2n -ltnS (ltn_predK (vpos u)); exact: ltn_ord.
move=> u v uK vK uDv.
have := Kcl _ _ uK vK uDv.
rewrite backedgeE !q0E /= !sub_arcE => /orP[/andP[lt a]|/andP[lt a]].
- apply/orP; right.
  rewrite predn_sub ?vpos //.
  move: a; rewrite (AC_arc_gt lt) => /orP[/eqP->//|h].
  exact: leq_trans (ltnW (ltnSn m)) (ltnW h).
- apply/orP; left.
  rewrite predn_sub ?vpos //.
  move: a; rewrite (AC_arc_gt lt) => /orP[/eqP->//|h].
  exact: leq_trans (ltnW (ltnSn m)) (ltnW h).
Qed.

Lemma omegabar_ACdel_le2 : (ω̄(ACdel) <= 2)%N.
Proof. exact: leq_trans (omegabar_min q0) omegab_at_q0_le2. Qed.

(** ** The lower bound: dom(ACₙ) ≥ 3 via the autocorrelation of N₀ *)

Let A := ACset m'.
Let N0 : {set 'Z_n} := 0 |: A.

Fact mem0A : (0 : 'Z_n) \in A = false.
Proof. by rewrite AC_mem_val. Qed.

Fact oppA_disjoint (z : 'Z_n) : z \in A -> - z \in A -> False.
Proof.
move=> zA ozA.
have := ACset_cond z; rewrite zA ozA /=.
move/negbFE/eqP=> ze0.
by move: zA; rewrite ze0 mem0A.
Qed.

Fact cardA : #|A| = m.
Proof.
have copp : [set~ (0 : 'Z_n)] = A :|: [set - z | z in A].
  apply/setP=> z; rewrite !inE.
  have -> : (z \in [set - w | w in A]) = (- z \in A).
    apply/imsetP/idP => [[w wA ->]|ozA]; first by rewrite opprK.
    by exists (- z); rewrite ?opprK.
  rewrite (ACset_cond z).
  case e1: (z \in A); case e2: (- z \in A) => //=.
  - by case: (oppA_disjoint e1 e2).
  - by rewrite orbF -AC_mem_val e1.
  - by rewrite orbT.
  - by rewrite orbF -AC_mem_val e1.
have dis : [disjoint A & [set - z | z in A]].
  rewrite disjoints_subset; apply/subsetP=> y yA; rewrite !inE.
  apply/negP=> /imsetP[w wA e].
  by apply: (oppA_disjoint yA); rewrite e opprK.
have card_opp : #|[set - z | z in A]| = #|A|.
  by apply: card_imset; apply: inv_inj opprK.
have := cardsC1 (0 : 'Z_n).
rewrite copp cardsU disjoint_setI0 // cards0 subn0 card_opp.
move=> e.
have : (#|A| + #|A|)%N = m.*2 by rewrite e card_ord.
by rewrite addnn => /double_inj.
Qed.

Fact cardN0 : #|N0| = m.+1.
Proof. by rewrite cardsU1 mem0A cardA. Qed.

(** Shifted sets. *)
Let shift (t : 'Z_n) (B : {set 'Z_n}) : {set 'Z_n} := [set t + z | z in B].

Fact mem_shift (t u : 'Z_n) (B : {set 'Z_n}) : (u \in shift t B) = (u - t \in B).
Proof.
apply/imsetP/idP => [[z zB ->]|utB]; first by rewrite (addrC t z) addrK.
by exists (u - t); rewrite // addrC subrK.
Qed.

Fact shift_comp (s t : 'Z_n) (B : {set 'Z_n}) : shift s (shift t B) = shift (s + t) B.
Proof. by apply/setP=> u; rewrite !mem_shift opprD addrA. Qed.

Fact card_shift (t : 'Z_n) (B : {set 'Z_n}) : #|shift t B| = #|B|.
Proof. by apply: card_imset; apply: addrI. Qed.

Fact shiftI (t : 'Z_n) (B C : {set 'Z_n}) :
  shift t (B :&: C) = shift t B :&: shift t C.
Proof. by apply/setP=> u; rewrite !inE !mem_shift !inE. Qed.

Fact shift0 (B : {set 'Z_n}) : shift 0 B = B.
Proof. by apply/setP=> u; rewrite mem_shift subr0. Qed.

Fact autocorr_sym (t : 'Z_n) :
  #|N0 :&: shift t N0| = #|N0 :&: shift (- t) N0|.
Proof.
rewrite -[in RHS](card_shift t (_ :&: _)) shiftI shift_comp subrr shift0.
by rewrite setIC.
Qed.

Fact val1 : val (1 : 'Z_n) = 1%N.
Proof. by rewrite /= modn_small. Qed.

Let zeta : 'Z_n := inZp m.+1.

Fact val_zeta : val zeta = m.+1.
Proof.
rewrite /zeta /= modn_small // ltnS -addnn -[m.+1]addn1 addnC.
by rewrite -[(Zp_trunc (m + m).+1).+1]/((m + m)%N) leq_add2r.
Qed.

Fact N0_val_in (u : 'Z_n) :
  (val u < m)%N || (val u == m.+1) -> u \in N0.
Proof.
move=> h; rewrite !inE.
case: (posnP (val u)) => [u0|upos].
- by apply/orP; left; apply/eqP/val_inj; rewrite u0.
- by apply/orP; right; case/orP: h => ->; rewrite ?upos ?orbT.
Qed.

Fact N0_0 : (0 : 'Z_n) \in N0.
Proof. by rewrite !inE eqxx. Qed.

(** The autocorrelation lemma, low half: for 0 < val t ≤ m, the sets N₀ and
    N₀ + t share at least two elements (m ≥ 3). *)
Lemma autocorr_lo (t : 'Z_n) : (3 <= m)%N -> (0 < val t <= m)%N ->
  (2 <= #|N0 :&: shift t N0|)%N.
Proof.
move=> m3 /andP[tpos tle].
apply/card_gt1P.
case: (ltngtP (val t) m) => [tltm|gtm|teqm]; last 2 first.
- by move: (leq_ltn_trans tle gtm); rewrite ltnn.
- (* val t = m : the pair (0, ζ) *)
  exists 0, zeta; split.
  + rewrite inE N0_0 /= mem_shift sub0r.
    have vopp : val (- t) = m.+1.
      rewrite val_oppE teqm modn_small.
      * by rewrite -addnn -addSn addnK.
      * by rewrite ltn_subrL.
    by apply: N0_val_in; rewrite vopp eqxx orbT.
  + rewrite inE mem_shift.
    have vz : val (zeta - t) = 1%N.
      by rewrite (val_sub_le (i:=t)) ?val_zeta ?teqm ?leqnSn // subSn // subnn.
    apply/andP; split; apply: N0_val_in.
    * by rewrite val_zeta eqxx orbT.
    * by rewrite vz (ltnW m3).
  + by apply/eqP=> /(congr1 val); rewrite val_zeta.
case: (ltngtP (val t).+1 m) => [t1lt|t1gt|t1e]; first last.
- (* val t = m − 1 : the pair (t, ζ) *)
  exists t, zeta; split.
  + rewrite inE mem_shift subrr N0_0 andbT.
    by apply: N0_val_in; rewrite tltm.
  + rewrite inE mem_shift.
    have tlez : (val t <= val zeta)%N.
      by rewrite val_zeta (leq_trans (ltnW tltm)) // ltnW.
    have vz : val (zeta - t) = 2%N.
      have tE : val t = m' by case: t1e.
      by rewrite (val_sub_le tlez) val_zeta tE -addn2 addKn.
    apply/andP; split; apply: N0_val_in.
    * by rewrite val_zeta eqxx orbT.
    * by rewrite vz m3.
  + apply/eqP=> /(congr1 val); rewrite val_zeta => e.
    by have := tltm; rewrite e => /ltnW; rewrite leqNgt ltnSn.
- by move: t1gt; rewrite ltnS leqNgt tltm.
- (* val t + 1 < m : the pair (t, t+1) *)
  exists t, (t + 1); split.
  + rewrite inE mem_shift subrr N0_0 andbT.
    by apply: N0_val_in; rewrite tltm.
  + have vt1 : val (t + 1) = (val t).+1.
      rewrite val_addE val1 addn1 modn_small //.
      apply: (ltn_trans t1lt).
      by rewrite ltnS -addnn leq_addr.
    rewrite inE mem_shift.
    have -> : t + 1 - t = 1 by rewrite (addrC t 1) addrK.
    apply/andP; split; apply: N0_val_in.
    * by rewrite vt1 t1lt.
    * by rewrite val1 (ltnW m3).
  + apply/eqP=> /(congr1 val) e.
    have : (val t < val ((t + 1)%R : 'Z_n))%N.
      rewrite val_addE val1 addn1 modn_small ?ltnSn //.
      apply: (ltn_trans t1lt).
      by rewrite ltnS -addnn leq_addr.
    by rewrite -e ltnn.
Qed.

(** The autocorrelation lemma: every nonzero shift overlaps N₀ in ≥ 2 points. *)
Lemma autocorr2 (t : 'Z_n) : (3 <= m)%N -> t != 0 ->
  (2 <= #|N0 :&: shift t N0|)%N.
Proof.
move=> m3 tN0.
have tpos : (0 < val t)%N by move: tN0; rewrite lt0n -val_eqE.
case: (leqP (val t) m) => [tle|tgt]; first by rewrite autocorr_lo ?tpos.
rewrite autocorr_sym autocorr_lo //.
have vopp : val (- t) = (n - val t)%N.
  by rewrite val_oppE modn_small // ltn_subrL tpos.
rewrite vopp subn_gt0 ltn_ord /= leq_subLR.
apply: (@leq_trans (m.+1 + m)%N).
- by rewrite addSn addnn.
- by rewrite leq_add2r.
Qed.

(** dom(ACₙ) ≥ 3: one or two translates of N₀ cannot cover 'Z_n. *)
Lemma domnum_AC_ge3 : (3 <= m)%N -> (3 <= domnum (AC m' : tournament))%N.
Proof.
move=> m3.
have [X Xdom dn] := domnum_witness (AC m' : tournament).
rewrite dn leqNgt ltnS; apply/negP=> Xle2.
have covE (x : ACm) : x |: N_out x = shift (x : 'Z_n) N0.
  apply/setP=> v; rewrite !inE mem_shift !inE.
  by rewrite AC_arcE AC_mem_val subr_eq0.
have covT : [set: 'Z_n] \subset \bigcup_(x in X) shift (x : 'Z_n) N0.
  apply/subsetP=> v _.
  move/dominatesbP: Xdom => /(_ v) h.
  case e: (v \in X).
  - apply/bigcupP; exists v => //.
    by rewrite mem_shift subrr N0_0.
  - have [x xX xv] := h (negbT e).
    apply/bigcupP; exists x => //.
    by rewrite -covE !inE xv orbT.
have cardcov : (n <= #|\bigcup_(x in X) shift (x : 'Z_n) N0|)%N.
  by rewrite -[n in (n <= _)%N]card_ord -cardsT (subset_leq_card covT).
move: Xle2; rewrite leq_eqVlt ltnS leq_eqVlt ltnS leqn0.
case/or3P=> [/cards2P[x [y [xDy Xxy]]]|/cards1P[x Xx]|/eqP X0]; last 2 first.
- (* #|X| = 1: a single translate covers only m+1 < n vertices *)
  move: cardcov; rewrite Xx big_set1 card_shift cardN0.
  by rewrite ltnS -addnn -{3}[m]addn0 leq_add2l leqn0.
- (* #|X| = 0 *)
  move: cardcov; rewrite (cards0_eq X0) big_set0 cards0.
  by rewrite leqNgt.
(* #|X| = 2: two translates overlap in ≥ 2 points, covering ≤ 2m < n *)
have xny : x \notin [set y] by rewrite inE.
have eI : shift (x : 'Z_n) N0 :&: shift (y : 'Z_n) N0
          = shift (x : 'Z_n) (N0 :&: shift ((y : 'Z_n) - (x : 'Z_n)) N0).
  rewrite shiftI shift_comp.
  suff -> : (x : 'Z_n) + ((y : 'Z_n) - (x : 'Z_n)) = (y : 'Z_n) by [].
  by rewrite addrC subrK.
have yxN0 : (y : 'Z_n) - (x : 'Z_n) != 0.
  by rewrite subr_eq0 eq_sym; exact: xDy.
have hc := autocorr2 m3 yxN0.
move: cardcov.
rewrite Xxy big_setU1 // big_set1 cardsU !card_shift cardN0 eI card_shift.
move=> hh.
have hh2 : (n <= m + m)%N.
  have := leq_trans hh (leq_sub2l _ hc).
  by rewrite addnS addSn !subSS subn0.
by move: hh2; rewrite -addnn leqNgt ltnSn.
Qed.

(** ** ω̄(ACₙ) = 3 *)

Theorem omegabar_AC : (3 <= m)%N -> ω̄((AC m' : tournament)) = 3.
Proof.
move=> m3; apply/anti_leq/andP; split; first exact: omegabar_AC_le3.
exact: leq_trans (domnum_AC_ge3 m3) (domnum_le_omegabar _).
Qed.

(** ** ACₙ − 0 still contains the directed triangle 1 → 2 → m+3 → 1 *)

Let c1 : 'Z_n := 1.
Let c2 : 'Z_n := inZp 2.
Let c3 : 'Z_n := inZp (m + 3).

Lemma ACdel_Ntransb : (3 <= m)%N -> ~~ transb ACdel.
Proof.
move=> m3.
have vc2 : val c2 = 2%N.
  by rewrite /c2 /= modn_small // ltnS -addnn -[2]/(1+1)%N leq_add.
have vc3 : val c3 = (m + 3)%N.
  by rewrite /c3 /= modn_small // ltnS -addnn leq_add2l.
have pf1 : (c1 : ACm) \in [set~ z0] by rewrite !inE -val_eqE val1.
have pf2 : (c2 : ACm) \in [set~ z0] by rewrite !inE -val_eqE vc2.
have pf3 : (c3 : ACm) \in [set~ z0] by rewrite !inE -val_eqE vc3.
apply/ntransbP.
exists (Sub (c1 : ACm) pf1), (Sub (c2 : ACm) pf2), (Sub (c3 : ACm) pf3).
split; rewrite sub_arcE !SubK.
- (* 1 → 2 : gap 1 < m *)
  by rewrite AC_arc_lt ?val1 ?vc2 // (ltnW m3).
- (* 2 → m+3 : gap m+1 *)
  rewrite AC_arc_lt ?vc2 ?vc3; last by rewrite addn3.
  by rewrite addnC !subSS subn0 eqxx orbT.
- (* m+3 → 1 : gap m+2, a backedge of the value order *)
  rewrite (AC_arc_gt (i := (c1 : ACm)) (j := (c3 : ACm))) ?val1 ?vc3;
    last by rewrite addn3.
  by rewrite addnC !subSS subn0 leqnn orbT.
Qed.

(** ** ω̄(ACₙ − v) = 2 and 3-criticality *)

Lemma omegabar_ACdel0 : (3 <= m)%N -> ω̄(ACdel) = 2.
Proof.
move=> m3; apply/anti_leq/andP; split; first exact: omegabar_ACdel_le2.
have pos : (0 < #|ACdel|)%N.
  apply/card_gt0P.
  have pf1 : (c1 : ACm) \in [set~ z0] by rewrite !inE -val_eqE val1.
  by exists (Sub (c1 : ACm) pf1).
by rewrite ltn_neqAle eq_sym omegabar_transb // (negbTE (ACdel_Ntransb m3))
           omegabar_gt0.
Qed.

Theorem omegabar_AC_del (v : ACm) :
  (3 <= m)%N -> ω̄(del_tournament v) = 2.
Proof.
move=> m3.
rewrite (omegabar_del_vt (AC_vertex_transitive m') v z0).
exact: omegabar_ACdel0.
Qed.

Theorem AC_kcritical3 : (3 <= m)%N -> kcritical 3 (AC m' : tournament).
Proof.
move=> m3.
rewrite (vt_kcritical 3 z0 (AC_vertex_transitive m')).
by rewrite omegabar_AC // omegabar_ACdel0 // !eqxx.
Qed.

End ACBase.
