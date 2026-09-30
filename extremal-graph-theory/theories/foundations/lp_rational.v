(** * Extremal.foundations.lp_rational -- attainment of rational linear programs

    A self-contained, axiom-free Fourier-Motzkin elimination over [rat], used to prove
    that the fractional invariants of [Extremal.conjectures.D2chr] (chi_f, had_f) exist
    as ATTAINED optima (atlas [fractional.frac_chromatic_exists] /
    [fractional.frac_hadwiger_exists]).

    - [lhs N a x] = sum_(i < N) a_i x_i, a constraint [(a, beta)] reads [lhs N a x <= beta],
      [sat N s x] = x satisfies every constraint of the list [s] (coefficients are
      [seq rat], so constraints form an [eqType]).
    - [fm_elim N s] eliminates variable [N] (pairwise positive/negative combinations);
      [fm_sound] / [fm_complete]: the projection of the solution set of [s] along
      variable [N] is exactly the solution set of [fm_elim N s]; [fm_proj] iterates.
    - [lp_max]: a feasible LP whose objective is bounded above ATTAINS its maximum
      (project onto the objective value: a 1-variable system, whose feasible set is a
      closed half-line or segment).
    - [lp_max_fin]: the same, with variables and constraints indexed by finite types.
    - [list_argmax]: arg-max of attained optima over a finite list of candidates. *)

From mathcomp Require Import all_boot all_order all_algebra.
Import GRing.Theory Num.Theory Order.TotalTheory Order.POrderTheory.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** ** Fourier-Motzkin elimination over [rat] (nat-indexed variables). *)
Notation cstr := (seq rat * rat)%type.
Definition lhs (N : nat) (a : seq rat) (x : nat -> rat) : rat := \sum_(i < N) nth 0 a i * x i.
Definition sat (N : nat) (s : seq cstr) (x : nat -> rat) : bool :=
  all (fun c => lhs N c.1 x <= c.2) s.
Notation co c i := (nth 0 (c : cstr).1 i).

Lemma lhsS N a x : lhs N.+1 a x = lhs N a x + nth 0 a N * x N.
Proof. by rewrite /lhs big_ord_recr. Qed.

Lemma lhs_ext N a x y : (forall i, (i < N)%N -> x i = y i) -> lhs N a x = lhs N a y.
Proof. by move=> e; apply: eq_bigr => i _; rewrite e. Qed.

Lemma sat_ext N s x y : (forall i, (i < N)%N -> x i = y i) -> sat N s x = sat N s y.
Proof. by move=> e; apply: eq_all => c; rewrite (lhs_ext c.1 e). Qed.

Definition comb (N : nat) (p n : cstr) : cstr :=
  (mkseq (fun i => (- co n N) * co p i + co p N * co n i) N, (- co n N) * p.2 + co p N * n.2).

Definition fm_elim (N : nat) (s : seq cstr) :=
  [seq c <- s | co c N == 0] ++
  [seq comb N p n | p <- [seq c <- s | 0 < co c N], n <- [seq c <- s | co c N < 0]].

Lemma lhs_comb N p n x :
  lhs N (comb N p n).1 x = (- co n N) * lhs N p.1 x + co p N * lhs N n.1 x.
Proof.
rewrite /lhs /= !mulr_sumr -big_split /=; apply: eq_bigr => i _.
by rewrite nth_mkseq // mulrDl !mulrA.
Qed.

Lemma fm_sound N s x : sat N.+1 s x -> sat N (fm_elim N s) x.
Proof.
rewrite /sat => /allP H; apply/allP => c; rewrite mem_cat => /orP [].
  rewrite mem_filter => /andP [/eqP c0 cs]; have := H c cs.
  by rewrite lhsS c0 mul0r addr0.
case/allpairsP => [[p n] [/= + + ->]].
rewrite !mem_filter => /andP [p0 ps] /andP [n0 ns].
have hp := H p ps; have hn := H n ns; rewrite lhsS in hp; rewrite lhsS in hn.
rewrite /= lhs_comb.
have nN : 0 <= - co n N by rewrite oppr_ge0 ltW.
have e1 : (- co n N) * lhs N p.1 x + co p N * lhs N n.1 x =
          (- co n N) * (lhs N p.1 x + co p N * x N) + co p N * (lhs N n.1 x + co n N * x N).
  have e2 : (- co n N) * (co p N * x N) + co p N * (co n N * x N) = 0.
    by rewrite mulNr !mulrA [co n N * co p N]mulrC addNr.
  by rewrite !mulrDr addrACA e2 addr0.
rewrite e1; apply: lerD; rewrite -subr_ge0 -mulrBr; apply: mulr_ge0; rewrite ?subr_ge0 ?(ltW p0) //.
Qed.

Lemma lower_bound_seq (us : seq rat) : exists x, forall u, u \in us -> x <= u.
Proof.
elim: us => [|u us [x Hx]]; first by exists 0.
exists (Order.min x u) => v; rewrite inE => /orP [/eqP ->|/Hx]; first by rewrite ge_min lexx orbT.
by move=> xv; rewrite ge_min xv.
Qed.

Lemma sep_seq (ls us : seq rat) :
  (forall l u, l \in ls -> u \in us -> l <= u) ->
  exists x, (forall l, l \in ls -> l <= x) /\ (forall u, u \in us -> x <= u).
Proof.
elim: ls => [|l ls IH] H.
  by have [x Hx] := lower_bound_seq us; exists x.
have [|x [H1 H2]] := IH.
  by move=> l' u hl hu; apply: H => //; rewrite inE hl orbT.
exists (Order.max x l); split.
  move=> l'; rewrite inE => /orP [/eqP ->|/H1 lx]; first by rewrite le_max lexx orbT.
  by rewrite le_max lx.
by move=> u hu; rewrite ge_max H2 //= H // inE eqxx.
Qed.

Definition upd (y : nat -> rat) (N : nat) (x0 : rat) : nat -> rat :=
  fun i => if i == N then x0 else y i.

Lemma div_sep (a b Pp Pn p2 n2 : rat) : 0 < a -> 0 < b ->
  a * Pp + b * Pn <= a * p2 + b * n2 -> (Pn - n2) / a <= (p2 - Pp) / b.
Proof.
move=> a0 b0 h.
rewrite ler_pdivrMr // mulrAC ler_pdivlMr // -subr_ge0.
have -> : (p2 - Pp) * a - (Pn - n2) * b = (a * p2 + b * n2) - (a * Pp + b * Pn).
  rewrite !mulrBl opprB addrACA -opprD.
  by congr (_ - _); congr (_ + _); apply: mulrC.
by rewrite subr_ge0.
Qed.

Lemma fm_complete N s y : sat N (fm_elim N s) y -> exists x0, sat N.+1 s (upd y N x0).
Proof.
rewrite /sat => /allP H.
pose U (p : cstr) := (p.2 - lhs N p.1 y) / co p N.
pose pos := [seq c <- s | 0 < co c N]; pose neg := [seq c <- s | co c N < 0].
have [|x0 [HL HU]] := @sep_seq (map U neg) (map U pos).
  move=> l u /mapP [n nn ->] /mapP [p pp ->].
  move: nn pp; rewrite !mem_filter => /andP [n0 ns] /andP [p0 ps].
  have hc : comb N p n \in fm_elim N s.
    by rewrite mem_cat; apply/orP; right; apply/allpairsP; exists (p, n); rewrite !mem_filter p0 n0 ps ns.
  have := H _ hc; rewrite /= lhs_comb => ineq.
  have a0 : 0 < - co n N by rewrite oppr_gt0.
  have eU : U n = (lhs N n.1 y - n.2) / (- co n N).
    by rewrite /U invrN mulrN -mulNr opprB.
  by rewrite eU /U; apply: div_sep => //; rewrite opprK.
exists x0; apply/allP => c cs /=.
rewrite lhsS (@lhs_ext _ _ _ y); last by move=> i iN; rewrite /upd (ltn_eqF iN).
rewrite /upd eqxx.
case: (ltrgtP 0 (co c N)) => c0.
- have := HU (U c) (map_f U (_ : c \in pos)); rewrite mem_filter c0 cs => /(_ isT).
  by rewrite /U ler_pdivlMr // mulrC -lerBrDl addrC.
- have := HL (U c) (map_f U (_ : c \in neg)); rewrite mem_filter c0 cs => /(_ isT).
  by rewrite /U ler_ndivrMr // mulrC -lerBrDl addrC.
- have hc : c \in fm_elim N s by rewrite mem_cat mem_filter -c0 eqxx cs.
  by have := H _ hc; rewrite -c0 mul0r addr0.
Qed.

Lemma fm_proj k N s : exists s' : seq cstr, forall y,
  sat N s' y <-> exists x, (forall i, (i < N)%N -> x i = y i) /\ sat (N + k) s x.
Proof.
elim: k s => [|k IH] s.
  exists s => y; split => [h|[x [e h]]]; first by exists y; rewrite addn0.
  by rewrite -(sat_ext s e) -[N]addn0.
have [s' Hs'] := IH (fm_elim (N + k) s).
exists s' => y; rewrite addnS; split.
  case/Hs' => x [e /fm_complete [x0 h]]; exists (upd x (N + k) x0); split => // i iN.
  by rewrite /upd ifF ?e // ltn_eqF // (leq_trans iN) // leq_addr.
by case=> x [e h]; apply/Hs'; exists x; split => //; exact: fm_sound.
Qed.

Lemma min_in_seq (us : seq rat) : us != [::] ->
  exists u, u \in us /\ forall v, v \in us -> u <= v.
Proof.
elim: us => [//|u us IH] _.
case: us IH => [_|u' us'] .
  by exists u; split => [|v]; rewrite ?mem_seq1 ?eqxx // => /eqP ->.
case/(_ isT) => m [mi hm].
case: (lerP u m) => um.
  exists u; split; first by rewrite inE eqxx.
  move=> v; rewrite inE => /orP [/eqP ->//|/hm]; exact: le_trans.
exists m; split; first by rewrite inE mi orbT.
move=> v; rewrite inE => /orP [/eqP ->|/hm //]; exact: ltW.
Qed.

Definition shiftc (c : cstr) : cstr := (0 :: c.1, c.2).

Lemma nth_oppseq (c : seq rat) i : nth 0 [seq - a | a <- c] i = - nth 0 c i.
Proof.
case: (ltnP i (size c)) => h; first by rewrite (nth_map 0).
by rewrite !nth_default ?size_map // oppr0.
Qed.

Lemma lhs_cons K (a0 : rat) a x :
  lhs K.+1 (a0 :: a) x = a0 * x 0%N + lhs K a (fun i => x i.+1).
Proof. by rewrite /lhs big_ord_recl. Qed.

Lemma lp_max K (s : seq cstr) (c : seq rat) :
  (exists x, sat K s x) -> (exists M, forall x, sat K s x -> lhs K c x <= M) ->
  exists x, sat K s x /\ forall x', sat K s x' -> lhs K c x' <= lhs K c x.
Proof.
move=> [x0 hx0] [M hM].
pose oc : cstr := (1 :: [seq - a | a <- c], 0).
pose S := oc :: map shiftc s.
have satS x : sat K.+1 S x = (x 0%N <= lhs K c (fun i => x i.+1)) && sat K s (fun i => x i.+1).
  rewrite /sat /= all_map /= lhs_cons mul1r.
  have -> : lhs K [seq - a | a <- c] (fun i => x i.+1) = - lhs K c (fun i => x i.+1).
    by rewrite /lhs -sumrN; apply: eq_bigr => i _; rewrite nth_oppseq mulNr.
  rewrite subr_le0 /=; congr (_ && _); apply: eq_all => d /=.
  by rewrite /shiftc lhs_cons /= mul0r add0r.
have [s1 Hs1] := fm_proj K 1 S.
pose T t := sat 1 s1 (fun _ => t).
have T1 x t : sat K s x -> t <= lhs K c x -> T t.
  move=> hx ht; apply/Hs1; exists (fun i => if i is j.+1 then x j else t); split.
    by case.
  by rewrite add1n satS /= ht hx.
have T2 t : T t -> exists x, sat K s x /\ t <= lhs K c x.
  case/Hs1 => x [e]; rewrite add1n satS => /andP [h1 h2].
  by exists (fun i => x i.+1); split => //; rewrite -(e 0%N).
have Tsat t : T t = all (fun d : cstr => co d 0%N * t <= d.2) s1.
  by apply: eq_all => d; rewrite /lhs big_ord1.
have hT0 : T (lhs K c x0) by exact: (T1 x0 _ hx0 (lexx _)).
pose us := [seq d.2 / co d 0%N | d <- s1 & 0 < co d 0%N].
case: (altP (us =P [::])) => hus.
  exfalso.
  pose t := Order.max (lhs K c x0) (M + 1).
  have : T t.
    rewrite Tsat; apply/allP => d ds; move: (hT0); rewrite Tsat => /allP /(_ d ds).
    case: (ltrgtP 0 (co d 0%N)) => d0.
    - move: hus; rewrite /us; case: [seq _ <- _ | _] (mem_filter (fun d : cstr => 0 < co d 0%N) d s1) => [|? ?] //.
      by rewrite ds d0 in_nil.
    - move=> h; apply: le_trans h; by rewrite ler_nM2l // le_max lexx.
    - by rewrite -d0 !mul0r.
  case/T2 => x [hx ht]; have := hM x hx.
  have h1 : M + 1 <= lhs K c x by apply: le_trans ht; rewrite le_max lexx orbT.
  move=> h2.
  by have := le_trans h1 h2; rewrite gerDl ler10.
have [u [ui hu]] := min_in_seq hus.
move: (ui); rewrite /us => /mapP [d']; rewrite mem_filter => /andP [d'0 d's] eu.
have Tle t : T t -> t <= u.
  rewrite Tsat => /allP /(_ d' d's); by rewrite eu ler_pdivlMr // mulrC.
have Tu : T u.
  rewrite Tsat; apply/allP => d ds.
  case: (ltrgtP 0 (co d 0%N)) => d0.
  - have : d.2 / co d 0%N \in us by apply/mapP; exists d; rewrite ?mem_filter ?d0.
    by move/hu; rewrite ler_pdivlMr // mulrC.
  - move: (hT0); rewrite Tsat => /allP /(_ d ds) h; apply: le_trans h.
    by rewrite ler_nM2l //; apply: Tle.
  - by move: (hT0); rewrite Tsat => /allP /(_ d ds); rewrite -d0 !mul0r.
case/T2: Tu => x [hx hux]; exists x; split => // x' hx'.
by apply: le_trans hux; apply: Tle; exact: (T1 x' _ hx' (lexx _)).
Qed.

(** Finite-type front end of [lp_max]. *)
Definition cf (T : finType) (a : T -> rat) : seq rat :=
  mkseq (fun i => oapp (fun o : 'I_#|T| => a (enum_val o)) 0 (insub i)) #|T|.

Lemma lhs_fin (T : finType) (a : T -> rat) x :
  lhs #|T| (cf a) x = \sum_(u : T) a u * x (enum_rank u).
Proof.
rewrite /lhs (reindex (@enum_rank T)) /=; last first.
  by exists enum_val => o _; rewrite ?enum_valK ?enum_rankK.
apply: eq_bigr => u _; rewrite /cf nth_mkseq ?ltn_ord // valK /= enum_rankK.
by [].
Qed.

Lemma lp_max_fin (I T : finType) (A : I -> T -> rat) (b : I -> rat) (c : T -> rat) :
  let feas X := forall i, \sum_(u : T) A i u * X u <= b i in
  (exists X, feas X) -> (exists M, forall X, feas X -> \sum_(u : T) c u * X u <= M) ->
  exists X, feas X /\ forall X', feas X' -> \sum_(u : T) c u * X' u <= \sum_(u : T) c u * X u.
Proof.
move=> feas [X0 h0] [M hM].
pose s : seq cstr := [seq (cf (A i), b i) | i <- enum I].
pose vx (X : T -> rat) : nat -> rat := fun i => oapp (fun o : 'I_#|T| => X (enum_val o)) 0 (insub i).
have vxE X u : vx X (enum_rank u) = X u by rewrite /vx valK /= enum_rankK.
have satE x : sat #|T| s x = [forall i, \sum_(u : T) A i u * x (enum_rank u) <= b i].
  rewrite /sat all_map; apply/allP/forallP => [h i|h i _] /=.
    by rewrite -lhs_fin; apply: h; rewrite mem_enum.
  by rewrite lhs_fin; exact: h.
have feasE x : sat #|T| s x -> feas (fun u => x (enum_rank u)).
  by rewrite satE => /forallP.
have satX X : feas X -> sat #|T| s (vx X).
  by move=> h; rewrite satE; apply/forallP => i; under eq_bigr do rewrite vxE; exact: h.
have [x [hx opt]] : exists x, sat #|T| s x /\ forall x', sat #|T| s x' -> lhs #|T| (cf c) x' <= lhs #|T| (cf c) x.
  apply: lp_max; first by exists (vx X0); exact: satX.
  by exists M => x /feasE /hM; rewrite lhs_fin.
exists (fun u => x (enum_rank u)); split; first exact: feasE.
move=> X' /satX /opt; rewrite !lhs_fin; by under eq_bigr do rewrite vxE.
Qed.

(** Arg-max of attained optima over a finite list of candidates. *)
Lemma list_argmax (A : eqType) (P : pred A) (Q : A -> rat -> Prop) (L : seq A) :
  (forall a, P a -> exists r, Q a r) -> (forall a r r', Q a r -> Q a r' -> r = r') ->
  has P L ->
  exists a r, [/\ P a, Q a r & forall a' r', a' \in L -> P a' -> Q a' r' -> r' <= r].
Proof.
move=> hQ hU; elim: L => [//|a L IH] /=.
case: (boolP (P a)) => Pa hh; last first.
  have [a' [r' [Pa' Qa' M']]] := IH hh.
  exists a', r'; split => // b rb; rewrite inE => /orP [/eqP -> Pb|]; last exact: M'.
  by rewrite Pb in Pa.
have [ra Qa] := hQ a Pa.
case: (boolP (has P L)) => hL.
  have [a' [r' [Pa' Qa' M']]] := IH hL.
  case: (lerP ra r') => c.
    exists a', r'; split => // b rb; rewrite inE => /orP [/eqP -> _ Qb|bL Pb Qb].
      by rewrite (hU _ _ _ Qb Qa).
    exact: M' bL Pb Qb.
  exists a, ra; split => // b rb; rewrite inE => /orP [/eqP -> _ Qb|bL Pb Qb].
    by rewrite (hU _ _ _ Qb Qa).
  exact: le_trans (M' _ _ bL Pb Qb) (ltW c).
exists a, ra; split => // b rb; rewrite inE => /orP [/eqP -> _ Qb|bL Pb Qb].
  by rewrite (hU _ _ _ Qb Qa).
by move/hasPn: hL => /(_ b bL); rewrite Pb.
Qed.
