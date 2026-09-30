(** * Atlas.foundations.fractional -- LP facts on the D2chr fractional invariants

    Elementary inequalities between the project-local fractional chromatic number
    ([is_fractional_chromatic], an attained minimum of a/b over (a:b)-colourings)
    and fractional Hadwiger number ([is_fractional_hadwiger], an attained maximum
    of the clique-minor LP) of [Extremal.conjectures.D2chr] and the integral
    invariants: [chi_f <= chi] and [n <= had_f] whenever [K_n] is a minor.  They
    would belong in [extremal-graph-theory]'s foundations, but that package cannot
    import [minor-theory]'s rows, so they live in the atlas. *)

From GTBase Require Import base.
From GraphTheory Require Import minor.
From Extremal.conjectures Require Import D2chr grounding_D2chr.
From Extremal.foundations Require Import lp_rational.
From mathcomp Require Import all_algebra.
Import GRing.Theory Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** An optimal colouring as a map into ['I_chi]. *)
Lemma chi_colouring (G : sgraph) :
  exists f : G -> 'I_χ([set: G]), forall x y : G, x -- y -> f x != f y.
Proof.
case: chiP => P hcol _.
have [hpart hstab] := andP hcol.
have hcov : cover P = [set: G] by rewrite (cover_partition hpart); apply/setP => x; rewrite !inE.
have inP (x : G) : pblock P x \in P.
  by rewrite pblock_mem // hcov inE.
have lt (x : G) : (index (pblock P x) (enum P) < #|P|)%N.
  by rewrite cardE index_mem mem_enum.
exists (fun x => Ordinal (lt x)) => x y xy; apply/negP => /eqP [] e.
have eb : pblock P x = pblock P y.
  by rewrite -(nth_index set0 (s := enum P) (x := pblock P x)) ?mem_enum // e nth_index ?mem_enum.
have /stableP st : stable (pblock P x) by move/forallP: hstab => /(_ (pblock P x)); rewrite inP.
have hx : x \in pblock P x by rewrite mem_pblock hcov inE.
have hy : y \in pblock P x by rewrite eb mem_pblock hcov inE.
by move: (st x y hx hy); rewrite xy.
Qed.

Local Open Scope ring_scope.

(** [chi_f <= chi]: an optimal colouring is a [(chi:1)]-colouring. *)
Lemma frac_chi_le_chi (G : sgraph) (xf : rat) :
  is_fractional_chromatic G xf -> xf <= (χ([set: G]))%:Q.
Proof.
case=> _ H.
have [f hf] := chi_colouring G.
have := H χ([set: G]) 1%N isT.
rewrite divr1; apply; exists (fun v => [set f v]); split => [v|x y xy].
  by rewrite cards1.
by rewrite disjoints1 inE (hf x y xy).
Qed.

(** [had <= had_f]: the branch sets of a [K_n] minor, each with weight one, are a
    feasible point of the fractional clique-minor LP of D2chr. *)
Lemma minor_K_le_frac_hadwiger (G : sgraph) (n : nat) (hf : rat) :
  minor G 'K_n -> is_fractional_hadwiger G hf -> n%:Q <= hf.
Proof.
move=> /minorRE [phi [ne con dis nb]] [_ H].
apply: (H n phi (fun _ => 1)); split => //.
- by move=> i j ij; have /neighborP [x [y [hx hy xy]]] := nb i j ij; exists x, y.
- move=> v.
  rewrite sumr_const.
  have c1 : (#|[pred i : 'I_n | v \in phi i]| <= 1)%N.
    apply/card_le1_eqP => i j hi hj.
    by apply: (@rmap_disjE G 'K_n phi v j i _ hj hi); split.
  by rewrite -[X in _ <= X](mulr1n 1) ler_pMn2l ?ltr01 //; exact: c1.
- by rewrite sumr_const card_ord pmulrn.
Qed.

(** STATEMENT DEFECT, REPAIRED (wave E10, 2026-09-24).  Wave A1 found that the
    original [frac_clique_minor] allowed EMPTY branch sets, making the clique-minor LP
    unbounded and [is_fractional_hadwiger] unsatisfiable (so the D2chr row was vacuously
    true).  D2chr now requires non-empty branch sets; the witness of the OLD defect is
    kept, on the old body spelled out verbatim, as
    [Extremal.conjectures.grounding_D2chr.old_is_fractional_hadwiger_unsat]. The two
    lemmas above are the honest ones and hold for the repaired definition. *)

(** ** Attainment of chi_f and had_f (wave E10).
    Both D2chr invariants are passed to the rows as parameters constrained by
    "attained optimum" predicates; the lemmas below show that these optima EXIST for
    every finite graph, by the Fourier-Motzkin LP-attainment theorem
    [Extremal.foundations.lp_rational.lp_max_fin]:
    - [frac_hadwiger_exists]: the clique-minor LP of every "bramble" (a set of non-empty
      connected, pairwise adjacent vertex sets, [goodb]) attains its maximum; the best
      bramble is found by [list_argmax] over the finitely many candidates, and every
      feasible indexed family collapses (duplicate sets merged, [sum_fibres]) onto the LP
      of its own bramble;
    - [frac_chromatic_exists]: the covering LP over stable sets attains its minimum [Y];
      clearing denominators of [Y] gives an (a:b)-colouring with a/b = sum Y
      ([colouring_of]), while every (a:b)-colouring yields a feasible point of value
      a/b ([colouring_feas]);
    - [frac_chi_n_alpha]: n <= chi_f * alpha (double counting of colour classes). *)
Import mathcomp.order.preorder.Order.PreorderTheory
  mathcomp.order.order.Order.POrderTheory mathcomp.order.order.Order.TotalTheory.

Lemma sum_enum_val (T : finType) (P : pred T) (F : T -> rat) :
  \sum_(o < #|T| | P (enum_val o)) F (enum_val o) = \sum_(u | P u) F u.
Proof.
rewrite (reindex (@enum_rank T)) /=; last by exists enum_val => o _; rewrite ?enum_valK ?enum_rankK.
by apply: eq_big => [u|u _]; rewrite enum_rankK.
Qed.

Lemma sum_fibres (n : nat) (T : finType) (f : 'I_n -> T) (P : pred T) (w : 'I_n -> rat) :
  \sum_(S | P S) \sum_(i | f i == S) w i = \sum_(i | P (f i)) w i.
Proof.
rewrite [RHS](partition_big f P) //; apply: eq_bigr => S PS.
by apply: eq_bigl => i; case: (altP (f i =P S)) => [->|]; rewrite ?PS ?andbF ?andbT.
Qed.

Section HadF.
Variable G : sgraph.
Local Notation bsT Bs := {S : {set G} | S \in Bs}.

Definition goodb (Bs : {set {set G}}) : bool :=
  [forall S in Bs, (S != set0) && connectedb S] &&
  [forall S in Bs, forall S' in Bs, (S != S') ==> [exists x in S, exists y in S', x -- y]].

Definition hfeas (Bs : {set {set G}}) (X : bsT Bs -> rat) : Prop :=
  (forall S, 0 <= X S) /\ (forall v : G, \sum_(S : bsT Bs | v \in val S) X S <= 1).

Definition hopt (Bs : {set {set G}}) (r : rat) : Prop :=
  (exists X, @hfeas Bs X /\ \sum_(S : bsT Bs) X S = r) /\ (forall X, @hfeas Bs X -> \sum_(S : bsT Bs) X S <= r).

Lemma hopt_unique Bs r r' : hopt Bs r -> hopt Bs r' -> r = r'.
Proof.
move=> [[X [hX <-]] H] [[X' [hX' <-]] H'].
by apply/le_anti; rewrite H' ?H.
Qed.

Lemma fam_ok Bs X : goodb Bs -> @hfeas Bs X ->
  frac_clique_minor (fun o : 'I_#|{: bsT Bs}| => val (enum_val o))
                    (fun o => X (enum_val o)) (\sum_(S : bsT Bs) X S).
Proof.
case/andP => /forall_inP h1 /forall_inP h2 [X0 Xc]; split => //.
- move=> o; have /andP [ne /connectedP co] := h1 _ (valP (enum_val o)); by split.
- move=> o o' oo'.
  have := h2 _ (valP (enum_val o)) => /forall_inP /(_ _ (valP (enum_val o'))).
  have -> : val (enum_val o) != val (enum_val o').
    by apply: contra oo' => /eqP /val_inj /enum_val_inj ->.
  by case/exists_inP => x xS /exists_inP [y yS xy]; exists x, y.
- by move=> v; rewrite (@sum_enum_val _ (fun S : bsT Bs => v \in val S) X).
- by rewrite (@sum_enum_val (bsT Bs) predT X).
Qed.

Lemma hfeas_bounded Bs X : goodb Bs -> @hfeas Bs X -> \sum_(S : bsT Bs) X S <= (#|G|)%:R.
Proof. by move=> g h; apply: frac_clique_minor_le_card (fam_ok g h). Qed.

Lemma hopt_exists Bs : goodb Bs -> exists r, hopt Bs r.
Proof.
move=> g.
pose T := {S : {set G} | S \in Bs}.
pose A (i : (T + G)%type) (S : T) : rat :=
  match i with inl S0 => if S0 == S then -1 else 0 | inr v => if v \in val S then 1 else 0 end.
pose b (i : (T + G)%type) : rat := match i with inl _ => 0 | inr _ => 1 end.
have feasE (X : T -> rat) : (forall i, \sum_(S : T) A i S * X S <= b i) <-> hfeas X.
  have e1 S0 : \sum_(S : T) A (inl S0) S * X S = - X S0.
    rewrite /A (bigD1 S0) //= eqxx mulN1r big1 ?addr0 // => S /negbTE.
    by rewrite eq_sym => ->; rewrite mul0r.
  have e2 v : \sum_(S : T) A (inr v) S * X S = \sum_(S : T | v \in val S) X S.
    by rewrite [RHS]big_mkcond; apply: eq_bigr => S _ /=; case: ifP; rewrite ?mul1r ?mul0r.
  split => [H|[H1 H2] [S0|v]].
  - split => [S0|v]; [have := H (inl S0) | have := H (inr v)]; rewrite ?e1 ?e2 //.
    by rewrite oppr_le0.
  - by rewrite e1 oppr_le0.
  - by rewrite e2.
have [X [hX opt]] : exists X : T -> rat, (forall i, \sum_(S : T) A i S * X S <= b i) /\
    forall X' : T -> rat, (forall i, \sum_(S : T) A i S * X' S <= b i) ->
      \sum_(S : T) 1 * X' S <= \sum_(S : T) 1 * X S.
  apply: (@lp_max_fin _ _ A b (fun _ => 1)).
    exists (fun _ => 0); apply/feasE; split => // v; rewrite big1 //.
  by exists (#|G|)%:R => X /feasE hX; under eq_bigr do rewrite mul1r; exact: hfeas_bounded.
exists (\sum_(S : T) X S); split.
  by exists X; split => //; apply/feasE.
move=> X' /feasE /opt; by under eq_bigr do rewrite mul1r; under [X in _ <= X]eq_bigr do rewrite mul1r.
Qed.

Lemma frac_hadwiger_exists : exists hf, is_fractional_hadwiger G hf.
Proof.
have [|Bs [r [gB oB M]]] := @list_argmax _ goodb hopt (enum {set {set G}}) hopt_exists (@hopt_unique).
  apply/hasP; exists set0; rewrite ?mem_enum //.
  by apply/andP; split; apply/forall_inP => S; rewrite inE.
exists r; split.
  case: oB => [[X [hX <-]] _]; exists #|{: bsT Bs}|, (fun o => val (enum_val o)), (fun o => X (enum_val o)).
  exact: fam_ok gB hX.
move=> n B w r' [w0 bc adj cov ->].
pose Bs' := B @: [set: 'I_n].
have hB i : B i \in Bs' by apply: imset_f; rewrite inE.
pose f (i : 'I_n) : {S : {set G} | S \in Bs'} := exist _ (B i) (hB i).
have g' : goodb Bs'.
  apply/andP; split; apply/forall_inP => S /imsetP [i _ ->].
    by have [ne co] := bc i; rewrite ne; apply/connectedP.
  apply/forall_inP => S' /imsetP [j _ ->]; apply/implyP => ne.
  have [|x [y [xi yj xy]]] := adj i j; first by apply: contra ne => /eqP ->.
  by apply/exists_inP; exists x => //; apply/exists_inP; exists y.
pose X (S : {S : {set G} | S \in Bs'}) := \sum_(i | f i == S) w i.
have hX : hfeas X.
  split => [S|v]; first by apply: sumr_ge0 => i _; exact: w0.
  by rewrite /X (sum_fibres f (fun S => v \in val S)); exact: cov.
have [rB oB'] := hopt_exists g'.
apply: le_trans (M Bs' rB _ g' oB'); last by rewrite mem_enum.
case: oB' => _ /(_ X hX); by rewrite /X (sum_fibres f predT).
Qed.
End HadF.

Section ChiF.
Variable G : sgraph.
Local Notation stT := {I : {set G} | stable I}.

Lemma stable_set1 (v : G) : stable [set v].
Proof. by apply/stableP => x y; rewrite !inE => /eqP -> /eqP ->; rewrite sg_irrefl. Qed.

Lemma stable_set0 : stable (@set0 G).
Proof. by apply/stableP => x y; rewrite inE. Qed.

Definition cfeas (Y : stT -> rat) : Prop :=
  (forall I, 0 <= Y I) /\ (forall v : G, 1 <= \sum_(I : stT | v \in val I) Y I).

Lemma copt_exists : exists Y, cfeas Y /\
  forall Y', cfeas Y' -> \sum_(I : stT) Y I <= \sum_(I : stT) Y' I.
Proof.
pose A (i : (stT + G)%type) (I : stT) : rat :=
  match i with inl I0 => if I0 == I then -1 else 0 | inr v => if v \in val I then -1 else 0 end.
pose b (i : (stT + G)%type) : rat := match i with inl _ => 0 | inr _ => -1 end.
have feasE (Y : stT -> rat) : (forall i, \sum_(I : stT) A i I * Y I <= b i) <-> cfeas Y.
  have e1 I0 : \sum_(I : stT) A (inl I0) I * Y I = - Y I0.
    rewrite /A (bigD1 I0) //= eqxx mulN1r big1 ?addr0 // => I /negbTE.
    by rewrite eq_sym => ->; rewrite mul0r.
  have e2 v : \sum_(I : stT) A (inr v) I * Y I = - \sum_(I : stT | v \in val I) Y I.
    rewrite -sumrN [RHS]big_mkcond; apply: eq_bigr => I _ /=.
    by case: ifP; rewrite ?mulN1r ?mul0r ?oppr0.
  split => [H|[H1 H2] [I0|v]].
  - split => [I0|v]; [have := H (inl I0) | have := H (inr v)]; rewrite ?e1 ?e2 /=.
      by rewrite oppr_le0.
    by rewrite lerN2.
  - by rewrite e1 oppr_le0.
  - by rewrite e2 /= lerN2.
have [Y [hY opt]] : exists Y : stT -> rat, (forall i, \sum_(I : stT) A i I * Y I <= b i) /\
    forall Y' : stT -> rat, (forall i, \sum_(I : stT) A i I * Y' I <= b i) ->
      \sum_(I : stT) (-1) * Y' I <= \sum_(I : stT) (-1) * Y I.
  apply: (@lp_max_fin _ _ A b (fun _ => -1)).
    exists (fun _ => 1); apply/feasE; split => // v.
    pose Iv : stT := exist _ [set v] (stable_set1 v).
    rewrite (bigD1 Iv) /=; last by rewrite inE.
    by rewrite lerDl sumr_ge0.
  exists 0 => Y /feasE [h _].
  under eq_bigr do rewrite mulN1r.
  by rewrite sumrN oppr_le0 sumr_ge0.
exists Y; split; first by apply/feasE.
move=> Y' /feasE /opt; under eq_bigr do rewrite mulN1r; under [X in _ <= X]eq_bigr do rewrite mulN1r.
by rewrite !sumrN lerN2.
Qed.

Lemma colouring_feas a b f : (0 < b)%N -> @bfold_colouring G a b f ->
  exists Y, cfeas Y /\ \sum_(I : stT) Y I = a%:Q / b%:Q.
Proof.
move=> b0 [cf df].
have stab (c : 'I_a) : stable [set v | c \in f v].
  apply/stableP => x y; rewrite !inE => cx cy; apply/negP => xy.
  by rewrite (disjointFr (df x y xy) cx) in cy.
pose col (c : 'I_a) : stT := exist (fun I : {set G} => stable I) _ (stab c).
pose Y (I : stT) := \sum_(c | col c == I) (b%:Q)^-1.
have bne : b%:Q != 0 by rewrite pnatr_eq0 -lt0n.
exists Y; split; first split.
- by move=> I; apply: sumr_ge0 => c _; rewrite invr_ge0 ler0n.
- move=> v; rewrite /Y (sum_fibres col (fun I : stT => v \in val I)) /=.
  under eq_bigl do rewrite inE.
  by rewrite sumr_const cf -mulr_natr mulVf.
- by rewrite /Y (sum_fibres col predT) sumr_const card_ord -mulr_natr mulrC.
Qed.

Lemma colouring_of Y : cfeas Y ->
  exists a b, [/\ (0 < b)%N, exists f, @bfold_colouring G a b f & \sum_(I : stT) Y I = a%:Q / b%:Q].
Proof.
move=> [Y0 Yc].
pose D : nat := \prod_(J : stT) `|denq (Y J)|%N.
pose k (I : stT) : nat := (`|numq (Y I)|%N * \prod_(J | J != I) `|denq (Y J)|%N)%N.
have D0 : (0 < D)%N by rewrite prodn_gt0 // => J; rewrite absz_gt0 denq_neq0.
have kE I : (k I)%:R = Y I * D%:R.
  rewrite /D (bigD1 I) //= /k !natrM mulrA; congr (_ * _).
  have hn : ((`|numq (Y I)|%N)%:R : rat) = (numq (Y I))%:~R.
    by rewrite natr_absz ger0_norm // numq_ge0.
  have hd : ((`|denq (Y I)|%N)%:R : rat) = (denq (Y I))%:~R.
    by rewrite natr_absz normr_denq.
  by rewrite hn hd numqE.
pose I0 : stT := exist _ set0 stable_set0.
pose s := flatten [seq nseq (k J) J | J <- enum {: stT}].
pose a := size s.
pose col (c : 'I_a) : stT := nth I0 s c.
have countE (Q : pred stT) : #|[set c : 'I_a | Q (col c)]| = (\sum_(J | Q J) k J)%N.
  rewrite -sum1_card (eq_bigl (fun c : 'I_a => Q (nth I0 s c))); last by move=> c; rewrite inE.
  have -> : (\sum_(c < a | Q (nth I0 s c)) 1 = \sum_(x <- s | Q x) 1)%N.
    by rewrite (big_nth I0) big_mkord.
  rewrite big_flatten big_map.
  rewrite [RHS]big_mkcond -[RHS]big_enum /=; apply: eq_bigr => J _.
  by rewrite sum1_count count_nseq; case: (Q J); rewrite ?mul1n ?mul0n.
pose C (v : G) := [set c : 'I_a | v \in val (col c)].
pose f (v : G) := [set c in take D (enum (C v))].
have hC v : (D <= #|C v|)%N.
  have -> : #|C v| = (\sum_(J : stT | v \in val J) k J)%N by exact: (countE (fun J : stT => v \in val J)).
  rewrite -(ler_nat rat) natr_sum; under eq_bigr do rewrite kE.
  by rewrite -mulr_suml -[X in X <= _]mul1r ler_pM2r ?ltr0n.
have fs v : f v \subset C v.
  by apply/subsetP => c; rewrite inE => /mem_take; rewrite mem_enum.
have fc v : #|f v| = D.
  rewrite cardsE; move/card_uniqP: (take_uniq D (enum_uniq (mem (C v)))) => ->.
  by rewrite size_takel // -cardE; exact: hC.
have ha : a = (\sum_J k J)%N.
  rewrite -(countE predT) -[in LHS](card_ord a) -cardsT; apply: eq_card => c.
  by rewrite !inE.
exists a, D; split => //.
  exists f; split => [v|x y xy]; first exact: fc.
  apply/pred0P => c /=; apply/negbTE/andP => [[cx cy]].
  have := subsetP (fs x) c cx; have := subsetP (fs y) c cy; rewrite !inE => hy hx.
  by move/stableP: (valP (col c)) => /(_ x y hx hy); rewrite xy.
rewrite ha -!pmulrn natr_sum; under [X in _ = X / _]eq_bigr do rewrite kE.
by rewrite -mulr_suml mulfK // pnatr_eq0 -lt0n.
Qed.

Lemma frac_chromatic_exists : exists xf, is_fractional_chromatic G xf.
Proof.
have [Y [hY opt]] := copt_exists.
have [a [b [b0 hf e]]] := colouring_of hY.
exists (a%:Q / b%:Q); split; first by exists a, b.
move=> a' b' b'0 [f' hf']; rewrite -e.
by have [Y' [hY' <-]] := colouring_feas b'0 hf'; exact: opt.
Qed.
End ChiF.

(** [chi_f >= n / alpha]: in an (a:b)-colouring the [a] colour classes are stable and
    cover every vertex [b] times, so [n * b <= a * alpha]. *)
Lemma bfold_n_alpha (G : sgraph) a b f : @bfold_colouring G a b f -> (#|G| * b <= a * α(G))%N.
Proof.
case=> cf df.
have stab (c : 'I_a) : stable [set v | c \in f v].
  apply/stableP => x y; rewrite !inE => cx cy; apply/negP => xy.
  by rewrite (disjointFr (df x y xy) cx) in cy.
have e : (#|G| * b = \sum_(c < a) #|[set v | c \in f v]|)%N.
  transitivity (\sum_(v : G) #|f v|)%N.
    by under eq_bigr => v _ do rewrite cf; rewrite sum_nat_const.
  under eq_bigr => v _ do rewrite -sum1_card big_mkcond.
  rewrite exchange_big; apply: eq_bigr => c _.
  by rewrite -sum1_card [RHS]big_mkcond; apply: eq_bigr => v _; rewrite inE.
rewrite e -alphaT -[X in (_ <= X * _)%N](card_ord a) -sum_nat_const.
apply: leq_sum => c _; apply: stabset_bound; apply/stabsetsP; split => //.
Qed.

Lemma frac_chi_n_alpha (G : sgraph) xf : is_fractional_chromatic G xf ->
  (#|G|)%:R <= xf * (α(G))%:R.
Proof.
case=> [[a [b [b0 [[f hf] ->]]]] _].
have := bfold_n_alpha hf; rewrite -(ler_nat rat) !natrM => h.
rewrite -!pmulrn mulrAC ler_pdivlMr ?ltr0n //.
Qed.
