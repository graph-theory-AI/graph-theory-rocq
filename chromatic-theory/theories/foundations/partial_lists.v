(** * Chromatic.foundations.partial_lists -- existence of lambda_t (partial list colouring)

    U4's [is_lambda G t lam] specifies lambda_t RELATIONALLY: [lam] is the
    minimum, over ALL finite palettes [C] and all assignments [L] of lists of
    size exactly [t], of the maximum number of [L]-colourable vertices
    ([colourable_count]).  As for the choice number (see [choice_number.v]) the
    minimum ranges over a [Type]-level quantifier, so its existence needs a
    palette canonicalisation.  This file provides:

      [lcob] / [lcobP]      -- [list_colourable_on L W] as a BOOLEAN (the partial
                               colouring ranges over the finType
                               [{ffun G -> option C}]);
      [muf] / [muf_count]   -- the maximum colourable count of a FIXED assignment,
                               as a [bigmax], and the fact that it satisfies
                               [colourable_count];
      [colourable_count_uniq] -- that count is unique;
      [lco_inj]             -- [list_colourable_on] is invariant under relabelling
                               the palette along a map injective on the colours
                               used (both directions; the backward one picks a
                               preimage with [pick], no choice axiom);
      [lambda_ex]           -- for [0 < t] and [0 < #|G|], [exists lam,
                               is_lambda G t lam]: every size-[t] assignment is
                               relabelled into the palette ['I_(t * #|G|)]
                               without changing its colourable sets, and the
                               minimum over the finitely many canonical
                               assignments is an [ex_minn].

    The vocabulary lives in U4.v and is reproduced by conversion only
    ([colourable_count] is re-stated here as [pl_count] with the same body, so
    this foundation file depends on no conjecture file). *)

From GTBase Require Import base.
From Chromatic.foundations Require Import choice_number.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section PartialLists.
Variable G : sgraph.

(** Same body as U4's [colourable_count]. *)
Definition pl_count (C : finType) (L : G -> {set C}) (mu : nat) : Prop :=
  (exists W : {set G}, list_colourable_on L W /\ #|W| = mu) /\
  (forall W : {set G}, list_colourable_on L W -> #|W| <= mu).

(** Same body as U4's [is_lambda]. *)
Definition pl_lambda (t lam : nat) : Prop :=
  (exists (C : finType) (L : G -> {set C}),
      (forall v : G, #|L v| = t) /\ pl_count L lam) /\
  (forall (C : finType) (L : G -> {set C}) (mu : nat),
      (forall v : G, #|L v| = t) -> pl_count L mu -> lam <= mu).

Definition lcob (C : finType) (L : G -> {set C}) (W : {set G}) : bool :=
  [exists f : {ffun G -> option C},
     [forall v in W, [exists c in L v, f v == Some c]] &&
     [forall x in W, [forall y in W, (x -- y) ==> (f x != f y)]]].

Lemma lcobP (C : finType) (L : G -> {set C}) (W : {set G}) :
  reflect (list_colourable_on L W) (lcob L W).
Proof.
apply: (iffP existsP) => [[f /andP[/forall_inP hf /forall_inP pf]]|[f [hf pf]]].
  exists (fun v => f v); split.
    by move=> v vW; have /exists_inP[c cL /eqP e] := hf v vW; exists c.
  by move=> x y xW yW xy; move/forall_inP: (pf x xW) => /(_ y yW) /implyP; apply.
exists [ffun v => f v]; apply/andP; split.
  apply/forall_inP => v vW; have [c [e cL]] := hf v vW.
  by apply/exists_inP; exists c => //; rewrite ffunE e.
apply/forall_inP => x xW; apply/forall_inP => y yW; apply/implyP => xy.
by rewrite !ffunE; exact: pf.
Qed.

Lemma lcob0 (C : finType) (L : G -> {set C}) : lcob L set0.
Proof. by apply/lcobP; exists (fun _ => None); split => v; rewrite inE. Qed.

Definition muf (C : finType) (L : G -> {set C}) : nat :=
  \max_(W : {set G} | lcob L W) #|W|.

Lemma muf_count (C : finType) (L : G -> {set C}) : pl_count L (muf L).
Proof.
have h0 := lcob0 L.
split; last by move=> W /lcobP hW; rewrite /muf;
  exact: (@leq_bigmax_cond _ (fun W => lcob L W) (fun W => #|W|) W hW).
exists [arg max_(W > set0 | lcob L W) #|W|]; split.
  by apply/lcobP; case: arg_maxnP.
by rewrite /muf (bigmax_eq_arg _ h0).
Qed.

Lemma pl_count_uniq (C : finType) (L : G -> {set C}) (m m' : nat) :
  pl_count L m -> pl_count L m' -> m = m'.
Proof.
move=> [[W [hW <-]] ub] [[W' [hW' <-]] ub'].
by apply/eqP; rewrite eqn_leq ub' // ub.
Qed.

(** ** Relabelling the palette *******************************************)

Lemma lco_inj (C D : finType) (L : G -> {set C}) (iota : C -> D) (U : {set C}) :
  {in U &, injective iota} -> (forall v : G, L v \subset U) ->
  forall W : {set G},
    list_colourable_on L W <-> list_colourable_on (fun v => iota @: L v) W.
Proof.
move=> inj sub W; split.
  move=> [f [hf pf]]; exists (fun v => omap iota (f v)); split.
    move=> v vW; have [c [e cL]] := hf v vW.
    by exists (iota c); rewrite e /=; split => //; apply: imset_f.
  move=> x y xW yW xy; have := pf x y xW yW xy.
  have [cx [ex cxL]] := hf x xW; have [cy [ey cyL]] := hf y yW.
  rewrite ex ey /=; apply: contra => /eqP [] ei; apply/eqP; congr Some.
  by apply: inj => //; [exact: (subsetP (sub x)) | exact: (subsetP (sub y))].
move=> [f' [hf' pf']].
pose g (v : G) : option C :=
  if f' v is Some d then [pick c in L v | iota c == d] else None.
have gP : forall v, v \in W -> exists2 c, g v = Some c & (c \in L v) && (iota c == oapp id (iota c) (f' v)).
  move=> v vW; have [d [e dL]] := hf' v vW.
  rewrite /g e; case: pickP => [c /andP[cL /eqP cd]|none].
    by exists c => //; rewrite cL cd /= eqxx.
  by case/imsetP: dL => c cL cd; move: (none c); rewrite cL cd eqxx.
exists g; split.
  by move=> v vW; have [c e /andP[cL _]] := gP v vW; exists c.
move=> x y xW yW xy; have := pf' x y xW yW xy.
have [dx [edx _]] := hf' x xW; have [dy [edy _]] := hf' y yW.
have [cx ex /andP[_]] := gP x xW; have [cy ey /andP[_]] := gP y yW.
rewrite edx edy /= ex ey => /eqP iy /eqP ix.
by apply: contra => /eqP [] cxy; rewrite -ix -iy cxy.
Qed.

(** ** Existence of lambda_t *********************************************)

Definition canon_ok (t m : nat) : bool :=
  [exists L : {ffun G -> {set 'I_(t * #|G|)}},
     [forall v : G, #|L v| == t] && (muf L == m)].

Lemma lambda_ex (t : nat) : 0 < t -> 0 < #|G| -> exists lam, pl_lambda t lam.
Proof.
move=> tpos gpos.
have tle : t <= #|[set: 'I_(t * #|G|)]| by rewrite cardsT card_ord leq_pmulr.
have [S /andP[_ /eqP cS]] := subset_of_cardW tle.
have ex : exists m, canon_ok t m.
  exists (muf [ffun _ : G => S]); apply/existsP; exists [ffun _ : G => S].
  by rewrite eqxx andbT; apply/forallP => v; rewrite ffunE cS.
case: (ex_minnP ex) => lam /existsP[L0 /andP[/forallP hL0 /eqP mL0]] lmin.
exists lam; split.
  exists 'I_(t * #|G|), (fun v => L0 v); split; first by move=> v; apply/eqP.
  by rewrite -mL0; exact: muf_count.
move=> C L mu hL cnt; apply: lmin.
have [v0 _] : exists v : G, v \in [set: G].
  by move: gpos; rewrite -cardsT card_gt0 => /set0Pn.
pose U : {set C} := \bigcup_(v : G) L v.
have subU : forall v : G, L v \subset U.
  by move=> v; apply/subsetP => c cL; apply/bigcupP; exists v.
have Ule : #|U| <= t * #|G| by rewrite /U card_bigcup_const // => v; rewrite hL.
have [c00 c00U] : exists c : C, c \in U.
  have : 0 < #|L v0| by rewrite hL.
  by case/card_gt0P => c cL; exists c; apply: (subsetP (subU v0)).
pose iota (c : C) : 'I_(t * #|G|) := widen_ord Ule (enum_rank_in c00U c).
have iota_inj : {in U &, injective iota}.
  move=> c1 c2 c1U c2U e.
  have e2 : enum_rank_in c00U c1 = enum_rank_in c00U c2.
    by apply: val_inj; move: e => /(f_equal (@nat_of_ord _)).
  by rewrite -(enum_rankK_in c00U c1U) -(enum_rankK_in c00U c2U) e2.
pose L' := [ffun v => iota @: L v].
have L'E : forall v, L' v = iota @: L v by move=> v; rewrite ffunE.
have tr : forall W, list_colourable_on L W <-> list_colourable_on (fun v => L' v) W.
  move=> W; rewrite (lco_inj iota_inj subU W).
  by split; move=> [f [hf pf]]; exists f; split => // v vW;
     [rewrite L'E | rewrite -L'E]; exact: hf.
have cnt' : pl_count (fun v => L' v) mu.
  case: cnt => [[W [hW cW]] ub]; split; first by exists W; split => //; apply/tr.
  by move=> W2 /tr; exact: ub.
apply/existsP; exists L'; apply/andP; split.
  apply/forallP => v; rewrite L'E card_in_imset ?hL //.
  by move=> c1 c2 c1L c2L; apply: iota_inj; exact: (subsetP (subU v)).
by rewrite (pl_count_uniq (muf_count (fun v => L' v)) cnt').
Qed.

(** A [k]-choosable graph has every size-[k] assignment colouring everything,
    so any lambda witness at [k] is [#|G|]. *)
Lemma pl_lambda_choosable (k lam : nat) : choosable G k -> pl_lambda k lam -> lam = #|G|.
Proof.
move=> ch [[C [L [hL cnt]]] _].
have full : list_colourable_on L [set: G].
  have [f [hf pf]] := ch C L (fun v => eq_leq (esym (hL v))).
  by exists (fun v => Some (f v)); split=> [v _|x y _ _ xy]; [exists (f v) | rewrite (inj_eq (@Some_inj _)) pf].
case: cnt => [[W [_ <-]] ub]; apply/eqP; rewrite eqn_leq max_card /=.
by rewrite -cardsT; exact: ub.
Qed.

End PartialLists.

Print Assumptions lambda_ex.
Print Assumptions pl_lambda_choosable.
