(** * Chromatic.foundations.choice_number -- existence of the choice number ch(G)

    GTBase's [is_choice_number G m] is RELATIONAL ("m is choosable and minimal
    among the choosable k"), so every conjecture row that quantifies over a
    relationally specified choice number (X7's list-Reed row, U4's edge
    list-colouring row, U4's partial-list-colouring rows) can only be USED once
    one knows that such an [m] exists.  That existence is not obvious: [choosable
    G k] quantifies over an ARBITRARY finite palette [C], so it is a [Prop] with
    a [Type]-level quantifier and no [ex_minn] applies to it directly.

    This file removes that obstruction:

      [choosable_leqW]        -- [choosable] is monotone in the list size;
      [choosable_card]        -- every nonempty graph is [#|G|]-choosable
                                 (greedy system of distinct representatives);
      [choosable_exact]       -- lists of size EXACTLY [k] suffice;
      [list_colourable_inj]   -- transport of list-colourability backwards along
                                 an injection of the palette;
      [choosable_of_canon]    -- PALETTE CANONICALISATION: [k]-choosability
                                 follows from its instances over the single
                                 palette ['I_(k * #|G|)];
      [choosable_canonb]      -- that canonical instance as a BOOLEAN;
      [choosableP] / [choosable_canonbW] -- the two directions relating it to
                                 [choosable];
      [choice_number_ex]      -- hence [0 < #|G| -> exists ch, is_choice_number
                                 G ch], by [ex_minn] on the boolean.

    Only the canonical palette is quantified over in [choosable_canonb], and
    [{ffun G -> {set 'I_n}}] is a [finType], so the predicate is decidable and
    [ex_minn] applies.  Nothing here resolves any conjecture: these are facts
    about the list-colouring vocabulary itself. *)

From GTBase Require Import base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Two set-cardinality utilities ***************************************)

(** [size (index_enum T)] is [#|T|] -- [index_enum] is [Finite.enum] under a
    [locked_with]. *)
Lemma size_index_enumE (T : finType) : size (index_enum T) = #|T|.
Proof. by rewrite [index_enum T]unlock -enumT -cardT. Qed.

(** A union of [size s] sets of at most [k] elements has at most [k * size s]
    elements.  Stated in the CONSTANT form rather than as [#|bigcup| <= sum of
    the cards] followed by [eq_bigr]: the [eq_bigr] rewrite on this goal sends
    the unifier into a blowup (playbook entry 336). *)
Lemma card_bigcup_const_seq (I C : finType) (F : I -> {set C}) (k : nat)
    (s : seq I) :
  (forall i : I, #|F i| <= k) -> #|\bigcup_(i <- s) F i| <= k * size s.
Proof.
move=> hF; elim: s => [|a s IH]; first by rewrite big_nil cards0.
rewrite big_cons; apply: (leq_trans (_ : _ <= #|F a| + #|\bigcup_(i <- s) F i|)).
  by rewrite -cardsUI leq_addr.
by rewrite /= mulnS leq_add // hF.
Qed.

Lemma card_bigcup_const (I C : finType) (F : I -> {set C}) (k : nat) :
  (forall i : I, #|F i| <= k) -> #|\bigcup_(i : I) F i| <= k * #|I|.
Proof. by move=> hF; rewrite -size_index_enumE card_bigcup_const_seq. Qed.

(** A finite set has a subset of every size it can accommodate. *)
Lemma subset_of_card_rec (C : finType) (n : nat) :
  forall (m : nat) (A : {set C}),
    #|A| <= m -> n <= #|A| -> exists S : {set C}, (S \subset A) && (#|S| == n).
Proof.
elim=> [|m IH] A cardA le.
  have n0 : n = 0 by apply/eqP; rewrite -leqn0 (leq_trans le cardA).
  by exists set0; rewrite sub0set cards0 n0 eqxx.
case: (eqVneq #|A| n) => [e|ne]; first by exists A; rewrite subxx e eqxx.
have lt : n < #|A| by rewrite ltn_neqAle eq_sym ne le.
have [x xA] : exists x : C, x \in A.
  by apply/card_gt0P; exact: leq_ltn_trans (leq0n n) lt.
have cd : #|A| = 1 + #|A :\ x| by rewrite (cardsD1 x) xA.
have cardA' : #|A :\ x| <= m by move: cardA; rewrite cd add1n ltnS.
have le' : n <= #|A :\ x| by move: lt; rewrite cd add1n ltnS.
have [S /andP[sub cS]] := IH _ cardA' le'.
by exists S; rewrite cS andbT (subset_trans sub (subD1set A x)).
Qed.

Lemma subset_of_cardW (C : finType) (n : nat) (A : {set C}) :
  n <= #|A| -> exists S : {set C}, (S \subset A) && (#|S| == n).
Proof. exact: subset_of_card_rec (leqnn #|A|). Qed.

Section ChoiceNumber.
Variable G : sgraph.

(** ** Monotonicity of choosability **************************************)

Lemma choosable_leqW (k k' : nat) : k <= k' -> choosable G k -> choosable G k'.
Proof.
move=> le ch C L hL; apply: ch => v; exact: leq_trans le (hL v).
Qed.

(** ** Every nonempty graph is [#|G|]-choosable **************************)

(** A system of distinct representatives, built greedily along a [uniq] list:
    if every list has more than [#|D| + size s] colours, the vertices of [s] get
    pairwise distinct colours from their own lists, all outside [D]. *)
Lemma sdr_seq (C : finType) (L : G -> {set C}) (s : seq G) (D : {set C}) :
  uniq s -> (forall v : G, #|D| + size s <= #|L v|) ->
  exists g : G -> option C,
    (forall v : G, v \in s -> exists2 c, g v = Some c & c \in L v :\: D) /\
    {in s &, injective g}.
Proof.
elim: s D => [|a s IH] D uq hcard.
  by exists (fun _ => None); split => // v; rewrite in_nil.
have lt : #|D| < #|L a|.
  by apply: (leq_trans _ (hcard a)); rewrite /= addnS ltnS leq_addr.
have nsub : ~~ (L a \subset D).
  by apply/negP => sub; move: (subset_leq_card sub); rewrite leqNgt lt.
have [c cLa cD] := subsetPn nsub.
have [aNs us] : a \notin s /\ uniq s by move: uq; rewrite cons_uniq => /andP[].
have hcard' : forall v : G, #|c |: D| + size s <= #|L v|.
  move=> v; rewrite cardsU1 cD /= add1n addSn -addnS; exact: hcard v.
have [g' [hg' inj']] := IH (c |: D) us hcard'.
exists (fun z => if z == a then Some c else g' z); split.
  move=> v; rewrite inE => /orP[/eqP->|vs].
    by rewrite eqxx; exists c => //; rewrite !inE cD cLa.
  have vna : v != a by apply: contraTneq vs => ->.
  rewrite (negbTE vna); have [c'' e c''in] := hg' v vs; exists c'' => //.
  by move: c''in; rewrite !inE negb_or => /andP[/andP[_ nD] cLv]; rewrite nD cLv.
move=> u v uin vin e; move: uin vin e; rewrite !inE.
case/orP=> [/eqP->|us']; case/orP=> [/eqP->|vs'] //.
- rewrite eqxx; have vna : v != a by apply: contraTneq vs' => ->.
  rewrite (negbTE vna) => e.
  have [c'' e2 c''in] := hg' v vs'.
  move: c''in; rewrite e2 in e; case: e => <-.
  by rewrite !inE eqxx /=.
- have una : u != a by apply: contraTneq us' => ->.
  rewrite (negbTE una) eqxx => e.
  have [c'' e2 c''in] := hg' u us'.
  move: c''in; rewrite e2 in e; case: e => ->.
  by rewrite !inE eqxx /=.
have una : u != a by apply: contraTneq us' => ->.
have vna : v != a by apply: contraTneq vs' => ->.
by rewrite (negbTE una) (negbTE vna) => e; apply: inj'.
Qed.

Lemma choosable_card : 0 < #|G| -> choosable G #|G|.
Proof.
move=> pos C L hL.
have [v0 _] : exists v : G, v \in [set: G].
  by move: pos; rewrite -cardsT card_gt0 => /set0Pn.
have hmem : forall v : G, v \in enum [set: G] by move=> v; rewrite mem_enum inE.
have hcard : forall v : G, #|set0 : {set C}| + size (enum [set: G]) <= #|L v|.
  by move=> v; rewrite cards0 add0n -cardE cardsT; exact: hL v.
have [g [hg inj]] := @sdr_seq C L (enum [set: G]) set0 (enum_uniq _) hcard.
have [c0 _ _] := hg v0 (hmem v0).
pose f (v : G) : C := oapp id c0 (g v).
have fE : forall v : G, g v = Some (f v).
  by move=> v; have [c e _] := hg v (hmem v); rewrite /f e.
exists f; split.
  move=> v; have [c e cin] := hg v (hmem v).
  by move: cin; rewrite setD0 /f e.
move=> x y xy; apply/eqP => e.
have gxy : g x = g y by rewrite !fE e.
have := inj x y (hmem x) (hmem y) gxy => xyE.
by move: xy; rewrite xyE sg_irrefl.
Qed.

(** ** Lists of size exactly [k] suffice *********************************)

Lemma choosable_exact (k : nat) :
  (forall (C : finType) (L : G -> {set C}),
     (forall v : G, #|L v| = k) -> list_colourable L) ->
  choosable G k.
Proof.
move=> H C L hL.
have ex : forall v : G, exists S : {set C}, (S \subset L v) && (#|S| == k).
  by move=> v; apply: subset_of_cardW; exact: hL v.
pose L' (v : G) : {set C} := xchoose (ex v).
have L'P : forall v : G, (L' v \subset L v) && (#|L' v| == k).
  by move=> v; exact: (xchooseP (ex v)).
have szL' : forall v : G, #|L' v| = k.
  by move=> v; case/andP: (L'P v) => _ /eqP.
have [f [hf pf]] := H C L' szL'.
exists f; split => // v.
by case/andP: (L'P v) => /subsetP sub _; exact: (sub _ (hf v)).
Qed.

(** ** Transport of list-colourability along an injection of the palette **)

Lemma list_colourable_inj (C D : finType) (L : G -> {set C}) (iota : C -> D) :
  (forall v : G, {in L v &, injective iota}) ->
  list_colourable (fun v => iota @: L v) -> list_colourable L.
Proof.
move=> _ [f' [hf' pf']].
have ex_c : forall v : G, exists c : C, (c \in L v) && (iota c == f' v).
  by move=> v; have /imsetP[c cL e] := hf' v; exists c; rewrite cL /= e eqxx.
pose f (v : G) : C := xchoose (ex_c v).
have fP : forall v : G, (f v \in L v) && (iota (f v) == f' v).
  by move=> v; exact: (xchooseP (ex_c v)).
exists f; split; first by move=> v; case/andP: (fP v).
move=> x y xy; apply/eqP => e.
have /eqP ex : iota (f x) == f' x by case/andP: (fP x).
have /eqP ey : iota (f y) == f' y by case/andP: (fP y).
by move: (pf' x y xy); rewrite -ex -ey e eqxx.
Qed.

(** ** Palette canonicalisation ******************************************)

(** The union of [#|G|] lists of size [k] has at most [k * #|G|] colours, so it
    embeds into ['I_(k * #|G|)]: [k]-choosability over that FIXED palette, for
    lists of size exactly [k], already implies [k]-choosability. *)
Lemma choosable_of_canon (k : nat) : 0 < k -> 0 < #|G| ->
  (forall L : G -> {set 'I_(k * #|G|)},
     (forall v : G, #|L v| = k) -> list_colourable L) ->
  choosable G k.
Proof.
move=> kpos gpos H; apply: choosable_exact => C L hL.
have [v0 _] : exists v : G, v \in [set: G].
  by move: gpos; rewrite -cardsT card_gt0 => /set0Pn.
pose U : {set C} := \bigcup_(v : G) L v.
have subU : forall v : G, L v \subset U.
  by move=> v; apply/subsetP => c cL; apply/bigcupP; exists v.
have Ule : #|U| <= k * #|G|.
  by rewrite /U card_bigcup_const // => v; rewrite hL.
have [c00 c00U] : exists c : C, c \in U.
  have : 0 < #|L v0| by rewrite hL.
  by case/card_gt0P => c cL; exists c; apply: (subsetP (subU v0)).
pose iota (c : C) : 'I_(k * #|G|) := widen_ord Ule (enum_rank_in c00U c).
have iota_inj : {in U &, injective iota}.
  move=> c1 c2 c1U c2U e.
  have e2 : enum_rank_in c00U c1 = enum_rank_in c00U c2.
    by apply: val_inj; move: e => /(f_equal (@nat_of_ord _)).
  by rewrite -(enum_rankK_in c00U c1U) -(enum_rankK_in c00U c2U) e2.
have inj_v : forall v : G, {in L v &, injective iota}.
  move=> v c1 c2 c1L c2L; apply: iota_inj; exact: (subsetP (subU v)).
apply: (list_colourable_inj inj_v); apply: H => v.
by rewrite (card_in_imset (inj_v v)); exact: hL v.
Qed.

(** ** Choosability as a boolean *****************************************)

(** The canonical instance of [k]-choosability: over the single palette
    ['I_(k * #|G|)], for list assignments of size exactly [k].  Both the list
    assignments and the colourings range over [finType]s, so this is a genuine
    boolean. *)
Definition choosable_canonb (k : nat) : bool :=
  [forall L : {ffun G -> {set 'I_(k * #|G|)}},
     [forall v : G, #|L v| == k] ==>
     [exists f : {ffun G -> 'I_(k * #|G|)},
        [forall v : G, f v \in L v]
        && [forall x : G, [forall y : G, (x -- y) ==> (f x != f y)]]]].

(** [choosable] implies its canonical boolean instance (specialisation). *)
Lemma choosable_canonbW (k : nat) : choosable G k -> choosable_canonb k.
Proof.
move=> ch; apply/forallP => L; apply/implyP => /forallP hL.
have hL' : forall v : G, k <= #|L v| by move=> v; rewrite (eqP (hL v)).
have [f [hf pf]] := ch _ (fun v => L v) hL'.
apply/existsP; exists [ffun v => f v]; apply/andP; split.
  by apply/forallP => v; rewrite ffunE; exact: hf v.
apply/forallP => x; apply/forallP => y; apply/implyP => xy.
by rewrite !ffunE; exact: pf.
Qed.

(** ... and conversely, for a positive list size over a nonempty graph. *)
Lemma choosableP (k : nat) : 0 < k -> 0 < #|G| ->
  choosable_canonb k -> choosable G k.
Proof.
move=> kpos gpos /forallP cb; apply: choosable_of_canon => // L hL.
have /implyP := cb [ffun v => L v].
have hL' : [forall v : G, #|[ffun v => L v] v| == k].
  by apply/forallP => v; rewrite ffunE hL.
case/(_ hL')/existsP => f /andP[/forallP hf /forallP pf].
exists (fun v => f v); split.
  by move=> v; move: (hf v); rewrite ffunE.
by move=> x y xy; move: (forallP (pf x) y) => /implyP; apply.
Qed.

(** ** No graph with a vertex is [0]-choosable ***************************)

Lemma choosable_gt0 (k : nat) : 0 < #|G| -> choosable G k -> 0 < k.
Proof.
move=> gpos ch; case: (posnP k) => // k0.
have [v0 _] : exists v : G, v \in [set: G].
  by move: gpos; rewrite -cardsT card_gt0 => /set0Pn.
have hL : forall v : G, k <= #|(set0 : {set 'I_1})| by rewrite k0.
by have [f [hf _]] := ch 'I_1 (fun _ => set0) hL; move: (hf v0); rewrite inE.
Qed.

(** ** Existence of the choice number ************************************)

Theorem choice_number_ex : 0 < #|G| -> exists ch : nat, is_choice_number G ch.
Proof.
move=> gpos.
have ex : exists k : nat, (0 < k) && choosable_canonb k.
  exists #|G|; rewrite gpos /=.
  by apply: choosable_canonbW; exact: choosable_card.
case: (ex_minnP ex) => m /andP[mpos mb] Pmin.
exists m; split; first exact: choosableP mb.
move=> k ck; apply: Pmin; rewrite (choosable_gt0 gpos ck) /=.
by apply: choosable_canonbW.
Qed.

End ChoiceNumber.

Print Assumptions choosable_leqW.
Print Assumptions choosable_card.
Print Assumptions choosable_of_canon.
Print Assumptions choice_number_ex.
