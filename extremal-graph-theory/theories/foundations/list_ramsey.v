(** Finite counting proof of the chromatic-family list Ramsey equality.
    Source: Fox--He--Luo--Xu, arXiv:2103.15175, Section 3.1. *)
From mathcomp Require Import all_boot.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition lr_agree (C Y : finType) (S : {set C}) (a : C -> Y) :=
  [set f : {ffun C -> Y} | [forall c in S, f c == a c]].

Lemma lr_agree_card (C Y : finType) (S : {set C}) (a : C -> Y) :
  #|lr_agree S a| = #|Y| ^ #|~: S|.
Proof.
pose F c : pred Y := if c \in S then pred1 (a c) else predT.
have E : #|lr_agree S a| = #|family F|.
  apply: eq_card => f; rewrite inE.
  apply/forallP/forallP => H c.
  - rewrite /F /=; case cS: (c \in S); last done.
    move: (H c); by rewrite cS implyTb.
  - move: (H c); rewrite /F /=; by case: (c \in S).
rewrite E card_family.
have cf c : #|F c| = if c \in S then 1 else #|Y|.
  by rewrite /F; case: (c \in S); rewrite ?card1 ?cardT.
rewrite /image_mem (eq_map cf).
rewrite cardE /enum_mem -enumT size_filter.
elim: (enum C) => [|c cs IH] //=.
rewrite inE; case: (c \in S); by rewrite /= ?mul1n ?expnS IH.
Qed.

Lemma lr_union_bound (Y : finType) (xs : seq {set Y}) :
  #|foldr (@setU _) set0 xs| <= \sum_(B <- xs) #|B|.
Proof.
elim: xs => [|B bs IH]; first by rewrite /= cards0 big_nil.
rewrite /= big_cons cardsU.
exact: leq_trans (leq_subr _ _) (leq_add (leqnn _) IH).
Qed.

Lemma lr_union_mem (Y : finType) (x : Y) (xs : seq {set Y}) :
  (x \in foldr (@setU _) set0 xs) = has (fun B : {set Y} => x \in B) xs.
Proof. by elim: xs => [|B bs IH] /=; rewrite ?inE ?IH. Qed.

Lemma lr_pick_label (I C Y : finType) (A : {set I})
    (S : I -> {set C}) (a : I -> C -> Y) (k : nat) :
  0 < #|Y| -> (forall i, i \in A -> #|S i| = k) ->
  #|A| < #|Y| ^ k ->
  exists b : {ffun C -> Y},
    forall i, i \in A -> exists c, c \in S i /\ b c != a i c.
Proof.
move=> Ypos Sk Ak.
case A0: (A == set0).
  have /card_gt0P [y _] := Ypos.
  exists [ffun _ => y] => i.
  by move/eqP: A0 => ->; rewrite inE.
have /set0Pn [i iA] := negbT A0.
have kC : k <= #|C| by rewrite -(Sk i iA); exact: max_card.
pose B i := lr_agree (S i) (a i).
pose U := foldr (@setU _) set0 [seq B i | i <- enum A].
have cb j : j \in A -> #|B j| = #|Y| ^ (#|C| - k).
  move=> jA; rewrite /B lr_agree_card.
  congr (_ ^ _); rewrite cardsCs setCK Sk //.
have Ub : #|U| <= #|A| * (#|Y| ^ (#|C| - k)).
  apply: leq_trans (lr_union_bound _) _.
  rewrite big_map (eq_big_seq (fun _ => #|Y| ^ (#|C| - k))).
  - by rewrite big_const_seq count_predT -cardE iter_addn addn0 mulnC.
  - by move=> j; rewrite mem_enum; exact: cb.
have Ul : #|U| < #|{ffun C -> Y}|.
  apply: leq_ltn_trans Ub _.
  rewrite card_ffun -[in X in _ < X](subnK kC) expnD.
  by rewrite [#|A| * _]mulnC ltn_mul2l expn_gt0 Ypos /= Ak.
have Uc : 0 < #|~: U|.
  by rewrite -(ltn_add2l #|U|) addn0 cardsC.
have /card_gt0P [b bU] := Uc.
exists b => j jA.
have bB : b \notin B j.
  move: bU; rewrite inE /U lr_union_mem has_map.
  move/hasPn=> H; apply: H; by rewrite mem_enum.
move: bB; rewrite /B /lr_agree inE negb_forall.
move/existsP=> [c]; rewrite negb_imply => /andP [cS ne].
by exists c.
Qed.

Definition lr_separates (V C Y : finType) (L : V -> V -> {set C})
    (f : V -> {ffun C -> Y}) (vs : seq V) : Prop :=
  forall x y, x \in vs -> y \in vs -> x != y ->
    exists c, c \in L x y /\ f x c != f y c.

Lemma lr_separation_seq (V C Y : finType) (L : V -> V -> {set C})
    (k : nat) (vs : seq V) :
  0 < #|Y| -> (forall x y, L x y = L y x) ->
  (forall x y, x != y -> #|L x y| = k) ->
  uniq vs -> size vs <= #|Y| ^ k ->
  exists f : V -> {ffun C -> Y}, lr_separates L f vs.
Proof.
move=> Ypos Lsym Lcard.
elim: vs => [|x xs IH] /=.
  move=> _ _; have /card_gt0P [y _] := Ypos.
  exists (fun _ => [ffun _ => y]).
  by move=> u v.
move=> /andP [xnot Uxs] bound.
have tailbound : size xs <= #|Y| ^ k := leq_trans (leqnSn _) bound.
have [f Hf] := IH Uxs tailbound.
pose A := [set v : V | v \in xs].
have Acard : #|A| = size xs.
  rewrite /A cardsE; exact/card_uniqP.
have cardS v : v \in A -> #|L x v| = k.
  rewrite inE => vx; apply: Lcard.
  apply/eqP=> xv; subst v; by rewrite vx in xnot.
have Abound : #|A| < #|Y| ^ k by rewrite Acard.
have [b Hb] := lr_pick_label (fun v => f v) Ypos cardS Abound.
exists (fun v => if v == x then b else f v).
move=> u v; rewrite !inE.
move=> /orP [/eqP ->|ux] /orP [/eqP ->|vx] ne.
- by rewrite eqxx in ne.
- have /Hb [c [cL cn]] : v \in A by rewrite inE.
  exists c; split=> //.
  by rewrite eqxx (eq_sym v x) (negbTE ne).
- have /Hb [c [cL cn]] : u \in A by rewrite inE.
  exists c; split; first by rewrite Lsym.
  by rewrite eqxx (negbTE ne) eq_sym.
- have unx : u != x by apply/eqP=> uxE; subst u; rewrite ux in xnot.
  have vnx : v != x by apply/eqP=> vxE; subst v; rewrite vx in xnot.
  have [c [cL cn]] := Hf u v ux vx ne.
  exists c; split=> //.
  by rewrite (negbTE unx) (negbTE vnx).
Qed.

Theorem lr_separation (V C : finType) (L : V -> V -> {set C}) (s k : nat) :
  0 < s -> (forall x y, L x y = L y x) ->
  (forall x y, x != y -> #|L x y| = k) -> #|V| <= s ^ k ->
  exists f : V -> {ffun C -> 'I_s},
    forall x y, x != y -> exists c, c \in L x y /\ f x c != f y c.
Proof.
move=> spos Lsym Lcard bound.
have Ypos : 0 < #|'I_s| by rewrite card_ord.
have bound' : size (enum V) <= #|'I_s| ^ k by rewrite -cardT card_ord.
have [f Hf] := lr_separation_seq Ypos Lsym Lcard (enum_uniq V) bound'.
exists f => x y xy; apply: Hf xy; by rewrite mem_enum.
Qed.

(** Lists are attached to unordered edges: symmetry is explicit and diagonal
    values have no mathematical role. *)
Definition lr_valid_lists (V C : finType) (k : nat) (L : V -> V -> {set C}) : Prop :=
  (forall x y, L x y = L y x) /\
  forall x y, x != y -> #|L x y| = k.
Definition lr_admissible (V C : finType) (L : V -> V -> {set C})
    (phi : V -> V -> C) : Prop :=
  (forall x y, phi x y = phi y x) /\
  forall x y, x != y -> phi x y \in L x y.
Definition lr_avoids (V C : finType) (s : nat) (phi : V -> V -> C) : Prop :=
  exists f : V -> {ffun C -> 'I_s},
    forall x y, x != y -> f x (phi x y) != f y (phi x y).

Theorem lr_avoiding_coloring (V C : finType) (c0 : C)
    (L : V -> V -> {set C}) (s k : nat) :
  0 < s -> lr_valid_lists k L -> #|V| <= s ^ k ->
  exists phi, lr_admissible L phi /\ lr_avoids s phi.
Proof.
move=> spos [Lsym Lcard] bound.
have [f Hf] := lr_separation spos Lsym Lcard bound.
pose good x y c := (c \in L x y) && (f x c != f y c).
pose phi x y := odflt c0 (pick (good x y)).
have phisym x y : phi x y = phi y x.
  rewrite /phi; congr (odflt _ _); apply: eq_pick => c.
  by rewrite /good Lsym eq_sym.
have phigood x y : x != y -> good x y (phi x y).
  move=> xy; rewrite /phi.
  case: pickP => [c gc|bad] //=.
  have [c [cL cn]] := Hf x y xy.
  by move: (bad c); rewrite /good cL cn.
exists phi; split.
- split=> // x y xy; have /andP[h _] := phigood x y xy; exact: h.
- exists f => x y xy; have /andP[_ h] := phigood x y xy; exact: h.
Qed.

Theorem lr_product_bound (V C : finType) (s : nat) (phi : V -> V -> C) :
  lr_avoids s phi -> #|V| <= s ^ #|C|.
Proof.
move=> [f hf].
have injf : injective f.
  move=> x y ef; apply/eqP; apply/negPn/negP=> xy.
  by have := hf x y xy; rewrite ef eqxx.
by have := leq_card f injf; rewrite card_ffun card_ord.
Qed.

(** A forcing assignment may use any finite, nonempty palette. A nonempty
    palette permits harmless diagonal values even when the graph has no edges. *)
Definition lr_forces (s k n : nat) : Prop :=
  exists q : nat, 0 < q /\
    exists L : 'I_n -> 'I_n -> {set 'I_q},
      lr_valid_lists k L /\
      forall phi, lr_admissible L phi -> ~ lr_avoids s phi.

(** The least-number characterization avoids assuming an unbounded decidable
    search or defining a number before its existence has been proved. *)
Definition lr_is_number (s k r : nat) : Prop :=
  lr_forces s k r /\ forall n, lr_forces s k n -> r <= n.

Definition list_ramsey_chromatic_statement : Prop :=
  forall s k : nat, 2 <= s -> 0 < k -> lr_is_number s k (s ^ k).+1.

Theorem list_ramsey_chromatic : list_ramsey_chromatic_statement.
Proof.
move=> s k s2 kpos.
have spos : 0 < s := ltn_trans (ltnSn 0) s2.
split.
- exists k; split=> //.
  exists (fun _ _ => [set: 'I_k]); split.
  + split=> // x y _; by rewrite cardsT card_ord.
  + move=> phi _ hav.
    have h := lr_product_bound hav.
    by rewrite !card_ord ltnn in h.
- move=> n [q [qpos [L [valid forcing]]]].
  case: (leqP (s ^ k).+1 n) => // bound.
  have vn : #|'I_n| <= s ^ k by rewrite card_ord; exact: bound.
  have [phi [legal avoid]] := lr_avoiding_coloring (Ordinal qpos) spos valid vn.
  exfalso; exact: forcing phi legal avoid.
Qed.
