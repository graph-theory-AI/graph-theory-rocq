(** A9 cut sizes: the frozen X209 cut-edge test and coloured cut count, its three chains and its row.
    Baseline, hashes and exact substitutions are recorded in meta/migration_reports/cut_size.spec.json.
    The cut count is over an ARBITRARY supplied family and colour map; no uniformity, nonemptiness or
    palette premise is added.  The minimum's documented carrier defect is frozen verbatim: it binds a
    fresh [T'] but its [E'] ranges over families on the OUTER carrier [T], so [T'] is unused.
    X209 RE-ENCODING (2026-10-26, coordination/PROGRAMME.md A2 with the A4 direction re-encode; record
    meta/STATEMENT_IMPROVEMENTS.md): the live row now uses the source's multicoloured cut, the baseline S(k,r) r!/r^k
    and a minimum over every vertex type.  Neither row implies the other; its certificate states only the placeholder
    relation the gate accepts, and the two defects are the named lemmas [x209_old_min_not_minimal] and
    [x209_cut_defect] at the end of this file.  The other certificates keep their exact iffs. *)
From Corelib Require Import Setoid Morphisms.
From GTBase Require Import base.
From Hypergraph.conjectures Require Import X209.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

#[local] Instance and3_iff_morphism : Proper (iff ==> iff ==> iff ==> iff) and3.
Proof. by move=> a a' ha b b' hb c c' hc; split=> -[x y z]; split; by [apply/ha|apply/hb|apply/hc]. Qed.

#[local] Instance and4_iff_morphism : Proper (iff ==> iff ==> iff ==> iff ==> iff) and4.
Proof.
by move=> a a' ha b b' hb c c' hc d d' hd; split=> -[x y z w]; split;
  by [apply/ha|apply/hb|apply/hc|apply/hd].
Qed.

Module Legacy.

Definition x209_cut_edge
    (T : finType) (r : nat) (col : T -> 'I_r) (e : {set T}) : bool :=
  [exists x in e, [exists y in e, col x != col y]].

Definition x209_cut_size
    (T : finType) (E : {set {set T}}) (r : nat) (col : T -> 'I_r) : nat :=
  #|[set e in E | Legacy.x209_cut_edge col e]|.

End Legacy.

Module X209Legacy.

Definition is_max_r_cut
    (T : finType) (E : {set {set T}}) (r c : nat) : Prop :=
  exists col : T -> 'I_r,
    Legacy.x209_cut_size E col = c /\
    forall col' : T -> 'I_r, Legacy.x209_cut_size E col' <= c.

Definition scaled_excess
    (T : finType) (E : {set {set T}}) (r k x : nat) : Prop :=
  exists c : nat,
    is_max_r_cut E r c /\
    x = x209_expected_den r k * c - (x209_expected_den r k).-1 * #|E|.

Definition is_min_scaled_excess (r k m x : nat) : Prop :=
  exists (T : finType) (E : {set {set T}}),
    [/\ x209_uniform E k, #|E| = m, scaled_excess E r k x &
        forall (T' : finType) (E' : {set {set T}}) (y : nat),
          x209_uniform E' k ->
          #|E'| = m ->
          scaled_excess E' r k y ->
          x <= y].

Definition hypergraph_cut_excess_theta_sqrt_statement : Prop :=
  forall r k : nat,
    2 <= r ->
    r <= k ->
    exists excess : nat -> nat,
      (forall m : nat, is_min_scaled_excess r k m (excess m)) /\
      big_Theta_nat (fun m => (excess m) ^ 2) (fun m => m).

End X209Legacy.

(** Not a conversion: the existential pair of differently coloured elements is the negated
    monochromatic predicate of C8 ([non_monochromatic_onP]). *)
Lemma x209_cut_edge_compat (T : finType) (r : nat) (col : T -> 'I_r) (e : {set T}) :
  Legacy.x209_cut_edge col e = x209_cut_edge col e.
Proof.
apply/idP/non_monochromatic_onP => [/existsP[x /andP[xe /existsP[y /andP[ye xy]]]]|[x [y [xe ye xy]]]].
  by exists x, y.
by apply/existsP; exists x; rewrite xe; apply/existsP; exists y; rewrite ye.
Qed.

Lemma x209_cut_size_compat (T : finType) (E : {set {set T}}) (r : nat) (col : T -> 'I_r) :
  Legacy.x209_cut_size E col = x209_cut_size E col.
Proof.
rewrite /Legacy.x209_cut_size /x209_cut_size /non_monochromatic_count.
by apply: eq_card => e; rewrite !inE x209_cut_edge_compat.
Qed.

Lemma x209_is_max_r_cut_compat (T : finType) (E : {set {set T}}) (r c : nat) :
  @X209Legacy.is_max_r_cut T E r c <-> @x209_is_max_r_cut T E r c.
Proof. rewrite /X209Legacy.is_max_r_cut /x209_is_max_r_cut; setoid_rewrite x209_cut_size_compat; reflexivity. Qed.

Lemma x209_scaled_excess_compat (T : finType) (E : {set {set T}}) (r k x : nat) :
  @X209Legacy.scaled_excess T E r k x <-> @x209_scaled_excess T E r k x.
Proof. rewrite /X209Legacy.scaled_excess /x209_scaled_excess; setoid_rewrite x209_is_max_r_cut_compat; reflexivity. Qed.

Lemma x209_is_min_scaled_excess_compat (r k m x : nat) :
  @X209Legacy.is_min_scaled_excess r k m x <-> @x209_is_min_scaled_excess r k m x.
Proof. rewrite /X209Legacy.is_min_scaled_excess /x209_is_min_scaled_excess; setoid_rewrite x209_scaled_excess_compat; reflexivity. Qed.

(** X209 RE-ENCODING (2026-10-26, PROGRAMME A2 + A4 re-encode; record meta/STATEMENT_IMPROVEMENTS.md), not a
    migration equivalence.  The frozen and the live rows imply each other in neither direction: the cuts differ for
    r >= 3 ([x209_cut_defect]) and the frozen minimum ranges over one vertex type ([x209_old_min_not_minimal]).  The
    type below is the placeholder relation of the spec's repair entry, not a claim. *)
Lemma hypergraph_cut_excess_theta_sqrt_statement_compat :
  (X209Legacy.hypergraph_cut_excess_theta_sqrt_statement -> True) /\ (hypergraph_cut_excess_theta_sqrt_statement -> True).
Proof. by split. Qed.

(** ** X209 re-encoding: the two defects, kernel-checked *)

(* a maximum cut is unique *)
Lemma x209_max_cut_unique (T : finType) (E : {set {set T}}) (r c c' : nat) :
  x209_is_max_r_cut E r c -> x209_is_max_r_cut E r c' -> c = c'.
Proof.
move=> [f [<- hf]] [g [<- hg]].
by apply/eqP; rewrite eqn_leq hg hf.
Qed.

(* On five vertices, a 3-uniform family missing some triple t is cut entirely by t versus the rest. *)
Lemma x209_five_cut_all (E : {set {set 'I_5}}) (t : {set 'I_5}) :
  x209_uniform E 3 -> #|t| = 3 -> t \notin E ->
  x209_cut_size E (fun v : 'I_5 => if v \in t then (ord0 : 'I_2) else ord_max) = #|E|.
Proof.
move=> hE ht tE.
rewrite /x209_cut_size /non_monochromatic_count.
apply: eq_card => e; rewrite inE.
case eE: (e \in E) => //=.
apply/negP => /monochromatic_onP hm.
have he := hE e eE.
have [v ve] : exists v, v \in e by apply/set0Pn; rewrite -card_gt0 he.
have hne : (ord0 : 'I_2) != ord_max by [].
case vt: (v \in t).
- have sub : e \subset t.
    apply/subsetP => w we; have := hm v w ve we; rewrite vt.
    by case: (w \in t) => // h; move: hne; rewrite h eqxx.
  have : e = t by apply/eqP; rewrite eqEcard sub he ht.
  by move=> eq; move: tE; rewrite -eq eE.
- have sub : e \subset ~: t.
    apply/subsetP => w we; rewrite inE; have := hm v w ve we; rewrite vt.
    by case: (w \in t) => // h; move: hne; rewrite h eqxx.
  have := subset_leq_card sub.
  have := cardsC t; rewrite card_ord ht he => h.
  have -> : #|~: t| = 2 by apply/eqP; rewrite -(eqn_add2l 3) h.
  by [].
Qed.

Lemma x209_triples_five : #|[set A : {set 'I_5} | #|A| == 3]| = 10.
Proof. by rewrite card_draws card_ord. Qed.

(* every 3-uniform family of at most nine triples on five vertices misses a triple *)
Lemma x209_five_missing (E : {set {set 'I_5}}) :
  x209_uniform E 3 -> #|E| <= 9 -> exists t : {set 'I_5}, #|t| = 3 /\ t \notin E.
Proof.
move=> hE hm.
have : ~~ ([set A : {set 'I_5} | #|A| == 3] \subset E).
  apply/negP => /subset_leq_card; rewrite x209_triples_five.
  by move=> h; have := leq_trans h hm.
case/subsetPn => t; rewrite inE => /eqP ht tE.
by exists t.
Qed.

Lemma x209_five_max_cut (E : {set {set 'I_5}}) :
  x209_uniform E 3 -> #|E| <= 9 -> x209_is_max_r_cut E 2 #|E|.
Proof.
move=> hE hm; have [t [ht tE]] := x209_five_missing hE hm.
exists (fun v : 'I_5 => if v \in t then (ord0 : 'I_2) else ord_max); split.
  exact: x209_five_cut_all.
by move=> col; exact: non_monochromatic_count_le.
Qed.

Lemma x209_five_excess (E : {set {set 'I_5}}) (y : nat) :
  x209_uniform E 3 -> #|E| <= 9 -> x209_scaled_excess E 2 3 y -> y = #|E|.
Proof.
move=> hE hm [c [hc ->]].
rewrite (x209_max_cut_unique hc (x209_five_max_cut hE hm)) /x209_expected_den /=.
by rewrite mulSn addnK.
Qed.

(* The witness: on five vertices, x = 7 passes the old minimality test, whose competitors live on the same type. *)
Lemma x209_seven_triples_five : exists E : {set {set 'I_5}}, x209_uniform E 3 /\ #|E| = 7.
Proof.
pose D := [set A : {set 'I_5} | #|A| == 3].
have hD : #|D| = 10 by rewrite /D card_draws card_ord.
exists [set A in take 7 (enum D)]; split.
  by move=> e; rewrite inE => /mem_take; rewrite mem_enum inE => /eqP.
rewrite cardsE.
have /card_uniqP -> : uniq (take 7 (enum D)) by apply: take_uniq; apply: enum_uniq.
by rewrite size_take -cardE hD.
Qed.

Lemma x209_old_min_seven : x209_is_min_scaled_excess 2 3 7 7.
Proof.
have [E [hE h7]] := x209_seven_triples_five.
have h9 : #|E| <= 9 by rewrite h7.
exists 'I_5, E; split=> //.
  by exists 7; split; [rewrite -h7; exact: x209_five_max_cut | rewrite h7].
by move=> _ E' y hE' h7' hy; rewrite (x209_five_excess hE' _ hy) h7'.
Qed.

(* The Fano plane on 'I_7: the lines {i, i+1, i+3} mod 7, written out. *)
Definition x209_o0 : 'I_7 := @Ordinal 7 0 isT.
Definition x209_o1 : 'I_7 := @Ordinal 7 1 isT.
Definition x209_o2 : 'I_7 := @Ordinal 7 2 isT.
Definition x209_o3 : 'I_7 := @Ordinal 7 3 isT.
Definition x209_o4 : 'I_7 := @Ordinal 7 4 isT.
Definition x209_o5 : 'I_7 := @Ordinal 7 5 isT.
Definition x209_o6 : 'I_7 := @Ordinal 7 6 isT.

Definition x209_fano_lines : seq {set 'I_7} :=
  [:: [set x209_o0; x209_o1; x209_o3]; [set x209_o1; x209_o2; x209_o4]; [set x209_o2; x209_o3; x209_o5]; [set x209_o3; x209_o4; x209_o6];
      [set x209_o4; x209_o5; x209_o0]; [set x209_o5; x209_o6; x209_o1]; [set x209_o6; x209_o0; x209_o2]].

Definition x209_fano : {set {set 'I_7}} := [set e in x209_fano_lines].

Lemma x209_fano_lines_uniq : uniq x209_fano_lines.
Proof.
rewrite /x209_fano_lines /= !inE !negb_or.
have d (x : 'I_7) (A B : {set 'I_7}) : x \in A -> x \notin B -> A != B.
  by move=> xA xB; apply/eqP => AB; move: xB; rewrite -AB xA.
repeat (apply/andP; split); first [ by [] | by apply: (d x209_o0); rewrite !inE
  | by apply: (d x209_o1); rewrite !inE | by apply: (d x209_o2); rewrite !inE | by apply: (d x209_o3); rewrite !inE
  | by apply: (d x209_o4); rewrite !inE | by apply: (d x209_o5); rewrite !inE ].
Qed.

Lemma x209_fano_card : #|x209_fano| = 7.
Proof. by rewrite cardsE (card_uniqP x209_fano_lines_uniq). Qed.

Lemma x209_fano_uniform : x209_uniform x209_fano 3.
Proof.
have c3 (a b c : 'I_7) : a != b -> a != c -> b != c -> #|[set a; b; c]| = 3.
  move=> ab ac bc; rewrite cardsU cards2 ab cards1 setIC.
  rewrite (_ : [set c] :&: _ = set0) ?cards0 //.
  apply/setP => x; rewrite !inE.
  by case: eqP => // ->; rewrite ![c == _]eq_sym (negbTE ac) (negbTE bc).
move=> e; rewrite inE /x209_fano_lines !in_cons in_nil orbF.
(repeat case/orP => [/eqP -> | ]); try (by apply: c3); move/eqP ->; by apply: c3.
Qed.

(* No 2-colouring of the Fano plane leaves every line bichromatic: 128 boolean cases. *)
Lemma x209_fano_bool (b : 'I_7 -> bool) :
  [|| (b x209_o0 == b x209_o1) && (b x209_o1 == b x209_o3), (b x209_o1 == b x209_o2) && (b x209_o2 == b x209_o4),
      (b x209_o2 == b x209_o3) && (b x209_o3 == b x209_o5), (b x209_o3 == b x209_o4) && (b x209_o4 == b x209_o6),
      (b x209_o4 == b x209_o5) && (b x209_o5 == b x209_o0), (b x209_o5 == b x209_o6) && (b x209_o6 == b x209_o1)
    | (b x209_o6 == b x209_o0) && (b x209_o0 == b x209_o2)].
Proof.
by case: (b x209_o0); case: (b x209_o1); case: (b x209_o2); case: (b x209_o3); case: (b x209_o4); case: (b x209_o5); case: (b x209_o6).
Qed.

Lemma x209_I2_eq (x y : 'I_2) : (x == ord0) = (y == ord0) -> x = y.
Proof.
by case: x => [[|[|//]] hx]; case: y => [[|[|//]] hy] //= _; apply/val_inj.
Qed.

Lemma x209_mono3 (col : 'I_7 -> 'I_2) (a b c : 'I_7) :
  (col a == ord0) == (col b == ord0) -> (col b == ord0) == (col c == ord0) ->
  monochromatic_on col [set a; b; c].
Proof.
move=> /eqP/x209_I2_eq ab /eqP/x209_I2_eq bc; apply/monochromatic_onP => x y.
rewrite !inE => hx hy.
have ex : col x = col b by move: hx; (repeat case/orP); move/eqP ->.
have ey : col y = col b by move: hy; (repeat case/orP); move/eqP ->.
by rewrite ex ey.
Qed.

Lemma x209_fano_mono_line (col : 'I_7 -> 'I_2) : exists2 e, e \in x209_fano & monochromatic_on col e.
Proof.
have := x209_fano_bool (fun v => col v == ord0).
(repeat case/orP) => /andP [h1 h2]; (eexists; [ | exact: x209_mono3 h1 h2 ]).
  all: by rewrite inE /x209_fano_lines !in_cons eqxx ?orbT.
Qed.

Lemma x209_fano_cut_le (col : 'I_7 -> 'I_2) : x209_cut_size x209_fano col <= 6.
Proof.
have [e ef em] := x209_fano_mono_line col.
have : x209_cut_size x209_fano col < #|x209_fano|.
  rewrite /x209_cut_size /non_monochromatic_count.
  apply: proper_card; apply/properP; split.
    by apply/subsetP => f; rewrite inE => /andP [].
  by exists e => //; rewrite inE em andbF.
by rewrite x209_fano_card.
Qed.

Lemma x209_fano_max_exists : exists2 c, c <= 6 & x209_is_max_r_cut x209_fano 2 c.
Proof.
pose g (f : {ffun 'I_7 -> 'I_2}) := x209_cut_size x209_fano f.
have [f _ hf] := @arg_maxnP _ [ffun=> ord0] xpredT g isT.
exists (g f); first exact: x209_fano_cut_le.
exists f; split=> // col.
have e : x209_cut_size x209_fano col = g [ffun v => col v].
  rewrite /g /x209_cut_size /non_monochromatic_count; apply: eq_card => e; rewrite !inE /monochromatic_on.
  by rewrite (@eq_map _ _ col [ffun v => col v]) // => x; rewrite ffunE.
by rewrite e; apply: hf.
Qed.

Lemma x209_fano_excess_small : exists2 y, y <= 3 & x209_scaled_excess x209_fano 2 3 y.
Proof.
have [c c6 hc] := x209_fano_max_exists.
exists (x209_expected_den 2 3 * c - (x209_expected_den 2 3).-1 * #|x209_fano|); last by exists c.
rewrite x209_fano_card /x209_expected_den /= leq_subLR (_ : (1 * 2 ^ 1).+1 * 7 + 3 = 2 ^ 2 * 6) //.
by rewrite leq_mul2l c6 orbT.
Qed.


(** Defect (1), the minimum: for (r, k, m) = (2, 3, 7) the frozen-chain minimum accepts 7 (its competitors live on
    five vertices, where every 7-edge 3-uniform family is 2-colourable), while the Fano plane has scaled excess at
    most 3, so 7 is not the least scaled excess over every vertex type. *)
Lemma x209_old_min_not_minimal :
  x209_is_min_scaled_excess 2 3 7 7 /\
  exists (T : finType) (E : {set {set T}}) (y : nat),
    [/\ x209_uniform E 3, #|E| = 7, x209_scaled_excess E 2 3 y & y < 7].
Proof.
split; first exact: x209_old_min_seven.
have [y y3 hy] := x209_fano_excess_small.
by exists 'I_7, x209_fano, y; split=> //; [exact: x209_fano_uniform | exact: x209_fano_card | exact: leq_ltn_trans y3 _].
Qed.

(** Defect (2), the cut: one triple, three colours, coloured 0, 0, 2.  It is cut in the frozen count (not
    monochromatic) but not multicoloured, so the frozen and the source sizes differ (1 and 0). *)
Definition x209_tri_col (v : 'I_3) : 'I_3 := if v == ord_max then ord_max else ord0.

Lemma x209_cut_defect :
  x209_cut_size [set [set: 'I_3]] x209_tri_col = 1 /\ x209_mc_cut_size [set [set: 'I_3]] x209_tri_col = 0.
Proof.
have c0 : x209_tri_col ord0 = ord0 by [].
have c2 : x209_tri_col ord_max = ord_max by [].
have nm : ~~ monochromatic_on x209_tri_col [set: 'I_3].
  apply/negP => /monochromatic_onP h.
  by have := h ord0 ord_max (in_setT _) (in_setT _); rewrite c0 c2.
have nmc : ~~ x209_multicoloured x209_tri_col [set: 'I_3].
  apply/negP => /forallP /(_ (@Ordinal 3 1 isT)) /existsP [v /andP [_]].
  by rewrite /x209_tri_col; case: (v == ord_max).
split.
  rewrite /x209_cut_size /non_monochromatic_count.
  rewrite (_ : [set e in _ | _] = [set [set: 'I_3]]) ?cards1 //.
  by apply/setP => e; rewrite !inE; case: eqP => // ->; rewrite nm.
rewrite /x209_mc_cut_size (_ : [set e in _ | _] = set0) ?cards0 //.
by apply/setP => e; rewrite !inE; case: eqP => // ->; rewrite (negbTE nmc).
Qed.
