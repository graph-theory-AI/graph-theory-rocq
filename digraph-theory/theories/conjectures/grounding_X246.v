(** * Digraph.conjectures.grounding_X246 -- grounding certificates of wave X246.

    For each of the six rows: hyp_inhabited (the hypotheses hold on a concrete instance, and the
    statement then yields its conclusion there) and not_trivially_true in the contract form of
    meta/EXPANSION_PLAN.md 4.4 (the row with one load-bearing hypothesis dropped is false, and
    that variant implies the row); and helper_sanity for each of the five x246_ helpers (one
    instance where it holds, one where it fails). The dropped hypotheses: the second hero
    hypothesis of arxiv:2202.13306#01 (H = 2K_1, F = K_1, refuted by the tournaments
    T_(k+1) = c3sub K1 T_k T_k of dichromatic number > k); the guard "odd n && 2 < n" of
    arxiv:2510.11311#00 (the single arc, n = 2, is not avoidable); the height function of #01
    (a one-vertex loop is avoidable); "dicycle c" of arxiv:2602.16333#00; vertex transitivity of
    #03 (the single arc); 2n < 3r of arxiv:2204.01938#00 (two disjoint directed triangles are
    2-free with beta = 2, not Remark 5.7's example). *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_fingroup.
From Digraph Require Import prelude digraph oriented dipath tournament heroes heroes_dichotomy dichromatic unvd.
From Digraph Require Import digraph_sum X246.
From Digraph Require automorphism X2.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Two disjoint directed triangles on 'I_6: blocks {0,1,2} and {3,4,5}. *)
Definition g246_two_tri : Type := 'I_6.
HB.instance Definition _ := Finite.on g246_two_tri.
HB.instance Definition _ := HasArc.Build g246_two_tri
  [rel i j : 'I_6 | (i %/ 3 == j %/ 3) && (j %% 3 == (i %% 3).+1 %% 3)].

Lemma g246_two_tri_r_free2 : x246_r_free 2 g246_two_tri.
Proof.
move=> c /and3P [nc cyc uc].
have nl : [forall x : g246_two_tri, ~~ (x --> x)] by apply/forallP => -[[|[|[|[|[|[|i]]]]]] //].
have nd : forall x y : g246_two_tri, ~~ ((x --> y) && (y --> x)) by move=> -[[|[|[|[|[|[|i]]]]]] ix] -[[|[|[|[|[|[|j]]]]]] jy] //.
case: c nc cyc uc => [|x [|y [|z t]]] //= _; [by rewrite andbT => xx; move/forallP: nl => /(_ x); rewrite xx | by rewrite andbT => /andP [xy yx]; have := nd x y; rewrite xy yx].
Qed.

Lemma g246_two_tri_not_fas_le1 : ~ x246_fas_le1 g246_two_tri.
Proof.
move=> [F [F1 hF]].
pose o0 : g246_two_tri := Ordinal (isT : 0 < 6).
pose o1 : g246_two_tri := Ordinal (isT : 1 < 6).
pose o2 : g246_two_tri := Ordinal (isT : 2 < 6).
pose o3 : g246_two_tri := Ordinal (isT : 3 < 6).
pose o4 : g246_two_tri := Ordinal (isT : 4 < 6).
pose o5 : g246_two_tri := Ordinal (isT : 5 < 6).
have d1 : dicycle [:: o0; o1; o2] by [].
have d2 : dicycle [:: o3; o4; o5] by [].
have /hasP [e1 e1F e1c] := hF _ d1.
have /hasP [e2 e2F e2c] := hF _ d2.
have h1 : (val e1.1 < 3)%N by move: e1F; rewrite /= !inE => /or3P [] /eqP ->.
have h2 : (3 <= val e2.1)%N by move: e2F; rewrite /= !inE => /or3P [] /eqP ->.
have ne : e1 != e2 by apply/eqP => E; move: h1; rewrite E ltnNge h2.
have : (#|[set e1; e2]| <= #|F|)%N.
  apply: subset_leq_card; apply/subsetP => x; rewrite !inE => /orP [] /eqP ->; [exact: e1c | exact: e2c].
by rewrite cards2 ne => h; have := leq_trans h F1.
Qed.

(** The single arc 0 -> 1 (the transitive tournament on two vertices). *)
Definition g246_arc : diGraphType := TT 2.

(** Row 6 (arxiv:2204.01938#00). *)
Definition g246_rfree_hyp_claim : Prop :=
  [/\ (2 * #|g246_arc| < 3 * 2)%N, x246_r_free 2 g246_arc &
      (r_free_two_thirds_one_arc_from_acyclic_statement -> x246_fas_le1 g246_arc)].

Lemma g246_arc_r_free2 : x246_r_free 2 g246_arc.
Proof.
move=> c /and3P [nc cyc _]; case: c nc cyc => [|x [|y [|z t]]] //= _.
  by case: x => [[|[|i]] ?].
by case: x => [[|[|i]] ?]; case: y => [[|[|j]] ?].
Qed.

Theorem g246_rfree_hyp_inhabited : g246_rfree_hyp_claim.
Proof.
have c2 : (2 * #|g246_arc| < 3 * 2)%N by rewrite card_ord.
by split => // [|h]; [exact: g246_arc_r_free2 | exact: h 2 g246_arc c2 g246_arc_r_free2].
Qed.

Definition g246_rfree_no_two_thirds : Prop :=
  forall (r : nat) (D : diGraphType), x246_r_free r D -> x246_fas_le1 D.

Definition g246_rfree_ntt_claim : Prop :=
  ~ g246_rfree_no_two_thirds /\ (g246_rfree_no_two_thirds -> r_free_two_thirds_one_arc_from_acyclic_statement).

Theorem g246_rfree_not_trivially_true : g246_rfree_ntt_claim.
Proof.
split; last by move=> h r D _; exact: h.
by move=> h; exact: g246_two_tri_not_fas_le1 (h 2 _ g246_two_tri_r_free2).
Qed.

(** The single arc has no dicycle: a dicycle is uniq, so it has at most 2 vertices, against 2-freeness. *)
Lemma g246_arc_no_dicycle (c : seq g246_arc) : ~~ dicycle c.
Proof.
apply/negP => dc; have := g246_arc_r_free2 dc; move: dc => /and3P [_ _ uc].
have : (size c <= #|g246_arc|)%N by rewrite -(card_uniqP uc); exact: max_card.
by rewrite card_ord => h1 h2; have := leq_trans h2 h1.
Qed.

(** The digon on 'I_2: both arcs between 0 and 1. *)
Definition g246_digon : Type := 'I_2.
HB.instance Definition _ := Finite.on g246_digon.
HB.instance Definition _ := HasArc.Build g246_digon [rel i j : 'I_2 | i != j].

Lemma g246_digon_vt : automorphism.vertex_transitiveb g246_digon.
Proof.
apply/automorphism.vertex_transitivebP => u v; exists (tperm u v); last by rewrite tpermL.
rewrite automorphism.dgautE; apply/automorphism.autbP => a b.
by change ((tperm u v a != tperm u v b) = (a != b)); rewrite (inj_eq perm_inj).
Qed.

(** Row 5 (arxiv:2602.16333#03). *)
Definition g246_ratio_hyp_claim : Prop :=
  [/\ automorphism.vertex_transitiveb g246_digon,
      dipath (ord0 : g246_digon) [:: (ord_max : g246_digon)] &
      (vertex_transitive_path_cycle_ratio_statement ->
         exists C : nat, exists c : seq g246_digon, dicycle c /\ (1 <= C * size c)%N)].

Theorem g246_ratio_hyp_inhabited : g246_ratio_hyp_claim.
Proof.
have dp : dipath (ord0 : g246_digon) [:: (ord_max : g246_digon)] by [].
split => // [|h]; first exact: g246_digon_vt.
have [C hC] := h; have [c [dc cs]] := hC g246_digon g246_digon_vt ord0 [:: ord_max] dp isT.
by exists C, c.
Qed.

Definition g246_ratio_no_vt : Prop :=
  exists C : nat, forall D : diGraphType,
    forall (x : D) (s : seq D), dipath x s -> (0 < size s)%N ->
      exists c : seq D, dicycle c /\ (size s <= C * size c)%N.

Definition g246_ratio_ntt_claim : Prop :=
  ~ g246_ratio_no_vt /\ (g246_ratio_no_vt -> vertex_transitive_path_cycle_ratio_statement).

Theorem g246_ratio_not_trivially_true : g246_ratio_ntt_claim.
Proof.
split; last by move=> [C hC]; exists C => D _; exact: hC.
move=> [C hC].
have dp : dipath (ord0 : g246_arc) [:: (ord_max : g246_arc)] by [].
have [c [dc _]] := hC g246_arc ord0 [:: ord_max] dp isT.
by have := g246_arc_no_dicycle c; rewrite dc.
Qed.

(** Row 4 (arxiv:2602.16333#00): the one-vertex arcless digraph K1 (= TT 1). *)
Lemma g246_K1_no_dicycle (c : seq (K1 : diGraphType)) : ~~ dicycle c.
Proof.
apply/negP => /and3P []; case: c => [|x [|y t]] //= _; first by rewrite andbT; case: x => [[|i] ?].
by move=> _; rewrite inE (ord1 x) (ord1 y) eqxx.
Qed.

Lemma g246_K1_wc : X2.weakly_connected (K1 : diGraphType).
Proof. by move=> u v; rewrite (ord1 u) (ord1 v) connect0. Qed.

Lemma g246_K1_vt : automorphism.vertex_transitiveb (K1 : diGraphType).
Proof.
apply/automorphism.vertex_transitivebP => u v; exists 1%g; first exact: automorphism.dgaut1.
by rewrite perm1 (ord1 u) (ord1 v).
Qed.

Definition g246_gap_hyp_claim : Prop :=
  [/\ (1 <= #|(K1 : diGraphType)|)%N, X2.weakly_connected (K1 : diGraphType),
      automorphism.vertex_transitiveb (K1 : diGraphType),
      (forall c : seq (K1 : diGraphType), dicycle c -> (1 * size c + #|(K1 : diGraphType)| <= 1 * #|(K1 : diGraphType)|)%N) &
      (vertex_transitive_linear_perimeter_gap_statement -> exists m : nat, exists D : diGraphType,
         [/\ (1 <= #|D|)%N, X2.weakly_connected D, automorphism.vertex_transitiveb D &
             forall c : seq D, dicycle c -> (m * size c + #|D| <= m * #|D|)%N])].

Theorem g246_gap_hyp_inhabited : g246_gap_hyp_claim.
Proof.
split; [by rewrite card_ord | exact: g246_K1_wc | exact: g246_K1_vt | | ].
- by move=> c dc; have := g246_K1_no_dicycle c; rewrite dc.
- by move=> [m hm]; exists m; exact: hm 1.
Qed.

Definition g246_gap_no_dicycle : Prop :=
  exists m : nat, forall N : nat, exists D : diGraphType,
    [/\ (N <= #|D|)%N, X2.weakly_connected D, automorphism.vertex_transitiveb D &
        forall c : seq D, (m * size c + #|D| <= m * #|D|)%N].

Definition g246_gap_ntt_claim : Prop :=
  ~ g246_gap_no_dicycle /\ (g246_gap_no_dicycle -> vertex_transitive_linear_perimeter_gap_statement).

Theorem g246_gap_not_trivially_true : g246_gap_ntt_claim.
Proof.
split; last by move=> [m hm]; exists m => N; have [D [h1 h2 h3 h4]] := hm N; exists D; split => // c _; exact: h4.
move=> [m hm]; have [D [n1 _ _ h]] := hm 1.
have := h (enum D); rewrite -cardE -[X in (_ <= X)%N]addn0 leq_add2l leqn0.
by move/eqP => e; move: n1; rewrite e.
Qed.

(** ** Avoidability: a two-vertex digraph whose only arc is a -> b is not avoidable. *)

(** The loopless complete digraph on 'I_N. *)
Definition g246_complete (N : nat) : Type := 'I_N.
HB.instance Definition _ (N : nat) := Finite.on (g246_complete N).
HB.instance Definition _ (N : nat) := HasArc.Build (g246_complete N) [rel i j : 'I_N | i != j].

Lemma g246_complete_outdeg (N : nat) (v : g246_complete N) : outdeg v = N.-1.
Proof.
rewrite /outdeg (_ : [set w | v --> w] = [set~ v]) ?cardsC1 ?card_ord //.
by apply/setP => w; rewrite !inE eq_sym.
Qed.

Lemma g246_not_avoidable_arc (F : diGraphType) (a b : F) :
  a != b -> (forall x : F, x = a \/ x = b) -> (forall u v : F, u --> v -> u = a /\ v = b) ->
  ~ x246_avoidable F.
Proof.
move=> ab hall harc [d hd].
pose D := (g246_complete (d 1).+1 : diGraphType).
have irr : irreflexive (@arc D) by move=> i; change ((i : 'I_(d 1).+1) != i = false); rewrite eqxx.
have pos : (0 < #|D|)%N by rewrite card_ord.
have deg : forall v : D, (d 1 <= outdeg v)%N by move=> v; rewrite g246_complete_outdeg.
have [S [f [Sn hdeg hfree]]] := hd 1 D irr pos deg.
have /set0Pn [x xS] := Sn.
pose v0 : outsel f := (exist _ x xS : induced_digraph S).
have /card_gt0P [w] := hdeg v0.
rewrite inE => vw.
have ne : v0 != w.
  apply/eqP => e; have := outsel_arc_sub vw; rewrite e.
  by rewrite sub_arcE irr.
have ba : (b == a) = false by rewrite eq_sym (negbTE ab).
apply: hfree; exists (fun y : F => if y == a then v0 else w); split.
- move=> y1 y2; case: (hall y1) => ->; case: (hall y2) => ->; rewrite ?eqxx ?ba //.
  + by move=> e; move: ne; rewrite e eqxx.
  + by move=> e; move: ne; rewrite e eqxx.
- by move=> u v /harc [-> ->]; rewrite eqxx ba.
Qed.

(** ** Avoidability: a digraph with a loop is avoidable (loopless hosts never contain it). *)
Lemma g246_loop_avoidable (F : diGraphType) (a : F) : a --> a -> x246_avoidable F.
Proof.
move=> aa; exists id => k D irr pos deg.
exists setT, (fun _ => setT); split.
- by have /card_gt0P [x _] := pos; apply/set0Pn; exists x; rewrite inE.
- move=> v.
  pose g (y : D) : outsel (fun=> [set: induced_digraph [set: D]]) :=
    (exist _ y (in_setT y) : induced_digraph [set: D]).
  have ginj : injective g by move=> y1 y2 /(congr1 val).
  apply: leq_trans (deg (val v)) _; rewrite /outdeg -(card_imset _ ginj); apply: subset_leq_card.
  by apply/subsetP => _ /imsetP [y yin ->]; rewrite !inE in yin *; rewrite outsel_arcE inE sub_arcE.
- by move=> [h [_ hh]]; have := outsel_arc_sub (hh a a aa); rewrite sub_arcE irr.
Qed.

(** The one-vertex loop. *)
Definition g246_loop : Type := 'I_1.
HB.instance Definition _ := Finite.on g246_loop.
HB.instance Definition _ := HasArc.Build g246_loop [rel i j : 'I_1 | true].

Lemma g246_loop_avoidable1 : x246_avoidable g246_loop.
Proof. exact: (@g246_loop_avoidable g246_loop ord0). Qed.

Lemma g246_arc_not_avoidable : ~ x246_avoidable g246_arc.
Proof.
apply: (@g246_not_avoidable_arc g246_arc ord0 ord_max) => //.
- by move=> x; case: x => [[|[|i]] hi]; [left; exact: val_inj | right; exact: val_inj |].
- by move=> u v; case: u => [[|[|i]] hi]; case: v => [[|[|j]] hj] // _; split; exact: val_inj.
Qed.

(** Row 2 (arxiv:2510.11311#00). *)
Definition g246_odd_hyp_claim : Prop :=
  [/\ odd 3 && (2 < 3)%N &
      (odd_cycle_orientations_avoidable_statement -> forall b : 'I_3 -> bool, x246_avoidable (x246_cycle_or b))].

Theorem g246_odd_hyp_inhabited : g246_odd_hyp_claim.
Proof. by split => // h b; exact: h 3 b isT. Qed.

Definition g246_odd_no_hyp : Prop :=
  forall (n : nat) (b : 'I_n -> bool), x246_avoidable (x246_cycle_or b).

Definition g246_odd_ntt_claim : Prop :=
  ~ g246_odd_no_hyp /\ (g246_odd_no_hyp -> odd_cycle_orientations_avoidable_statement).

Theorem g246_odd_not_trivially_true : g246_odd_ntt_claim.
Proof.
split; last by move=> h n b _; exact: h.
move=> h; have := h 2 (fun i : 'I_2 => i == ord0).
apply: (@g246_not_avoidable_arc _ (ord0 : x246_cycle_or (fun i : 'I_2 => i == ord0)) ord_max) => //.
- by move=> x; case: x => [[|[|i]] hi]; [left; exact: val_inj | right; exact: val_inj |].
- by move=> u v; case: u => [[|[|i]] hi]; case: v => [[|[|j]] hj] // _; split; exact: val_inj.
Qed.

(** Row 3 (arxiv:2510.11311#01). *)
Lemma g246_arc_height : x246_height g246_arc.
Proof.
exists (fun x : g246_arc => val x) => u v.
by case: u => [[|[|i]] ?]; case: v => [[|[|j]] ?].
Qed.

Definition g246_height_hyp_claim : Prop :=
  [/\ x246_height g246_arc & (height_function_not_avoidable_statement -> ~ x246_avoidable g246_arc)].

Theorem g246_height_hyp_inhabited : g246_height_hyp_claim.
Proof. by split => [|h]; [exact: g246_arc_height | exact: h _ g246_arc_height]. Qed.

Definition g246_height_no_height : Prop := forall F : diGraphType, ~ x246_avoidable F.

Definition g246_height_ntt_claim : Prop :=
  ~ g246_height_no_height /\ (g246_height_no_height -> height_function_not_avoidable_statement).

Theorem g246_height_not_trivially_true : g246_height_ntt_claim.
Proof.
split; last by move=> h F _; exact: h.
by move=> h; exact: h _ g246_loop_avoidable1.
Qed.

(** ** helper_sanity: each helper holds on one instance and fails on another. *)
Definition g246_avoidable_helper_claim : Prop :=
  x246_avoidable g246_loop /\ ~ x246_avoidable g246_arc.

Theorem g246_avoidable_helper_sanity : g246_avoidable_helper_claim.
Proof. by split; [exact: g246_loop_avoidable1 | exact: g246_arc_not_avoidable]. Qed.

Definition g246_cycle_or_helper_claim : Prop :=
  [/\ (Ordinal (isT : 0 < 3) : x246_cycle_or (fun _ : 'I_3 => true)) --> Ordinal (isT : 1 < 3),
      (Ordinal (isT : 1 < 3) : x246_cycle_or (fun _ : 'I_3 => true)) --> Ordinal (isT : 2 < 3),
      (Ordinal (isT : 2 < 3) : x246_cycle_or (fun _ : 'I_3 => true)) --> Ordinal (isT : 0 < 3) &
      ~~ ((Ordinal (isT : 1 < 3) : x246_cycle_or (fun _ : 'I_3 => true)) --> Ordinal (isT : 0 < 3))].

Theorem g246_cycle_or_helper_sanity : g246_cycle_or_helper_claim.
Proof. by []. Qed.

Lemma g246_two_tri_no_height : ~ x246_height g246_two_tri.
Proof.
move=> [h hh].
have e1 := hh (Ordinal (isT : 0 < 6)) (Ordinal (isT : 1 < 6)) isT.
have e2 := hh (Ordinal (isT : 1 < 6)) (Ordinal (isT : 2 < 6)) isT.
have e3 := hh (Ordinal (isT : 2 < 6)) (Ordinal (isT : 0 < 6)) isT.
by move: e3; rewrite e2 e1 => /eqP; rewrite -(addn0 (h (Ordinal (isT : 0 < 6)))) -!addnS eqn_add2l.
Qed.

Definition g246_height_helper_claim : Prop :=
  x246_height g246_arc /\ ~ x246_height g246_two_tri.

Theorem g246_height_helper_sanity : g246_height_helper_claim.
Proof. by split; [exact: g246_arc_height | exact: g246_two_tri_no_height]. Qed.

Definition g246_r_free_helper_claim : Prop :=
  x246_r_free 2 g246_arc /\ ~ x246_r_free 3 g246_two_tri.

Theorem g246_r_free_helper_sanity : g246_r_free_helper_claim.
Proof.
split; first exact: g246_arc_r_free2.
move=> h; have := h [:: Ordinal (isT : 0 < 6); Ordinal (isT : 1 < 6); Ordinal (isT : 2 < 6)] isT.
by rewrite ltnn.
Qed.

Definition g246_fas_helper_claim : Prop :=
  x246_fas_le1 g246_arc /\ ~ x246_fas_le1 g246_two_tri.

Theorem g246_fas_helper_sanity : g246_fas_helper_claim.
Proof.
split; last exact: g246_two_tri_not_fas_le1.
exists set0; split; first by rewrite cards0.
by move=> c dc; have := g246_arc_no_dicycle c; rewrite dc.
Qed.

(** ** Row 1 (arxiv:2202.13306#01): tournaments of large dichromatic number. *)

(** An arc-preserving and arc-reflecting injection maps dicycles to dicycles and back. *)
Lemma g246_dicycle_map (D D' : diGraphType) (g : D -> D') :
  injective g -> (forall u v, (g u --> g v) = (u --> v)) -> forall s : seq D, dicycle (map g s) = dicycle s.
Proof.
move=> gi ga s; rewrite /dicycle (map_inj_uniq gi) cycle_map.
have -> : path.cycle (relpre g arc) s = path.cycle arc s by apply: eq_cycle => u v; rewrite /relpre /= ga.
by case: s.
Qed.

(** A dicycle inside S: the induced subdigraph on S is not acyclic. *)
Lemma g246_not_acyclic_induced (D : diGraphType) (S : {set D}) (c : seq D) :
  dicycle c -> all (mem S) c -> ~~ acyclicb (induced_digraph S).
Proof.
move=> dc cS.
pose c' : seq (induced_digraph S) := pmap insub c.
have ec : map val c' = c.
  rewrite /c'; elim: c cS {dc c'} => [|x t IH] //= /andP [xS tS]; rewrite insubT /= IH //.
have gi : injective (fun v : induced_digraph S => (val v : D)) by move=> x y; exact: val_inj.
have ga : forall u v : induced_digraph S, ((val u : D) --> val v) = (u --> v) by move=> u v; rewrite sub_arcE.
rewrite -ec (g246_dicycle_map gi ga) in dc; exact: dicycle_not_acyclicb dc.
Qed.

(** The tournaments T_0 = K1, T_(k+1) = Delta(1, T_k, T_k) = c3sub K1 T_k T_k. *)
Fixpoint g246_T (k : nat) : diGraphType :=
  if k is k'.+1 then (c3sub K1 (g246_T k') (g246_T k') : diGraphType) else K1.

(** In T_k, every colouring with colours from a list of at most k values has a monochromatic dicycle. *)
Lemma g246_T_mono (k : nat) (col : g246_T k -> nat) (L : seq nat) :
  (size L <= k)%N -> (forall v, col v \in L) ->
  exists c : seq (g246_T k), dicycle c /\ forall v w, v \in c -> w \in c -> col v = col w.
Proof.
elim: k col L => [|k IH] col L sL hL.
  by have := hL ord0; move: sL; rewrite leqn0 => /nilP ->.
pose x : g246_T k.+1 := inl (inl ord0).
pose c0 := col x.
have c0L : c0 \in L := hL x.
have sF : (size (filter (predC1 c0) L) <= k)%N.
  rewrite size_filter -ltnS; apply: leq_trans sL; rewrite -(count_predC (pred1 c0) L) -add1n leq_add2r.
  by rewrite -has_count has_pred1.
(* a copy of T_k avoiding the apex's colour has a monochromatic dicycle by induction *)
have lift : forall g : g246_T k -> g246_T k.+1, injective g -> (forall u v, (g u --> g v) = (u --> v)) ->
    (forall b, col (g b) != c0) ->
    exists c : seq (g246_T k.+1), dicycle c /\ forall v w, v \in c -> w \in c -> col v = col w.
  move=> g gi ga hb.
  have hF : forall b, col (g b) \in filter (predC1 c0) L by move=> b; rewrite mem_filter /= hb hL.
  have [c [dc mono]] := IH (fun b => col (g b)) _ sF hF.
  exists (map g c); split; first by rewrite (g246_dicycle_map gi ga).
  by move=> v w /mapP [v' v'c ->] /mapP [w' w'c ->]; exact: mono.
pose g1 (b : g246_T k) : g246_T k.+1 := inl (inr b).
pose g2 (b : g246_T k) : g246_T k.+1 := inr b.
have g1i : injective g1 by move=> u v [].
have g2i : injective g2 by move=> u v [].
have g1a : forall u v, (g1 u --> g1 v) = (u --> v) by [].
have g2a : forall u v, (g2 u --> g2 v) = (u --> v) by [].
case: (boolP [exists b, col (g1 b) == c0]) => [/existsP [b1 /eqP e1] | /existsPn n1]; last by apply: lift g1i g1a _.
case: (boolP [exists b, col (g2 b) == c0]) => [/existsP [b2 /eqP e2] | /existsPn n2]; last by apply: lift g2i g2a _.
(* both copies meet the apex's colour: the triangle x -> b1 -> b2 -> x is monochromatic *)
exists [:: x; g1 b1; g2 b2]; split; first by [].
by move=> v w; rewrite !inE => /or3P [] /eqP -> /or3P [] /eqP ->; rewrite ?e1 ?e2.
Qed.

Lemma g246_T_not_dicolorable (k : nat) : ~~ dicolorableb (g246_T k) k.
Proof.
apply/negP => /existsP [col /forallP ac].
have sz : (size (iota 0 k) <= k)%N by rewrite size_iota.
have inL : forall v, val (col v) \in iota 0 k by move=> v; rewrite mem_iota add0n ltn_ord.
have [c [dc mono]] := @g246_T_mono k (fun v => val (col v)) (iota 0 k) sz inL.
case: c dc mono => [|x t] dc mono; first by case/and3P: dc.
have hall : all (mem [set v | col v == col x]) (x :: t).
  apply/allP => v vc.
  by rewrite !inE; apply/eqP/ord_inj; apply: mono => //; rewrite inE eqxx.
by have := g246_not_acyclic_induced dc hall; rewrite ac.
Qed.

Lemma g246_T_oriented (k : nat) : oriented_dg (g246_T k).
Proof.
elim: k => [|k IH] u v; first by rewrite (ord1 u) (ord1 v).
case: u => [[a|b]|c]; case: v => [[a'|b']|c'] //=; try exact: IH.
by rewrite (ord1 a) (ord1 a').
Qed.

Lemma g246_T_semicomplete (k : nat) (u v : g246_T k) : u != v -> (u --> v) || (v --> u).
Proof.
elim: k u v => [|k IH] u v; first by rewrite (ord1 u) (ord1 v) eqxx.
case: u => [[a|b]|c]; case: v => [[a'|b']|c'] //=; try exact: IH.
by rewrite (ord1 a) (ord1 a') eqxx.
Qed.

(** A digraph with two distinct non-adjacent vertices is never induced in a semicomplete digraph. *)
Lemma g246_semicomplete_ind_free (X D : diGraphType) (a b : X) :
  a != b -> ~~ (a --> b) -> ~~ (b --> a) ->
  (forall u v : D, u != v -> (u --> v) || (v --> u)) -> ind_free X D.
Proof.
move=> ab nab nba sc [f [fi fa]].
have : f a != f b by rewrite (inj_eq fi).
by move/sc; rewrite !fa (negbTE nab) (negbTE nba).
Qed.

(** Oriented and K1-free: no vertex. *)
Lemma g246_K1_free_void (D : diGraphType) : oriented_dg D -> ind_free K1 D -> forall x : D, False.
Proof.
move=> oD kf x; apply: kf; exists (fun _ => x); split; first by move=> u v _; rewrite (ord1 u) (ord1 v).
move=> u v; rewrite (ord1 u) (ord1 v) /=.
by case xx: (x --> x) => //; have := oD x x xx; rewrite xx.
Qed.

(** Oriented and TT_2-free: no arc. *)
Lemma g246_arc_free_arcless (D : diGraphType) : oriented_dg D -> ind_free g246_arc D -> forall u v : D, ~~ (u --> v).
Proof.
move=> oD af u v; apply/negP => uv; apply: af.
have nl : forall x : D, (x --> x) = false by move=> x; apply/negP => xx; have := oD x x xx; rewrite xx.
have vu : (v --> u) = false by apply/negbTE; exact: oD.
have uv' : u != v by apply/eqP => e; move: uv; rewrite e nl.
exists (fun i : g246_arc => if i == ord0 then u else v); split.
- move=> i j; case: i => [[|[|i]] ?]; case: j => [[|[|j]] ?] //= e; try (by apply/val_inj);
    by move: uv'; rewrite e eqxx.
- by move=> i j; case: i => [[|[|i]] ?]; case: j => [[|[|j]] ?] //=; rewrite ?nl ?uv ?vu.
Qed.

Lemma g246_arcless_dicolorable (D : diGraphType) : (forall u v : D, ~~ (u --> v)) -> dicolorableb D 1.
Proof.
move=> nA; apply/existsP; exists [ffun _ => ord0]; apply/forallP => i.
by apply/forallP => v; apply/forallP => w; apply/implyP; rewrite sub_arcE (negbTE (nA _ _)).
Qed.

Lemma g246_TT_oriented (n : nat) : oriented_dg (TT n : diGraphType).
Proof. by move=> u v; rewrite !arcTTE => uv; rewrite -leqNgt ltnW. Qed.

(** Two isolated vertices. *)
Definition g246_2K1 : diGraphType := digraph_sum K1 K1.

Lemma g246_2K1_oriented : oriented_dg g246_2K1.
Proof. by move=> [a|a] [b|b] //=; rewrite (ord1 a) (ord1 b). Qed.

Definition g246_hero_hyp_claim : Prop :=
  [/\ oriented_dg (K1 : diGraphType), oriented_dg g246_arc,
      dichromatic_bounded
        (fun D => [/\ oriented_dg D, ind_free g246_arc D & ind_free (c3sub K1 K1 K1) D]),
      dichromatic_bounded
        (fun D => [/\ oriented_dg D, ind_free (digraph_sum K1 g246_arc) D & ind_free K1 D]) &
      (delta11_hero_transfer_k1_plus_statement ->
         dichromatic_bounded
           (fun D => [/\ oriented_dg D, ind_free (digraph_sum K1 g246_arc) D & ind_free (c3sub K1 K1 K1) D]))].

Theorem g246_hero_hyp_inhabited : g246_hero_hyp_claim.
Proof.
have oK1 : oriented_dg (K1 : diGraphType) := @g246_TT_oriented 1.
have oA : oriented_dg g246_arc := @g246_TT_oriented 2.
have b1 : dichromatic_bounded (fun D => [/\ oriented_dg D, ind_free g246_arc D & ind_free (c3sub K1 K1 K1) D]).
  by exists 1 => D [oD af _]; apply: g246_arcless_dicolorable; exact: g246_arc_free_arcless oD af.
have b2 : dichromatic_bounded (fun D => [/\ oriented_dg D, ind_free (digraph_sum K1 g246_arc) D & ind_free K1 D]).
  by exists 1 => D [oD _ kf]; apply: g246_arcless_dicolorable => u; case: (g246_K1_free_void oD kf u).
by split => // h; exact: h K1 g246_arc oK1 oA b1 b2.
Qed.

Definition g246_hero_no_second : Prop :=
  forall H F : diGraphType, oriented_dg H -> oriented_dg F ->
    dichromatic_bounded
      (fun D => [/\ oriented_dg D, ind_free F D & ind_free (c3sub K1 K1 H) D]) ->
    dichromatic_bounded
      (fun D => [/\ oriented_dg D, ind_free (digraph_sum K1 F) D & ind_free (c3sub K1 K1 H) D]).

Definition g246_hero_ntt_claim : Prop :=
  ~ g246_hero_no_second /\ (g246_hero_no_second -> delta11_hero_transfer_k1_plus_statement).

Theorem g246_hero_not_trivially_true : g246_hero_ntt_claim.
Proof.
split; last by move=> h H F oH oF b1 _; exact: h H F oH oF b1.
move=> h.
(* H = 2K1, F = K1: the first class is the empty digraph; the conclusion fails on every T_B *)
have b1 : dichromatic_bounded (fun D => [/\ oriented_dg D, ind_free K1 D & ind_free (c3sub K1 K1 g246_2K1) D]).
  by exists 1 => D [oD kf _]; apply: g246_arcless_dicolorable => u; case: (g246_K1_free_void oD kf u).
have [B hB] := h g246_2K1 K1 g246_2K1_oriented (@g246_TT_oriented 1) b1.
have f1 : ind_free (digraph_sum K1 K1) (g246_T B).
  apply: (@g246_semicomplete_ind_free (digraph_sum K1 K1) (g246_T B) (inl ord0) (inr ord0)) => //.
  exact: g246_T_semicomplete.
have f2 : ind_free (c3sub K1 K1 g246_2K1) (g246_T B).
  apply: (@g246_semicomplete_ind_free (c3sub K1 K1 g246_2K1) (g246_T B) (inr (inl ord0)) (inr (inr ord0))) => //.
  exact: g246_T_semicomplete.
by have := g246_T_not_dicolorable B; rewrite hB //; split => //; exact: g246_T_oriented.
Qed.
