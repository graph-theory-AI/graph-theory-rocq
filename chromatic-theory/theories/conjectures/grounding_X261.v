(** * Chromatic.conjectures.grounding_X261 -- grounding certificates of wave X261.

    For each of the five rows: hyp_inhabited (the hypotheses hold on a concrete instance, with a concrete value of
    every relational number, and the statement then yields its conclusion there) and not_trivially_true in the
    contract form of meta/EXPANSION_PLAN.md 4.4 (a variant obtained from the body by deleting one hypothesis is false
    and implies the row): erdos:625 without the cochromatic-number hypothesis (z = n and M = 1 empty the event, so
    with probability 0); erdos:717 without the sigma hypothesis (s = 0 at K_2 asks 4 <= 0); erdos:760 without the
    guard 2 <= m (K_1, m = 1, log 1 = 0 asks 1 <= 0 for every subgraph); erdos:797 without Delta G = d (the complete
    graph on d^2 + 1 vertices needs more than d^2 colours); erdos:799 without 0 < q (q = 0 asks for empty lists).
    The concrete values: zeta(K_3) = 1, sigma(K_3) = 3, chi(K_3) = 3, Delta(K_2) = 1.  helper_sanity: zeta(K_3) = 1
    and zeta(P_3) = 2, not 1 and not 3 (colour classes must induce a complete or an empty graph); C_5 contains a
    subdivision of K_3 although it has no triangle, the path P_3 contains none, sigma(K_3) = 3 and not 2; C_4 has an
    acyclic 3-colouring and no acyclic 2-colouring; K_2 is 2-choosable and not 1-choosable.  Links to existing
    notions: x261_cochromatic_at_most reflects Chromatic.conjectures.XE2's xe2_cochromatic_colouring
    (g261_cochromatic_at_mostP), x261_acyclic_colourable is U4's acyclic_colouring with whole-palette lists
    (g261_acyclic_colourableE), and x261_choosable_b is equivalent to GTBase's choosable over any finite palette
    (g261_choosable_bE).  Two facts the X261.v Notes use: zeta(G) <= #|G| (g261_cochromatic_card) and fg_whp is
    monotone in the event (g261_whp_mono). *)

From GTBase Require Import base common finite_graph path_graphs.
From Chromatic.conjectures Require Import XE1 XE2 U4 X261.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** General facts *)

Lemma g261_cochromatic_at_mostP (G : sgraph) (k : nat) :
  reflect (xe2_cochromatic_colouring G k) (x261_cochromatic_at_most G k).
Proof.
apply: (iffP existsP) => [[col /forallP h]|[col h]].
  exists (fun v => col v) => i; have /orP [/cliqueP c|s] := h i; [by left | by right].
exists [ffun v => col v]; apply/forallP => i.
have e : [set v : G | [ffun v => col v] v == i] = [set v : G | col v == i]
  by apply/setP => v; rewrite !inE ffunE.
rewrite /= e; have [c|s] := h i; apply/orP; [left; exact/cliqueP | by right].
Qed.

(** One colour per vertex: zeta(G) <= #|G|. *)
Lemma g261_cochromatic_card (G : sgraph) : x261_cochromatic_at_most G #|G|.
Proof.
apply/existsP; exists [ffun v => enum_rank v]; apply/forallP => i; apply/orP; left.
apply/cliqueP => x y; rewrite !inE !ffunE => /eqP hx /eqP hy xy.
by move: xy; rewrite -(enum_rankK x) -(enum_rankK y) hx hy eqxx.
Qed.

(** No colouring into 'I_0 exists once G has a vertex. *)
Lemma g261_cochromatic_at_most0 (G : sgraph) (v : G) : ~~ x261_cochromatic_at_most G 0.
Proof. by apply/existsP => -[col _]; case: (col v). Qed.

Lemma g261_chi_le_card (G : sgraph) : χ([set: G]) <= #|G|.
Proof. by rewrite -cardsT; exact: leq_chi. Qed.

Lemma g261_chi_K (n : nat) : χ([set: 'K_n]) = n.
Proof. by rewrite chi_clique ?cardsT ?card_ord // => x y _ _. Qed.

(** A Boolean event that fails at arbitrarily large n is not with high probability. *)
Lemma g261_not_whp (T : nat -> finType) (w : forall n : nat, T n -> nat) (P : forall n : nat, pred (T n)) :
  (forall N : nat, exists2 n : nat, N <= n & forall x : T n, ~~ P n x) -> ~ fg_whp w P.
Proof.
move=> h /(_ 1 2 isT isT) [N hN]; have [n Nn nP] := h N; have [tot] := hN n Nn.
have -> : fg_event_weight (w n) (P n) = 0
  by rewrite /fg_event_weight big_pred0 // => x; apply/negbTE; exact: nP.
by rewrite muln0 leqn0 mul1n => /eqP t0; move: tot; rewrite t0.
Qed.

(** fg_whp is monotone in the event. *)
Lemma g261_whp_mono (T : nat -> finType) (w : forall n : nat, T n -> nat) (P Q : forall n : nat, pred (T n)) :
  (forall n (x : T n), P n x -> Q n x) -> fg_whp w P -> fg_whp w Q.
Proof.
move=> PQ h a b a0 ab; have [N hN] := h a b a0 ab; exists N => n Nn; have [tot hP] := hN n Nn.
split => //; apply: leq_trans hP _; rewrite leq_mul2l; apply/orP; right.
rewrite /fg_event_weight [X in X <= _]big_mkcond [X in _ <= X]big_mkcond /=.
by apply: leq_sum => x _; case: ifP => // /PQ ->.
Qed.

Lemma g261_card_labelled (n : nat) (E : {set {set 'I_n}}) : #|fg_labelled_sgraph E| = n.
Proof. exact: card_ord. Qed.

(** ** helper_sanity: cochromatic colourings *)

Lemma g261_K3_at_most1 : x261_cochromatic_at_most ('K_3) 1.
Proof.
apply/existsP; exists [ffun _ => ord0]; apply/forallP => i; apply/orP; left.
by apply/cliqueP => x y _ _.
Qed.

Lemma g261_K3_exact1 : x261_cochromatic_exact ('K_3) 1.
Proof.
rewrite /x261_cochromatic_exact g261_K3_at_most1 /=; apply/forallP => -[[|j] Hj] //.
exact: (g261_cochromatic_at_most0 (ord0 : 'K_3)).
Qed.

Lemma g261_P3_not_at_most1 : ~~ x261_cochromatic_at_most (ordinal_path 3) 1.
Proof.
apply/existsP => -[col /forallP /(_ ord0)].
have inS : forall v : ordinal_path 3, v \in [set v | col v == ord0]
  by move=> v; rewrite inE; case: (col v) => -[|m] // Hm; apply/eqP; apply: val_inj.
case/orP => [/cliqueP c | /stableP s].
- by have := c (@Ordinal 3 0 isT) (@Ordinal 3 2 isT) (inS _) (inS _) isT.
- by have := s (@Ordinal 3 0 isT) (@Ordinal 3 1 isT) (inS _) (inS _).
Qed.

Lemma g261_P3_at_most2 : x261_cochromatic_at_most (ordinal_path 3) 2.
Proof.
apply/existsP.
exists [ffun v : ordinal_path 3 => if val v == 1 then (@Ordinal 2 1 isT) else (@Ordinal 2 0 isT)].
apply/forallP => -[[|[|i]] Hi] //; apply/orP.
- right; apply/stableP => x y; rewrite !inE !ffunE.
  by case: x => -[|[|[|x]]] Hx //; case: y => -[|[|[|y]]] Hy.
- left; apply/cliqueP => x y; rewrite !inE !ffunE.
  by case: x => -[|[|[|x]]] Hx //; case: y => -[|[|[|y]]] Hy.
Qed.

Lemma g261_P3_exact2 : x261_cochromatic_exact (ordinal_path 3) 2.
Proof.
rewrite /x261_cochromatic_exact g261_P3_at_most2 /=; apply/forallP => -[[|[|j]] Hj] //.
- exact: (g261_cochromatic_at_most0 (@Ordinal 3 0 isT : ordinal_path 3)).
- exact: g261_P3_not_at_most1.
Qed.

Lemma g261_P3_not_exact3 : ~~ x261_cochromatic_exact (ordinal_path 3) 3.
Proof.
rewrite /x261_cochromatic_exact negb_and; apply/orP; right.
by apply/forallP => /(_ (@Ordinal 3 2 isT)); rewrite g261_P3_at_most2.
Qed.

(** K_3 has zeta 1, P_3 has zeta 2 (not 1, not 3): colour classes must induce a complete or an empty graph. *)
Definition g261_co_helper_claim : Prop :=
  [/\ x261_cochromatic_exact ('K_3) 1, ~~ x261_cochromatic_at_most (ordinal_path 3) 1,
      x261_cochromatic_exact (ordinal_path 3) 2 & ~~ x261_cochromatic_exact (ordinal_path 3) 3].

Theorem g261_co_helper_sanity : g261_co_helper_claim.
Proof.
by split; [exact: g261_K3_exact1 | exact: g261_P3_not_at_most1 | exact: g261_P3_exact2 | exact: g261_P3_not_exact3].
Qed.

(** ** helper_sanity: clique subdivisions *)

(** C_5 contains a subdivision of K_3: branch vertices 0, 1, 2; the pair (0, 2) is joined through 4 and 3. *)
Lemma g261_C5_tclique3 : x261_topological_clique (cycle_graph 5) 3.
Proof.
pose b (i : 'I_3) : cycle_graph 5 := widen_ord (isT : 3 <= 5) i.
pose p (i j : 'I_3) : seq (cycle_graph 5) :=
  if (val i == 0) && (val j == 2) then [:: @Ordinal 5 4 isT; @Ordinal 5 3 isT] else [::].
have pP : forall i j x, x \in p i j -> [/\ val i = 0, val j = 2 & (val x == 4) || (val x == 3)].
  move=> i j x; rewrite /p; case: ifP => [/andP [/eqP -> /eqP ->]|] //.
  by rewrite !inE => /orP [] /eqP ->.
exists b, p; split.
- by move=> i j /(congr1 val) /= /val_inj.
- by case=> -[|[|[|i]]] Hi //; case=> -[|[|[|j]]] Hj.
- move=> i j l x _ /pP [_ _ hx]; move: hx; apply: contraL => /eqP ->.
  by case: l => -[|[|[|l]]] Hl.
- move=> i j i' j' x _ _ /pP [hi hj _] /pP [hi' hj' _].
  by split; apply: val_inj; [rewrite hi hi' | rewrite hj hj'].
Qed.

(** P_3 contains no subdivision of K_3: all three vertices would be branch vertices, the interiors would be empty, and
    the two ends would have to be adjacent. *)
Lemma g261_P3_no_tclique3 : ~ x261_topological_clique (ordinal_path 3) 3.
Proof.
move=> [b [p [binj hpath havoid _]]].
have onto : forall y : ordinal_path 3, exists l, b l = y.
  move=> y; have : y \in codom b by apply: inj_card_onto binj _ y; rewrite !card_ord.
  by case/codomP => l ->; exists l.
have empty : forall i j : 'I_3, i < j -> p i j = [::].
  move=> i j ij; case e: (p i j) => [|x s] //; have [l bl] := onto x.
  by have := havoid i j l x ij; rewrite e mem_head bl eqxx => /(_ isT).
have [l0 b0] := onto (@Ordinal 3 0 isT); have [l2 b2] := onto (@Ordinal 3 2 isT).
case: (ltngtP l0 l2) => [lt|lt|eq].
- by have := hpath l0 l2 lt; rewrite empty //= b0 b2.
- by have := hpath l2 l0 lt; rewrite empty //= b0 b2.
- by move: b2; rewrite -(val_inj eq) b0 => /(congr1 val).
Qed.

Lemma g261_K3_tclique3 : x261_topological_clique ('K_3) 3.
Proof.
exists id, (fun _ _ => [::]); split => // i j ij.
have ne : i != j by rewrite neq_ltn ij.
by rewrite /= !andbT inE; apply/andP; split; [exact: ne | exact: ne].
Qed.

Lemma g261_K3_order3 : x261_clique_subdivision_order ('K_3) 3.
Proof.
split; first exact: g261_K3_tclique3.
by move=> t [b [p [binj _ _ _]]]; have := leq_card b binj; rewrite !card_ord.
Qed.

Lemma g261_K3_not_order2 : ~ x261_clique_subdivision_order ('K_3) 2.
Proof. by move=> [_ /(_ 3 g261_K3_tclique3)]. Qed.

(** C_5 has a subdivided K_3 although it has no triangle; P_3 (a tree) has none; sigma(K_3) = 3, not 2. *)
Definition g261_sd_helper_claim : Prop :=
  [/\ x261_topological_clique (cycle_graph 5) 3, ~ x261_topological_clique (ordinal_path 3) 3,
      x261_clique_subdivision_order ('K_3) 3 & ~ x261_clique_subdivision_order ('K_3) 2].

Theorem g261_sd_helper_sanity : g261_sd_helper_claim.
Proof.
by split; [exact: g261_C5_tclique3 | exact: g261_P3_no_tclique3 | exact: g261_K3_order3 | exact: g261_K3_not_order2].
Qed.

(** ** helper_sanity: acyclic colourings *)

Lemma g261_undup_size_card (T : finType) (s : seq T) : size (undup s) <= #|T|.
Proof. by rewrite -(card_uniqP (undup_uniq s)); exact: max_card. Qed.

(** C_4 has no acyclic 2-colouring: the whole cycle would use two colours. *)
Lemma g261_C4_not_acyclic2 : ~ x261_acyclic_colourable (cycle_graph 4) 2.
Proof.
move=> [f [_ fC]].
have := fC [:: @Ordinal 4 0 isT; @Ordinal 4 1 isT; @Ordinal 4 2 isT; @Ordinal 4 3 isT] isT isT.
by rewrite ltnNge (leq_trans (g261_undup_size_card _)) ?card_ord.
Qed.

(** C_4 has an acyclic 3-colouring: colours 0, 1, 0, 2 around the cycle; its only cycle of length at least 3 is the
    whole C_4, which sees all three colours. *)
Lemma g261_C4_acyclic3 : x261_acyclic_colourable (cycle_graph 4) 3.
Proof.
pose f (v : cycle_graph 4) : 'I_3 :=
  if val v == 1 then @Ordinal 3 1 isT else if val v == 3 then @Ordinal 3 2 isT else @Ordinal 3 0 isT.
exists f; split.
  by case=> -[|[|[|[|x]]]] Hx //; case=> -[|[|[|[|y]]]] Hy.
case=> [|x [|y [|z [|w [|u c]]]]] //=.
- by case: x => -[|[|[|[|x]]]] Hx //; case: y => -[|[|[|[|y]]]] Hy //; case: z => -[|[|[|[|z]]]] Hz.
- by case: x => -[|[|[|[|x]]]] Hx //; case: y => -[|[|[|[|y]]]] Hy //; case: z => -[|[|[|[|z]]]] Hz //;
     case: w => -[|[|[|[|w]]]] Hw.
- move=> /andP [_ U] _; have := max_card (mem [:: x, y, z, w, u & c]).
  by rewrite (card_uniqP U) card_ord.
Qed.

(** C_4: acyclically 3-colourable, not 2-colourable acyclically (although it is properly 2-colourable). *)
Definition g261_ac_helper_claim : Prop :=
  x261_acyclic_colourable (cycle_graph 4) 3 /\ ~ x261_acyclic_colourable (cycle_graph 4) 2.

Theorem g261_ac_helper_sanity : g261_ac_helper_claim.
Proof. by split; [exact: g261_C4_acyclic3 | exact: g261_C4_not_acyclic2]. Qed.

(** The same notion as Chromatic.conjectures.U4's list form [acyclic_colouring] with every list the whole palette. *)
Lemma g261_acyclic_colourableE (G : sgraph) (k : nat) :
  x261_acyclic_colourable G k <-> exists f : G -> 'I_k, acyclic_colouring (fun _ => [set: 'I_k]) f.
Proof.
split => [[f [fP fC]]|[f [_ fP fC]]]; exists f.
  by split => // v; rewrite inE.
by split => // c uc; exact: fC.
Qed.

(** ** Choosability: the Boolean palette form and GTBase's [choosable] *)

Lemma g261_choosable_bP (G : sgraph) (k : nat) :
  choosable G k -> x261_choosable_b G k.
Proof.
move=> ch; apply/forallP => L; apply/implyP => /forallP sz.
have [f [fL fP]] := ch _ (fun v => L v) (fun v => sz v).
apply/existsP; exists [ffun v => f v]; apply/andP; split.
- by apply/forallP => v; rewrite ffunE.
- apply/forallP => x; apply/forallP => y; apply/implyP => xy; rewrite !ffunE; exact: fP.
Qed.

(** The converse, over any finite palette: keep the first k colours of every list, index all of them in one
    sequence of length #|G| * k, colour there and pull the colouring back. *)
Lemma g261_choosable_b_choosable (G : sgraph) (k : nat) :
  x261_choosable_b G k -> choosable G k.
Proof.
move=> /forallP hb C L szL.
have [G0|Gpos] := posnP #|G|.
  have nv : forall v : G, False by move=> v; move/card0_eq: G0 => /(_ v); rewrite !inE.
  by exists (fun v => False_rect C (nv v)); split => [v|x y]; case: (nv v) || case: (nv x).
have [v0 _] := card_gt0P Gpos.
have [k0|kpos] := posnP k.
  subst k; have := hb [ffun _ => set0].
  have -> : [forall v, 0 <= #|([ffun _ => set0] : {ffun G -> {set 'I_(#|G| * 0)}}) v|] by apply/forallP.
  by move=> /existsP [f _]; case: (f v0) => m; rewrite muln0.
have Npos : 0 < #|G| * k by rewrite muln_gt0 Gpos kpos.
(* the first k colours of each list, and all of them in one sequence of length #|G| * k *)
pose sv (v : G) := take k (enum (L v)).
pose pal := [seq y | x <- enum G, y <- sv x].
have szsv : forall v, size (sv v) = k by move=> v; rewrite size_takel // -cardE; exact: szL.
have szpal : size pal = #|G| * k.
  rewrite /pal size_allpairs_dep.
  have -> : [seq size (sv x) | x <- enum G] = nseq (size (enum G)) k
    by elim: (enum G) => //= x s ->; rewrite szsv.
  by rewrite sumn_nseq -cardE mulnC.
(* a colour's position in [pal], injective on [pal] *)
pose g (c : C) : 'I_(#|G| * k) := insubd (Ordinal Npos) (index c pal).
have palP : forall v c, c \in sv v -> c \in pal
  by move=> v c cv; apply/allpairsPdep; exists v, c; rewrite mem_enum.
have gval : forall c, c \in pal -> val (g c) = index c pal.
  move=> c cp; have lt : index c pal < #|G| * k by rewrite -szpal index_mem.
  by rewrite /g val_insubd lt.
have ginj : {in pal &, injective g}.
  move=> c1 c2 c1p c2p /(congr1 val); rewrite !gval // => e.
  by rewrite -(nth_index c1 c1p) e nth_index.
pose L2 : {ffun G -> {set 'I_(#|G| * k)}} := [ffun v => g @: [set c | c \in sv v]].
have szL2 : forall v, k <= #|L2 v|.
  move=> v; rewrite ffunE card_in_imset.
    move=> c1 c2; rewrite !inE => c1v c2v; apply: ginj; [exact: palP c1v | exact: palP c2v].
  rewrite cardsE; have /card_uniqP -> : uniq (sv v) by rewrite take_uniq // enum_uniq.
  by rewrite szsv.
have /existsP [f2 /andP [/forallP f2L /forallP f2P]] := implyP (hb L2) (introT forallP szL2).
(* pull the colouring back along [g] *)
have back : forall v, exists2 c, c \in sv v & f2 v = g c.
  move=> v; have := f2L v; rewrite ffunE => /imsetP [c]; rewrite inE => cv ->.
  by exists c.
have [c0 _] : exists c0 : C, c0 \in L v0 by apply/card_gt0P; exact: leq_trans kpos (szL v0).
pose f (v : G) := nth c0 pal (val (f2 v)).
have fE : forall v c, c \in sv v -> f2 v = g c -> f v = c.
  by move=> v c cv e; rewrite /f e gval ?nth_index ?(palP v).
exists f; split.
  move=> v; have [c cv e] := back v; rewrite (fE v c cv e).
  by move: cv; rewrite /sv => /mem_take; rewrite mem_enum.
move=> x y xy; have [cx cxv ex] := back x; have [cy cyv ey] := back y.
rewrite (fE x cx cxv ex) (fE y cy cyv ey).
apply: contraNneq (implyP (forallP (f2P x) y) xy) => exy.
by rewrite ex ey exy.
Qed.

Lemma g261_choosable_bE (G : sgraph) (k : nat) : x261_choosable_b G k <-> choosable G k.
Proof. by split; [exact: g261_choosable_b_choosable | exact: g261_choosable_bP]. Qed.

(** No list colouring into 'I_0 once G has a vertex. *)
Lemma g261_choosable_b0 (G : sgraph) (v : G) : ~~ x261_choosable_b G 0.
Proof.
apply/negP => /forallP /(_ [ffun _ => set0]) /implyP.
have -> : [forall v0, 0 <= #|([ffun _ => set0] : {ffun G -> {set 'I_(#|G| * 0)}}) v0|] by apply/forallP.
by move=> /(_ isT) /existsP [f _]; case: (f v) => m; rewrite muln0.
Qed.

(** ** helper_sanity: choosability *)

Lemma g261_K2_choosable2 : choosable ('K_2) 2.
Proof.
move=> C L szL.
have [c1 c1L] : exists c1, c1 \in L ord0 by apply/card_gt0P; exact: leq_trans _ (szL ord0).
have [c2 c2L] : exists c2, c2 \in L ord_max :\ c1.
  apply/card_gt0P; move: (szL ord_max); rewrite (cardsD1 c1).
  by case: (c1 \in L ord_max) => //=; rewrite add0n => /ltnW.
move: c2L; rewrite !inE => /andP [c21 c2L].
exists (fun v => if v == ord0 then c1 else c2); split.
  case=> -[|[|v]] Hv //=.
    by rewrite (_ : Ordinal Hv = ord0) //; apply: val_inj.
  by have -> : Ordinal Hv = ord_max by apply: val_inj.
by case=> -[|[|x]] Hx //; case=> -[|[|y]] Hy //= _; rewrite // eq_sym.
Qed.

Lemma g261_K2_not_choosable1 : ~~ x261_choosable_b ('K_2) 1.
Proof.
have h0 : 0 < #|'K_2| * 1 by rewrite card_ord.
apply/negP => /forallP /(_ [ffun _ => [set Ordinal h0]]) /implyP.
have -> : [forall v, 1 <= #|([ffun _ => [set Ordinal h0]] : {ffun 'K_2 -> {set 'I_(#|'K_2| * 1)}}) v|]
  by apply/forallP => v; rewrite ffunE cards1.
move=> /(_ isT) /existsP [f /andP [/forallP fL /forallP fP]].
have := fP ord0; move/forallP/(_ ord_max)/implyP/(_ isT).
by have := fL ord0; have := fL ord_max; rewrite !ffunE !inE => /eqP -> /eqP ->; rewrite eqxx.
Qed.

(** K_2 is 2-choosable and not 1-choosable with lists from the Boolean palette. *)
Definition g261_ch_helper_claim : Prop :=
  x261_choosable_b ('K_2) 2 /\ ~~ x261_choosable_b ('K_2) 1.

Theorem g261_ch_helper_sanity : g261_ch_helper_claim.
Proof. by split; [exact: g261_choosable_bP g261_K2_choosable2 | exact: g261_K2_not_choosable1]. Qed.

(** ** erdos:625 *)

(** hyp_inhabited: zeta(K_3) = 1; the statement at M = 0. *)
Definition g261_co_hyp_claim : Prop :=
  x261_cochromatic_exact ('K_3) 1 /\
  (random_graph_chi_minus_cochromatic_unbounded_statement ->
     @fg_whp (fun n : nat => {set {set 'I_n}}) (fun n => @fg_gnp_weight 1 2 n)
       (fun n E => let G := fg_labelled_sgraph E in
          [forall z : 'I_n.+1, x261_cochromatic_exact G z ==> (z + 0 <= χ([set: G]))])).

Theorem g261_co_hyp_inhabited : g261_co_hyp_claim.
Proof. by split; [exact: g261_K3_exact1 | move=> h; exact: h 0]. Qed.

(** not_trivially_true: without the cochromatic-number hypothesis, z = n and M = 1 empty the event. *)
Definition g261_co_no_number : Prop :=
  forall M : nat,
    @fg_whp (fun n : nat => {set {set 'I_n}}) (fun n => @fg_gnp_weight 1 2 n)
      (fun n E => [forall z : 'I_n.+1, z + M <= χ([set: fg_labelled_sgraph E])]).

Definition g261_co_ntt_claim : Prop :=
  ~ g261_co_no_number /\ (g261_co_no_number -> random_graph_chi_minus_cochromatic_unbounded_statement).

Theorem g261_co_not_trivially_true : g261_co_ntt_claim.
Proof.
split.
- move=> h; have := h 1; apply: g261_not_whp => N; exists N => // E.
  apply/negP => /forallP /(_ ord_max) /=; rewrite addn1 => hz.
  by have := leq_trans hz (g261_chi_le_card _); rewrite g261_card_labelled ltnn.
- move=> h M; apply: g261_whp_mono (h M) => n E /forallP hz.
  by apply/forallP => z; apply/implyP => _; exact: hz.
Qed.

(** ** erdos:717 *)

(** hyp_inhabited: sigma(K_3) = 3; the statement at K_3. *)
Definition g261_sd_hyp_claim : Prop :=
  x261_clique_subdivision_order ('K_3) 3 /\
  (chi_clique_subdivision_root_log_statement ->
     exists C : nat, (χ([set: 'K_3]) * trunc_log 2 #|'K_3|) ^ 2 <= C * #|'K_3| * 3 ^ 2).

Theorem g261_sd_hyp_inhabited : g261_sd_hyp_claim.
Proof.
split; first exact: g261_K3_order3.
by move=> [C hC]; exists C; exact: hC g261_K3_order3.
Qed.

(** not_trivially_true: without the sigma hypothesis, s = 0 at K_2 asks 4 <= 0. *)
Definition g261_sd_no_number : Prop :=
  exists C : nat, forall (G : sgraph) (s : nat), (χ([set: G]) * trunc_log 2 #|G|) ^ 2 <= C * #|G| * s ^ 2.

Definition g261_sd_ntt_claim : Prop :=
  ~ g261_sd_no_number /\ (g261_sd_no_number -> chi_clique_subdivision_root_log_statement).

Theorem g261_sd_not_trivially_true : g261_sd_ntt_claim.
Proof.
split.
- by move=> [C /(_ ('K_2) 0)]; rewrite g261_chi_K card_ord exp0n // muln0.
- by move=> [C hC]; exists C => G s _; exact: hC.
Qed.

(** ** erdos:760 *)

(** hyp_inhabited: chi(K_3) = 3 >= 2; the statement at K_3. *)
Definition g261_zh_hyp_claim : Prop :=
  [/\ χ([set: 'K_3]) = 3, 2 <= 3 &
      (subgraph_large_cochromatic_number_statement ->
         exists C : nat, exists H : sgraph, has_subgraph ('K_3) H /\
           forall k : nat, x261_cochromatic_at_most H k -> 3 <= C * k * trunc_log 2 3)].

Theorem g261_zh_hyp_inhabited : g261_zh_hyp_claim.
Proof.
split; [exact: g261_chi_K | by [] |].
by move=> [C hC]; exists C; exact: hC ('K_3) 3 (g261_chi_K 3) isT.
Qed.

(** not_trivially_true: without the guard 2 <= m, K_1 (m = 1, log 1 = 0) asks 1 <= 0 for every subgraph. *)
Definition g261_zh_no_guard : Prop :=
  exists C : nat, forall (G : sgraph) (m : nat), χ([set: G]) = m ->
    exists H : sgraph, has_subgraph G H /\
      forall k : nat, x261_cochromatic_at_most H k -> m <= C * k * trunc_log 2 m.

Definition g261_zh_ntt_claim : Prop :=
  ~ g261_zh_no_guard /\ (g261_zh_no_guard -> subgraph_large_cochromatic_number_statement).

Theorem g261_zh_not_trivially_true : g261_zh_ntt_claim.
Proof.
split.
- move=> [C /(_ ('K_1) 1 (g261_chi_K 1)) [H [_ /(_ #|H| (g261_cochromatic_card H))]]].
  by rewrite (_ : trunc_log 2 1 = 0) // muln0.
- by move=> [C hC]; exists C => G m hm _; exact: hC.
Qed.

(** ** erdos:797 *)

Lemma g261_Delta_K2 : Delta ('K_2) = 1.
Proof.
have N1 : forall (x : 'K_2), #|N(x)| = 1.
  move=> x; rewrite (_ : N(x) = [set~ x]) ?cardsC1 ?card_ord //.
  by apply/setP => y; rewrite !inE eq_sym.
apply/eqP; rewrite eqn_leq; apply/andP; split.
  by apply/bigmax_leqP => x _; rewrite N1.
by rewrite /Delta; apply: leq_trans (leq_bigmax ord0); rewrite N1.
Qed.

(** An acyclic colouring is proper, so K_m needs m colours. *)
Lemma g261_acyclic_K (m k : nat) : x261_acyclic_colourable ('K_m) k -> m <= k.
Proof.
move=> [f [fP _]]; have finj : injective f by move=> x y; apply: contra_eq => xy; exact: fP xy.
by have := leq_card f finj; rewrite !card_ord.
Qed.

(** hyp_inhabited: K_2 has maximum degree 1; the statement at q = 1. *)
Definition g261_ac_hyp_claim : Prop :=
  [/\ 0 < 1, Delta ('K_2) = 1 &
      (acyclic_chromatic_max_degree_subquadratic_statement ->
         eventually (fun d : nat => forall G : sgraph, Delta G = d ->
           exists k : nat, x261_acyclic_colourable G k /\ 1 * k <= d ^ 2))].

Theorem g261_ac_hyp_inhabited : g261_ac_hyp_claim.
Proof. by split; [by [] | exact: g261_Delta_K2 | move=> h; exact: h 1 isT]. Qed.

(** not_trivially_true: without Delta G = d, the complete graph on d^2 + 1 vertices needs more than d^2 colours. *)
Definition g261_ac_no_degree : Prop :=
  forall q : nat, 0 < q -> eventually (fun d : nat =>
    forall G : sgraph, exists k : nat, x261_acyclic_colourable G k /\ q * k <= d ^ 2).

Definition g261_ac_ntt_claim : Prop :=
  ~ g261_ac_no_degree /\ (g261_ac_no_degree -> acyclic_chromatic_max_degree_subquadratic_statement).

Theorem g261_ac_not_trivially_true : g261_ac_ntt_claim.
Proof.
split.
- move=> /(_ 1 isT) [N /(_ N (leqnn N) ('K_((N ^ 2).+1))) [k [/g261_acyclic_K hk]]].
  by rewrite mul1n => hk2; have := leq_trans hk hk2; rewrite ltnn.
- by move=> h q hq; have [N hN] := h q hq; exists N => d Nd G _; exact: hN.
Qed.

(** ** erdos:799 *)

(** hyp_inhabited: q = 1 meets 0 < q; the statement at q = 1. *)
Definition g261_ch_hyp_claim : Prop :=
  0 < 1 /\
  (almost_all_graphs_choice_number_sublinear_statement ->
     @fg_whp (fun n : nat => {set {set 'I_n}}) (fun n => @fg_gnp_weight 1 2 n)
       (fun n E => x261_choosable_b (fg_labelled_sgraph E) (n %/ 1))).

Theorem g261_ch_hyp_inhabited : g261_ch_hyp_claim.
Proof. by split => // h; exact: h 1 isT. Qed.

(** not_trivially_true: without 0 < q, q = 0 asks for lists of 0 colours, and no graph with a vertex has them. *)
Definition g261_ch_no_guard : Prop :=
  forall q : nat,
    @fg_whp (fun n : nat => {set {set 'I_n}}) (fun n => @fg_gnp_weight 1 2 n)
      (fun n E => x261_choosable_b (fg_labelled_sgraph E) (n %/ q)).

Definition g261_ch_ntt_claim : Prop :=
  ~ g261_ch_no_guard /\ (g261_ch_no_guard -> almost_all_graphs_choice_number_sublinear_statement).

Theorem g261_ch_not_trivially_true : g261_ch_ntt_claim.
Proof.
split.
- move=> h; have := h 0; apply: g261_not_whp => N; exists N.+1 => // E.
  by rewrite divn0; exact: (@g261_choosable_b0 (fg_labelled_sgraph E) ord0).
- by move=> h q _; exact: h q.
Qed.

Print Assumptions g261_co_helper_sanity.
Print Assumptions g261_sd_helper_sanity.
Print Assumptions g261_ac_helper_sanity.
Print Assumptions g261_ch_helper_sanity.
Print Assumptions g261_co_hyp_inhabited.
Print Assumptions g261_co_not_trivially_true.
Print Assumptions g261_sd_hyp_inhabited.
Print Assumptions g261_sd_not_trivially_true.
Print Assumptions g261_zh_hyp_inhabited.
Print Assumptions g261_zh_not_trivially_true.
Print Assumptions g261_ac_hyp_inhabited.
Print Assumptions g261_ac_not_trivially_true.
Print Assumptions g261_ch_hyp_inhabited.
Print Assumptions g261_ch_not_trivially_true.
Print Assumptions g261_cochromatic_at_mostP.
Print Assumptions g261_choosable_bE.
Print Assumptions g261_acyclic_colourableE.
