(** * Cycle.foundations.comp_reduce — reducing a bridgeless multigraph to a
      CONNECTED bridgeless multigraph

    Several cycle-theory rows are stated for CONNECTED bridgeless multigraphs
    ([two_edge_connected]) while their consequences are wanted for all
    bridgeless multigraphs.  This file supplies the missing reduction for
    properties of the "double cover by even subgraphs" kind.

    Construction.  Pick one representative [mroot v] in every connected
    component and COLLAPSE all representatives onto a single vertex [r0]: the
    carrier [Vsub r0] consists of the non-representatives together with [r0],
    and [Hc r0] is the multigraph on [Vsub r0] with the SAME EDGE TYPE as [G],
    each endpoint pushed forward by [prj r0].  Then

    - [Hc r0] is connected (every vertex reaches its representative inside its
      own component, and all representatives are [r0]);
    - [Hc r0] is bridgeless (collapsing only ADDS walks, so a bridge of
      [Hc r0] is a bridge of [G]);
    - an edge set is an even subgraph of [Hc r0] iff it is one of [G]: at a
      non-representative vertex the two degrees are literally equal, and at a
      representative the degree is even because the [G]-degree sum over its
      whole component is even (no [G]-edge leaves a component) while all the
      other summands are.

    Since the edge types agree, a double cover of [Hc r0] by even subgraphs IS
    a double cover of [G] by even subgraphs, with no edge bookkeeping at all. *)

From GraphTheory Require Import mgraph.
From GTBase Require Export base.
From Cycle.foundations Require Export cycle_space.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Concatenation and reversal of undirected walks *)

Lemma uwalk_cat (G : mgraph) (w1 w2 : seq (edge G)) (x y z : G) :
  uwalk x y w1 -> uwalk y z w2 -> uwalk x z (w1 ++ w2).
Proof.
elim: w1 x => [x /eqP -> //|e w1 IH x h1 h2].
have [/andP[/eqP hx hw]|/andP[/eqP hx hw]] := orP h1.
- by apply: uwalk_cons; [exact: hx | exact: IH hw h2].
- by apply: uwalk_cons_rev; [exact: hx | exact: IH hw h2].
Qed.

Lemma uwalk_rev (G : mgraph) (w : seq (edge G)) (x y : G) :
  uwalk x y w -> uwalk y x (rev w).
Proof.
elim: w x => [x /eqP ->|e w IH x h]; first by rewrite /= eqxx.
rewrite rev_cons -cats1.
have [/andP[/eqP hx hw]|/andP[/eqP hx hw]] := orP h.
- apply: (@uwalk_cat G (rev w) [:: e] y (target e) x); first exact: IH hw.
  by apply: uwalk_one_rev.
- apply: (@uwalk_cat G (rev w) [:: e] y (source e) x); first exact: IH hw.
  by apply: uwalk_one.
Qed.

(** ** Reachability in a multigraph *)

Definition mrel (G : mgraph) : rel G :=
  fun x y => [exists e : edge G,
    ((source e == x) && (target e == y)) || ((source e == y) && (target e == x))].

Lemma mrel_sym (G : mgraph) : symmetric (@mrel G).
Proof.
move=> x y; apply/idP/idP => /existsP[e he]; apply/existsP; exists e;
  by rewrite orbC.
Qed.

Lemma mrel_uwalk (G : mgraph) (x y : G) :
  connect (@mrel G) x y -> exists w, uwalk x y w.
Proof.
case/connectP => p; elim: p x => [x _ hl|z p IH x /= /andP[hx hp] hl].
  have hxy : x = y by move: hl.
  by exists [::]; rewrite /= hxy eqxx.
have [w hw] := IH z hp hl.
case/existsP: hx => e /orP[/andP[/eqP hs /eqP ht]|/andP[/eqP hs /eqP ht]].
- by exists (e :: w); apply: uwalk_cons; [exact: hs | rewrite ht].
- by exists (e :: w); apply: uwalk_cons_rev; [exact: ht | rewrite hs].
Qed.

Definition mcomp (G : mgraph) (x : G) : {set G} := [set y | connect (@mrel G) x y].

Lemma mcompP (G : mgraph) (x y : G) : (y \in mcomp x) = connect (@mrel G) x y.
Proof. by rewrite inE. Qed.

Lemma mcomp_id (G : mgraph) (x : G) : x \in mcomp x.
Proof. by rewrite inE connect0. Qed.

Lemma mcomp_eq (G : mgraph) (x y : G) :
  connect (@mrel G) x y -> mcomp x = mcomp y.
Proof.
move=> hxy; apply/setP => z; rewrite !inE; apply/idP/idP => h.
- have hyx : connect (@mrel G) y x by rewrite (sym_connect_sym (@mrel_sym G)).
  exact: (@connect_trans _ (@mrel G) x y z hyx h).
- exact: (@connect_trans _ (@mrel G) y x z hxy h).
Qed.

Lemma mrel_ep (G : mgraph) (e : edge G) (b : bool) :
  mrel (endpoint b e) (endpoint (~~ b) e).
Proof.
apply/existsP; exists e.
by case: b => /=; rewrite !eqxx ?orbT.
Qed.

Lemma mcomp_closed (G : mgraph) (x : G) (e : edge G) (b : bool) :
  endpoint b e \in mcomp x -> endpoint (~~ b) e \in mcomp x.
Proof.
rewrite !mcompP => h.
apply: (@connect_trans _ (@mrel G) (endpoint b e) x (endpoint (~~ b) e) h).
by apply: connect1; exact: mrel_ep.
Qed.

Lemma cut_mcomp (G : mgraph) (x : G) : cut (mcomp x) = set0.
Proof.
apply/setP => e; rewrite in_set0 /cut in_set.
have h1 : (source e \in mcomp x) -> (target e \in mcomp x).
  exact: (@mcomp_closed G x e false).
have h2 : (target e \in mcomp x) -> (source e \in mcomp x).
  exact: (@mcomp_closed G x e true).
case E1: (source e \in mcomp x); case E2: (target e \in mcomp x) => //.
- by move: (h1 E1); rewrite E2.
- by move: (h2 E2); rewrite E1.
Qed.

(** ** One representative per component *)

Definition mroot (G : mgraph) (x : G) : G := odflt x [pick y | y \in mcomp x].

Lemma mroot_mem (G : mgraph) (x : G) : mroot x \in mcomp x.
Proof.
rewrite /mroot; case: pickP => [y hy|h] /=; first exact: hy.
exact: mcomp_id.
Qed.

Lemma mroot_eq (G : mgraph) (x y : G) :
  connect (@mrel G) x y -> mroot x = mroot y.
Proof.
move=> h; have hc := mcomp_eq h; rewrite /mroot.
have -> : [pick z | z \in mcomp x] = [pick z | z \in mcomp y] by rewrite hc.
case: pickP => //= h0.
by move: (h0 y); rewrite mcomp_id.
Qed.

Lemma mroot_root (G : mgraph) (x : G) : mroot (mroot x) = mroot x.
Proof.
apply: mroot_eq.
by rewrite (sym_connect_sym (@mrel_sym G)) -mcompP mroot_mem.
Qed.

Lemma mroot_unique (G : mgraph) (r y : G) :
  mroot r = r -> y \in mcomp r -> mroot y = y -> y = r.
Proof.
move=> hr hy hyy; rewrite mcompP in hy.
by rewrite -hyy -(mroot_eq hy) hr.
Qed.

(** ** The collapsed multigraph *)

Definition vpred (G : mgraph) (r0 : G) : pred G :=
  fun v => (mroot v != v) || (v == r0).

Definition Vsub (G : mgraph) (r0 : G) : finType := {v : G | vpred r0 v}.

Definition pr (G : mgraph) (r0 v : G) : G := if mroot v == v then r0 else v.

Lemma pr_mem (G : mgraph) (r0 v : G) : vpred r0 (pr r0 v).
Proof.
rewrite /vpred /pr; case: ifP => h; first by rewrite eqxx orbT.
by rewrite h.
Qed.

Definition prj (G : mgraph) (r0 v : G) : Vsub r0 := Sub (pr r0 v) (pr_mem r0 v).

Lemma val_prj (G : mgraph) (r0 v : G) : val (prj r0 v) = pr r0 v.
Proof. exact: SubK. Qed.

Definition Hc (G : mgraph) (r0 : G) : mgraph :=
  @Graph unit unit (Vsub r0) (edge G) (fun b e => prj r0 (endpoint b e))
         (fun _ => tt) (fun _ => tt).

Lemma Hc_ep (G : mgraph) (r0 : G) (b : bool) (e : edge G) :
  @endpoint unit unit (Hc r0) b e = prj r0 (endpoint b e).
Proof. by []. Qed.

Lemma pr_root (G : mgraph) (r0 v : G) : pr r0 (mroot v) = r0.
Proof. by rewrite /pr mroot_root eqxx. Qed.

Lemma pr_id (G : mgraph) (r0 : G) : mroot r0 = r0 -> forall u : Vsub r0, pr r0 (val u) = val u.
Proof.
move=> hr0 u; rewrite /pr; case: ifP => // h.
have := valP u; rewrite /vpred h /= => /eqP ->.
by [].
Qed.

Lemma prj_val (G : mgraph) (r0 : G) :
  mroot r0 = r0 -> forall u : Vsub r0, prj r0 (val u) = u.
Proof. by move=> hr0 u; apply: val_inj; rewrite val_prj (pr_id hr0). Qed.

Lemma prj_mroot (G : mgraph) (r0 v : G) : prj r0 (mroot v) = prj r0 r0.
Proof.
apply: val_inj; rewrite !val_prj pr_root /pr.
by case: ifP.
Qed.

Lemma Hc_uwalk (G : mgraph) (r0 : G) (x y : G) (w : seq (edge G)) :
  uwalk x y w -> @uwalk (Hc r0) (prj r0 x) (prj r0 y) w.
Proof.
elim: w x => [x /eqP ->|e w IH x h]; first by rewrite /= eqxx.
have [/andP[/eqP hx hw]|/andP[/eqP hx hw]] := orP h.
- apply: uwalk_cons; last exact: IH hw.
  by rewrite Hc_ep hx.
- apply: uwalk_cons_rev; last exact: IH hw.
  by rewrite Hc_ep hx.
Qed.

Lemma pr_eqE (G : mgraph) (r0 v w : G) :
  mroot r0 = r0 -> mroot v != v -> (pr r0 w == v) = (w == v).
Proof.
move=> hr0 hv; rewrite /pr; case: ifP => hw //.
have e1 : (r0 == v) = false.
  apply/negbTE; apply: contraNneq hv => <-; by rewrite hr0.
have e2 : (w == v) = false.
  apply/negbTE; apply/negP => /eqP hwv.
  by move: hw; rewrite hwv (negbTE hv).
by rewrite e1 e2.
Qed.

(** ** The reduction: a double cover by five even subgraphs transfers from the
       collapsed (connected) graph back to [G] *)

Lemma five_even_cover_connected_reduce (G : mgraph) :
  (forall H : mgraph, (0 < #|H|)%N -> mconnected H -> bridgeless H ->
     exists L : seq {set edge H},
       [/\ size L = 5,
           (forall C : {set edge H}, C \in L -> forall v : H, ~~ odd (subdeg C v))
         & (forall e : edge H, count (fun C : {set edge H} => e \in C) L = 2)]) ->
  (0 < #|G|)%N -> bridgeless G ->
  exists L : seq {set edge G},
    [/\ size L = 5,
        (forall C : {set edge G}, C \in L -> forall v : G, ~~ odd (subdeg C v))
      & (forall e : edge G, count (fun C : {set edge G} => e \in C) L = 2)].
Proof.
move=> Hstat Hn Hbl.
have /card_gt0P[x0 _] : (0 < #|[set: G]|)%N by rewrite cardsT.
set r0 := mroot x0.
have hr0 : mroot r0 = r0 := mroot_root x0.
have hcard : (0 < #|Hc r0|)%N by apply/card_gt0P; exists (prj r0 x0).
have hroute : forall u : Vsub r0, exists w, @uwalk (Hc r0) u (prj r0 r0) w.
  move=> u.
  have hc : connect (@mrel G) (val u) (mroot (val u)) by rewrite -mcompP mroot_mem.
  have [w hw] := mrel_uwalk hc.
  have h := @Hc_uwalk G r0 (val u) (mroot (val u)) w hw.
  rewrite (prj_val hr0) prj_mroot in h.
  by exists w.
have hconn : mconnected (Hc r0).
  move=> u u'.
  have [w1 hw1] := hroute u.
  have [w2 hw2] := hroute u'.
  exists (w1 ++ rev w2).
  apply: (@uwalk_cat (Hc r0) w1 (rev w2) u (prj r0 r0) u') => //.
  exact: uwalk_rev hw2.
have hbl : bridgeless (Hc r0).
  move=> e hbr; apply: (Hbl e); apply/is_bridgeP => w hw.
  have h := @Hc_uwalk G r0 _ _ w hw.
  by have /is_bridgeP hb := hbr; apply: hb; exact: h.
have [L [Lsize Leven Lcount]] := Hstat (Hc r0) hcard hconn hbl.
have keyends : forall (C : {set edge G}) (v : G) (h : vpred r0 v) (b : bool),
    mroot v != v -> #|@ends_at (Hc r0) C b (Sub v h)| = #|ends_at C b v|.
  move=> C v h b hv; apply: eq_card => f; rewrite !inE.
  by rewrite -val_eqE val_prj SubK (pr_eqE _ hr0 hv).
have keydeg : forall (C : {set edge G}) (v : G) (h : vpred r0 v),
    mroot v != v -> @subdeg (Hc r0) C (Sub v h) = subdeg C v.
  move=> C v h hv.
  by rewrite /subdeg (keyends C v h false hv) (keyends C v h true hv).
exists L; split => //.
move=> C hC v.
case: (boolP (mroot v == v)) => [/eqP hvr|hnr]; last first.
  have hv : vpred r0 v by rewrite /vpred hnr.
  by rewrite -(keydeg C v hv hnr); exact: (Leven C hC (Sub v hv)).
have hsum : ~~ odd (\sum_(y in mcomp v) subdeg C y).
  by rewrite sum_subdeg_cut (cut_mcomp v) setI0 cards0 addn0 oddM /=.
have hrest : ~~ odd (\sum_(y in mcomp v | y != v) subdeg C y).
  apply: odd_sum_even_P => y /andP[hy hyv].
  have hnr : mroot y != y.
    apply/negP => /eqP hyy.
    by move: hyv; rewrite (mroot_unique hvr hy hyy) eqxx.
  have hv : vpred r0 y by rewrite /vpred hnr.
  by rewrite -(keydeg C y hv hnr); exact: (Leven C hC (Sub y hv)).
by move: hsum; rewrite (bigD1 v (mcomp_id v)) /= oddD (negbTE hrest) addbF.
Qed.

(** ** The collapsed graph is connected, bridgeless and nonempty (reusable
       outside the even-cover reduction, e.g. for flows: gc:e246) *)

Lemma Hc_card_gt0 (G : mgraph) (r0 x : G) : (0 < #|Hc r0|)%N.
Proof. by apply/card_gt0P; exists (prj r0 x). Qed.

Lemma Hc_mconnected (G : mgraph) (r0 : G) : mroot r0 = r0 -> mconnected (Hc r0).
Proof.
move=> hr0.
have hroute : forall u : Vsub r0, exists w, @uwalk (Hc r0) u (prj r0 r0) w.
  move=> u.
  have hc : connect (@mrel G) (val u) (mroot (val u)) by rewrite -mcompP mroot_mem.
  have [w hw] := mrel_uwalk hc.
  have h := @Hc_uwalk G r0 (val u) (mroot (val u)) w hw.
  rewrite (prj_val hr0) prj_mroot in h.
  by exists w.
move=> u u'.
have [w1 hw1] := hroute u.
have [w2 hw2] := hroute u'.
exists (w1 ++ rev w2).
apply: (@uwalk_cat (Hc r0) w1 (rev w2) u (prj r0 r0) u') => //.
exact: uwalk_rev hw2.
Qed.

Lemma Hc_bridgeless (G : mgraph) (r0 : G) : bridgeless G -> bridgeless (Hc r0).
Proof.
move=> Hbl e hbr; apply: (Hbl e); apply/is_bridgeP => w hw.
have h := @Hc_uwalk G r0 _ _ w hw.
by have /is_bridgeP hb := hbr; apply: hb; exact: h.
Qed.
