(** * Digraph.conjectures.grounding_X216 — faithfulness grounding for wave X216

    GROUNDING (not new mathematics): satisfiability witnesses and guard-has-teeth
    facts for the single statement of [X216.v], the weighted Caccetta–Häggkvist
    conjecture [weighted_caccetta_haggkvist_statement] (corpus row bm:bm-070).

    Coverage:
      - NON-VACUITY: the whole hypothesis block is satisfiable by a concrete
        digraph — the digon [x216_dg2] (two vertices, both arcs, no loops) with
        all arc weights 1 — and the conclusion holds there ([x216_dg2_witness]).
      - GUARD 1 ([0 < #|D|]) HAS TEETH: the empty digraph satisfies every other
        hypothesis vacuously and has NO directed cycle at all
        ([x216_order_guard_has_teeth]).
      - GUARD 2 (looplessness) HAS TEETH: with loops allowed the statement is
        FALSE — [x216_dgl2] (two vertices, all four arcs including both loops)
        with loop weight 3/4 and digon weight 1/4 is strongly connected, has
        w^-(v) = w^+(v) = 1 at every vertex and positive weights, yet ALL of its
        directed cycles have weight below 1 ([x216_loopless_guard_has_teeth]).

    Every lemma is closed by [Qed]; the [Print Assumptions] audit at the end
    shows they are axiom-free. *)

From HB Require Import structures.
From mathcomp Require Import all_boot.
From mathcomp Require Import all_order all_algebra.
From Digraph Require Import prelude digraph oriented dipath strong tournament.
From Digraph Require Import X216.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.Theory GRing.Theory Num.Theory.

Local Open Scope ring_scope.

(** ** Two concrete two-vertex digraphs on [bool] *)

(** [x216_dg2]: the digon — two vertices, the two arcs between them, NO loop. *)
Definition x216_dg2 : Type := bool.
HB.instance Definition _ := Finite.on x216_dg2.
HB.instance Definition _ :=
  HasArc.Build x216_dg2 (fun u v : bool => u != v).

Lemma x216_dg2_arcE (u v : x216_dg2) : (u --> v) = (u != v).
Proof. by []. Qed.

(** [x216_dgl2]: the same two vertices with ALL four arcs, loops included. *)
Definition x216_dgl2 : Type := bool.
HB.instance Definition _ := Finite.on x216_dgl2.
HB.instance Definition _ :=
  HasArc.Build x216_dgl2 (fun _ _ : bool => true).

Lemma x216_dgl2_arcE (u v : x216_dgl2) : (u --> v) = true.
Proof. by []. Qed.

(** ** Non-vacuity: the digon with unit weights satisfies everything *)

Definition x216_w1 : x216_dg2 -> x216_dg2 -> rat := fun _ _ => 1.

Lemma x216_dg2_card : (0 < #|{: x216_dg2}|)%N.
Proof. by rewrite card_bool. Qed.

Lemma x216_dg2_loopless (v : x216_dg2) : ~~ (v --> v).
Proof. by rewrite x216_dg2_arcE eqxx. Qed.

Lemma x216_dg2_strong : strongb x216_dg2.
Proof.
apply/strongP => x y; have [->|nxy] := eqVneq x y; first exact: connect0.
by apply: connect1; rewrite x216_dg2_arcE.
Qed.

Lemma x216_dg2_wpos (u v : x216_dg2) : u --> v -> 0 < x216_w1 u v.
Proof. by move=> _; rewrite /x216_w1 ltr01. Qed.

Lemma x216_dg2_win (v : x216_dg2) : x216_win x216_w1 v = 1.
Proof.
rewrite /x216_win (bigD1 (~~ v)) /=; last by rewrite x216_dg2_arcE; case: v.
by rewrite big1 ?addr0 // => u /andP[]; rewrite x216_dg2_arcE; case: u; case: v.
Qed.

Lemma x216_dg2_wout (v : x216_dg2) : x216_wout x216_w1 v = 1.
Proof.
rewrite /x216_wout (bigD1 (~~ v)) /=; last by rewrite x216_dg2_arcE; case: v.
by rewrite big1 ?addr0 // => u /andP[]; rewrite x216_dg2_arcE; case: u; case: v.
Qed.

Lemma x216_dg2_dicycle : dicycle ([:: true; false] : seq x216_dg2).
Proof. by []. Qed.

Lemma x216_dg2_cycle_weight :
  x216_cycle_weight x216_w1 [:: true; false] = 1 + 1.
Proof. by rewrite /x216_cycle_weight big_cons big_cons big_nil addr0. Qed.

(** The full non-vacuity witness: every hypothesis of
    [weighted_caccetta_haggkvist_statement] holds for the digon with unit
    weights, and so does its conclusion. *)
Lemma x216_dg2_witness :
  [/\ (0 < #|{: x216_dg2}|)%N, (forall v : x216_dg2, ~~ (v --> v)),
      strongb x216_dg2,
      (forall u v : x216_dg2, u --> v -> 0 < x216_w1 u v)
    & (forall v : x216_dg2, 1 <= x216_win x216_w1 v)
      /\ (forall v : x216_dg2, 1 <= x216_wout x216_w1 v)]
  /\ (exists c : seq x216_dg2, dicycle c /\ 1 <= x216_cycle_weight x216_w1 c).
Proof.
split.
  split; try by [exact: x216_dg2_card | exact: x216_dg2_strong].
  - exact: x216_dg2_loopless.
  - exact: x216_dg2_wpos.
  split=> v; [by rewrite x216_dg2_win | by rewrite x216_dg2_wout].
exists [:: true; false]; split; first exact: x216_dg2_dicycle.
by rewrite x216_dg2_cycle_weight lerDl ler01.
Qed.

(** ** Guard 1 has teeth: the order guard [0 < #|D|] *)

(** The empty digraph has no directed cycle whatsoever. *)
Lemma x216_empty_no_dicycle (c : seq (TT 0 : diGraphType)) : ~~ dicycle c.
Proof. by case: c => [//|x s]; have := ltn_ord x; rewrite ltn0. Qed.

(** Dropping [0 < #|D|] refutes the statement: the empty digraph satisfies
    every remaining hypothesis (all of them vacuously) yet has no cycle. *)
Lemma x216_order_guard_has_teeth :
  let D := (TT 0 : diGraphType) in
  let w := (fun _ _ : D => 1 : rat) in
  [/\ (forall v : D, ~~ (v --> v)), strongb D,
      (forall u v : D, u --> v -> 0 < w u v),
      (forall v : D, 1 <= x216_win w v)
    & (forall v : D, 1 <= x216_wout w v)]
  /\ ~ (exists c : seq D, dicycle c /\ 1 <= x216_cycle_weight w c).
Proof.
have e0 : forall v : (TT 0 : diGraphType), False.
  by move=> v; have := ltn_ord v; rewrite ltn0.
split.
  split; try by move=> v; case: (e0 v).
  by apply/strongP => v; case: (e0 v).
by move=> [c [dc _]]; move: (x216_empty_no_dicycle c); rewrite dc.
Qed.

(** ** Guard 2 has teeth: looplessness *)

Local Notation qb := (1%:R / 4%:R : rat).

Lemma x216_qb_gt0 : 0 < qb.
Proof. by apply: divr_gt0; rewrite ltr0n. Qed.

Lemma x216_qb4 : qb + qb + qb + qb = 1.
Proof. by rewrite -!mulrDl -!natrD divff // pnatr_eq0. Qed.

(** Loop weight 3/4 (written [qb + qb + qb]), digon-arc weight 1/4. *)
Definition x216_wl : x216_dgl2 -> x216_dgl2 -> rat :=
  fun u v => if u == v then qb + qb + qb else qb.

Lemma x216_dgl2_wpos (u v : x216_dgl2) : 0 < x216_wl u v.
Proof.
rewrite /x216_wl; case: ifP => _; last exact: x216_qb_gt0.
by rewrite !addr_gt0 //; exact: x216_qb_gt0.
Qed.

Lemma x216_dgl2_strong : strongb x216_dgl2.
Proof.
apply/strongP => x y; have [->|nxy] := eqVneq x y; first exact: connect0.
by apply: connect1; rewrite x216_dgl2_arcE.
Qed.

Lemma x216_dgl2_win (v : x216_dgl2) : x216_win x216_wl v = 1.
Proof.
rewrite /x216_win (bigD1 v) //= (bigD1 (~~ v)) /=; last by case: v.
rewrite big1 ?addr0 => [|u /andP[nuv nun]]; last by case: u nuv nun; case: v.
by rewrite /x216_wl eqxx ifN ?x216_qb4 //; case: v.
Qed.

Lemma x216_dgl2_wout (v : x216_dgl2) : x216_wout x216_wl v = 1.
Proof.
rewrite /x216_wout (bigD1 v) //= (bigD1 (~~ v)) /=; last by case: v.
rewrite big1 ?addr0 => [|u /andP[nuv nun]]; last by case: u nuv nun; case: v.
by rewrite /x216_wl eqxx ifN ?x216_qb4 //; case: v.
Qed.

(** Successor in a one- and a two-element cycle (no rational arithmetic here). *)
Lemma x216_next1 (T : eqType) (x : T) : next [:: x] x = x.
Proof. by rewrite /next /= eqxx. Qed.

Lemma x216_next2l (T : eqType) (x y : T) : next [:: x; y] x = y.
Proof. by rewrite /next /= eqxx. Qed.

Lemma x216_next2r (T : eqType) (x y : T) : x != y -> next [:: x; y] y = x.
Proof.
move=> nxy; have nyx : y != x by rewrite eq_sym.
by rewrite /next /= (negbTE nyx) eqxx.
Qed.

(** Every directed cycle of the loopful digon is a loop [[:: x]] or the digon
    [[:: x; y]] with [x != y]; both have weight below 1. *)
Lemma x216_dgl2_cycles (c : seq x216_dgl2) :
  dicycle c -> x216_cycle_weight x216_wl c < 1.
Proof.
case/and3P => nnil _ uc.
have sz : (size c <= 2)%N by rewrite -card_bool -(card_uniqP uc) max_card.
case: c nnil uc sz => [//|x [|y [|z t]]] // _ uc _.
  rewrite /x216_cycle_weight big_cons big_nil addr0 x216_next1 /x216_wl eqxx.
  by rewrite -x216_qb4 ltrDl x216_qb_gt0.
have nxy : x != y.
  by apply/negP => /eqP e; move: uc; rewrite e /= inE eqxx.
have nyx : y != x by rewrite eq_sym.
rewrite /x216_cycle_weight big_cons big_cons big_nil addr0.
rewrite x216_next2l (x216_next2r nxy) /x216_wl (negbTE nxy) (negbTE nyx).
rewrite -x216_qb4 -[X in _ < X]addrA ltrDl.
by rewrite addr_gt0 // x216_qb_gt0.
Qed.

(** Dropping the looplessness guard refutes the statement. *)
Lemma x216_loopless_guard_has_teeth :
  [/\ (0 < #|{: x216_dgl2}|)%N, strongb x216_dgl2,
      (forall u v : x216_dgl2, u --> v -> 0 < x216_wl u v),
      (forall v : x216_dgl2, 1 <= x216_win x216_wl v)
    & (forall v : x216_dgl2, 1 <= x216_wout x216_wl v)]
  /\ ~ (exists c : seq x216_dgl2, dicycle c /\ 1 <= x216_cycle_weight x216_wl c).
Proof.
split.
  split; rewrite ?card_bool //.
  - exact: x216_dgl2_strong.
  - by move=> u v _; exact: x216_dgl2_wpos.
  - by move=> v; rewrite x216_dgl2_win.
  - by move=> v; rewrite x216_dgl2_wout.
move=> [c [dc ge1]].
by move: ge1; rewrite (lt_geF (x216_dgl2_cycles dc)).
Qed.

(** ** Print Assumptions audit *)

Print Assumptions x216_dg2_witness.
Print Assumptions x216_order_guard_has_teeth.
Print Assumptions x216_loopless_guard_has_teeth.
