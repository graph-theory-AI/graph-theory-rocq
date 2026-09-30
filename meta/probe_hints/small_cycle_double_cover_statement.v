(** Witness hint (faithfulness readback of wave X212, 2026-09-23): an axiom-free
    REFUTATION of [Cycle.conjectures.X212.small_cycle_double_cover_statement]
    (corpus row bm:bm-013, Bondy's small cycle double cover conjecture, status
    `partial`).

    Why the row is refutable as encoded.  The source restricts the conjecture to
    SIMPLE graphs, and the encoding renders "simple" by [U6.simple_mgraph G] =
    [loopless G /\ forall x y, #|edges x y| <= 1].  But coq-graph-theory's
    [edges x y] is DIRECTED ([set e | (source e == x) && (target e == y)]), so
    [simple_mgraph] admits a pair of ANTIPARALLEL edges between two vertices,
    i.e. a doubled edge of the underlying undirected multigraph.  The graph
    below is the complete symmetric digraph on three vertices: three vertices,
    six arcs, one per ordered pair.  It is [simple_mgraph] and [bridgeless]
    (every arc u -> v has the alternative directed route u -> w -> v), it has
    three vertices, so the row demands a cycle double cover with at most two
    members -- while six edges covered twice need twelve circuit slots and no
    circuit of a three-vertex graph has more than three edges.  The proof below
    uses an even cheaper form of that count: with [size L <= 2] the exact-count
    condition forces every edge into EVERY member, so a member equals the whole
    edge set, whose degree at a vertex is 4, not 0 or 2.

    This hint must STOP compiling once the row is repaired (a genuinely simple
    carrier, e.g. an [sgraph], or a [simple_mgraph] that also bounds
    [#|edges x y| + #|edges y x|]).  See
    meta/X211-X229_faithfulness_audit.md.

    STALE BY DESIGN since the foundation repair of 2026-09-23:
    [U6.simple_mgraph] now bounds [#|edges x y| + #|edges y x|], so [cex_simple]
    below no longer holds of [Gcex] (its two antiparallel arcs between each pair
    give the sum 2), and [Cycle.foundations.connectivity.is_bridge] now
    quantifies over the UNDIRECTED [uwalk].  The file is KEPT UNCHANGED, and
    must keep failing to compile: `python3 meta/vacuity_probe.py --names
    small_cycle_double_cover_statement` reports `hint-stale-FIX-OK`, which is
    the fix-verification signal.  See meta/STATEMENT_IMPROVEMENTS.md,
    section "cycle-theory - bridgeless/simple_mgraph repair (2026-09-23)". *)

From GraphTheory Require Import mgraph.
From GTBase Require Import base.
From Cycle.foundations Require Import connectivity.
From Cycle.conjectures Require Import U6 X212.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Three vertices as [option bool]. *)
Definition V3 := option bool.
Definition nx (v : V3) : V3 :=
  match v with None => Some false | Some false => Some true | Some true => None end.

Lemma nx3 (v : V3) : nx (nx (nx v)) = v.
Proof. by case: v => [[]|]. Qed.

Lemma nx_neq (v : V3) : nx v != v.
Proof. by case: v => [[]|]. Qed.

Lemma nx2_neq (v : V3) : nx (nx v) != v.
Proof. by case: v => [[]|]. Qed.

Lemma nx_nx2 (v : V3) : nx v != nx (nx v).
Proof. by case: v => [[]|]. Qed.

Definition Ecex := (V3 * bool)%type.

Definition cex_ep (b : bool) (e : Ecex) : V3 :=
  if b then (if e.2 then nx (nx e.1) else nx e.1) else e.1.

Definition Gcex : mgraph := @Graph unit unit V3 Ecex cex_ep (fun _ => tt) (fun _ => tt).

Lemma cex_src (e : edge Gcex) : source e = e.1. Proof. by []. Qed.
Lemma cex_tgt (e : edge Gcex) : target e = if e.2 then nx (nx e.1) else nx e.1.
Proof. by []. Qed.

Lemma card_Gcex : #|Gcex| = 3.
Proof. by rewrite /= card_option card_bool. Qed.


Lemma cex_loopless : loopless Gcex.
Proof. by case=> v []; rewrite /= eq_sym; [exact: nx2_neq | exact: nx_neq]. Qed.

Lemma cex_simple : simple_mgraph Gcex.
Proof.
split; first exact: cex_loopless.
move=> x y; apply/card_le1_eqP => -[u b] [u' b'].
rewrite !inE /= => /andP[/eqP -> /eqP tb] /andP[/eqP -> /eqP tb'].
suff -> : b = b' by [].
case: b tb => tb; case: b' tb' => tb' //.
- by move: (nx_nx2 x); rewrite tb tb' eqxx.
- by move: (nx_nx2 x); rewrite tb' tb eqxx.
Qed.

Lemma cex_walk_f (u : V3) :
  walk (G := Gcex) u (nx u) [:: ((u, true) : edge Gcex); ((nx (nx u), true) : edge Gcex)].
Proof. by rewrite /= !eqxx /= nx3 eqxx. Qed.

Lemma cex_walk_t (u : V3) :
  walk (G := Gcex) u (nx (nx u)) [:: ((u, false) : edge Gcex); ((nx u, false) : edge Gcex)].
Proof. by rewrite /= !eqxx. Qed.

Lemma cex_bridgeless : bridgeless Gcex.
Proof.
move=> [u b] sep; case: b sep => sep.
- have [f fE fw] := sep _ (cex_walk_t u).
  move: fE fw; rewrite inE => /eqP ->.
  by rewrite !inE /= !xpair_eqE /= !andbF.
- have [f fE fw] := sep _ (cex_walk_f u).
  move: fE fw; rewrite inE => /eqP ->.
  by rewrite !inE /= !xpair_eqE /= !andbF.
Qed.

Definition ea : edge Gcex := (None, false).
Definition eb : edge Gcex := (None, true).
Definition ec : edge Gcex := (Some true, false).

Lemma cex_card3 : #|(ea |: (eb |: [set ec]))| = 3.
Proof. by rewrite !cardsU1 !inE cards1 /ea /eb /ec /eq_op /= /eq_op /=. Qed.

Lemma cex_sub : (ea |: (eb |: [set ec])) \subset edges_at (None : Gcex).
Proof.
apply/subsetP => e; rewrite !in_setU1 in_set1 in_set /incident.
move=> /orP[|/orP[]] /eqP ->; apply/existsP.
- by exists false.
- by exists false.
- by exists true.
Qed.

Lemma cex_deg_gt2 : 2 < #|edges_at (None : Gcex)|.
Proof. by rewrite -cex_card3; apply: subset_leq_card cex_sub. Qed.

Lemma refuted : ~ small_cycle_double_cover_statement.
Proof.
move=> H.
have gt0 : (0 < #|Gcex|)%N by rewrite card_Gcex.
have [L [[circ cnt] sz]] := H Gcex gt0 cex_simple cex_bridgeless.
case: L circ cnt sz => [|C1 [|C2 [|C3 L']]] circ cnt sz; last first.
- by move: sz; rewrite card_Gcex.
- have allC1 : forall e : edge Gcex, e \in C1.
    by move=> e; move: (cnt e) => /=; case: (e \in C1); case: (e \in C2).
  have C1T : C1 = [set: edge Gcex] by apply/setP => e; rewrite !inE allC1.
  have [_ reg _] := circ C1 (mem_head _ _).
  have := reg None; rewrite /subdeg C1T setIT.
  by case=> E; move: cex_deg_gt2; rewrite E.
- by move: (cnt ea) => /=; case: (ea \in C1).
- by move: (cnt ea).
Qed.

Print Assumptions refuted.
