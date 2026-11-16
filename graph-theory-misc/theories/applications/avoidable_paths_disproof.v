(** * GTMisc.applications.avoidable_paths_disproof -- two disjoint avoidable paths: the question's answer is no

    Wave X312, row arxiv:1908.03788#00 (PROGRAMME A6). [two_disjoint_avoidable_paths_disproved] refutes
    [two_disjoint_avoidable_paths_statement] of conjectures/X312.v, Question 1.12 of Bonamy, Defrain, Hatzel and
    Thiebaut, "Avoidable paths in graphs" (arXiv:1908.03788v1 l.115-116), by the record's own counterexample
    (l.118-126): for k >= 3, a cycle on 2k - 1 vertices with an added vertex adjacent to two consecutive cycle
    vertices contains two disjoint P_k but no two disjoint avoidable P_k. One k suffices: k = 3.

    The graph [R5G] on 'I_6: the cycle 0-1-2-3-4-0 and the vertex 5 adjacent to 0 and 1.
    - [two_disjoint_P3]: [1; 2; 3] and [4; 0; 5] are disjoint induced paths on three vertices.
    - [P3_in_L14] / [pairs_bad]: the induced paths on three vertices are the 14 sequences of [L14]; in every
      disjoint pair of them one is [1; 2; 3], [0; 4; 3] or a reverse ([BAD]), the path holding exactly one vertex of
      the triangle {0, 1, 5}.
    - [bad_not_avoidable]: such a path has an induced two-sided extension ([5; 1; 2; 3; 4], resp. [5; 0; 4; 3; 2] or
      the reverses) contained in no chordless cycle ([no_cycle_12345], [no_cycle_02345]): a chordless cycle holding
      five distinct vertices is a hole, the extension's end vertex 4 (resp. 2) has its two cycle neighbours among
      its two graph neighbours, so 0 (resp. 1) lies on the hole with the triangle {0, 1, 5}, which a hole cannot
      hold ([hole_no_triangle] of applications/heavy_path_disproof.v).
    Everything is closed by [Qed]; see the [Print Assumptions] audit at the end. *)

From mathcomp Require Import all_boot zify.
From Stdlib Require Import Lia.
From GraphTheory Require Import preliminaries digraph sgraph.
From GTBase Require Import base walk_usage induced_paths induced_cycles.
From GTMisc.conjectures Require Import X91 X312.
From GTMisc.applications Require Import heavy_path_disproof.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** The record's graph at k = 3: a cycle 0-1-2-3-4-0 and a vertex 5 adjacent to 0 and 1 *)

Definition r5e (a b : nat) : bool :=
  [|| (a == 0) && (b == 1), (a == 1) && (b == 2), (a == 2) && (b == 3),
      (a == 3) && (b == 4), (a == 4) && (b == 0), (a == 5) && (b == 0)
    | (a == 5) && (b == 1)].

Definition r5_rel (i j : 'I_6) : bool := r5e i j || r5e j i.

Lemma r5_sym : symmetric r5_rel.
Proof. by move=> i j; rewrite /r5_rel orbC. Qed.

Lemma r5_irrefl : irreflexive r5_rel.
Proof. by move=> [[|[|[|[|[|[|i]]]]]] Hi]. Qed.

Definition R5G : sgraph := SGraph r5_sym r5_irrefl.

Definition w0 : R5G := @Ordinal 6 0 isT.
Definition w1 : R5G := @Ordinal 6 1 isT.
Definition w2 : R5G := @Ordinal 6 2 isT.
Definition w3 : R5G := @Ordinal 6 3 isT.
Definition w4 : R5G := @Ordinal 6 4 isT.
Definition w5 : R5G := @Ordinal 6 5 isT.

(** ** Deciding induced paths on concrete sequences *)

Definition r5_ipb (p : seq R5G) : bool :=
  [&& p != [::], uniq p, (if p is x :: q then path (--) x q else true)
    & all (fun u => all (fun v => (u -- v) ==> (u != v) ==> seq_consecutiveb p u v) p) p].

Lemma r5_ipbP (p : seq R5G) : nonempty_induced_path p <-> r5_ipb p.
Proof.
case: p => [|x q]; first by split => //; rewrite /r5_ipb eqxx.
rewrite /r5_ipb; split.
- move=> [uq [pq ch]]; apply/and4P; split => //.
  apply/allP => u up; apply/allP => v vp; apply/implyP => uv; apply/implyP => nuv.
  by apply/seq_consecutivebP; exact: ch.
- move=> /and4P [_ uq pq /allP ch]; split => //; split => // u v up vp uv nuv.
  by apply/seq_consecutivebP; have /allP/(_ v vp) := ch u up; rewrite uv nuv.
Qed.

(** ** The witnesses: two disjoint induced paths on three vertices *)

Lemma two_disjoint_P3 :
  exists p q : seq R5G,
    [/\ size p = 3, size q = 3, nonempty_induced_path p, nonempty_induced_path q & [disjoint p & q]].
Proof.
exists [:: w1; w2; w3], [:: w4; w0; w5]; split => //; try exact/r5_ipbP.
by rewrite disjoint_has.
Qed.

(** ** The induced paths on three vertices, and the disjoint pairs *)

Definition L14 : seq (seq nat) :=
  [:: [:: 1; 0; 4]; [:: 4; 0; 1]; [:: 4; 0; 5]; [:: 5; 0; 4]; [:: 0; 1; 2]; [:: 2; 1; 0];
      [:: 2; 1; 5]; [:: 5; 1; 2]; [:: 1; 2; 3]; [:: 3; 2; 1]; [:: 2; 3; 4]; [:: 4; 3; 2];
      [:: 3; 4; 0]; [:: 0; 4; 3]].

Definition BAD : seq (seq nat) := [:: [:: 1; 2; 3]; [:: 3; 2; 1]; [:: 0; 4; 3]; [:: 3; 4; 0]].

Lemma P3_in_L14 (a b c : R5G) : r5_ipb [:: a; b; c] -> [:: val a; val b; val c] \in L14.
Proof.
case: a => [[|[|[|[|[|[|a]]]]]] Ha] //;
case: b => [[|[|[|[|[|[|b]]]]]] Hb] //;
case: c => [[|[|[|[|[|[|c]]]]]] Hc] //.
Qed.

Lemma pairs_bad :
  all (fun s => all (fun t => has (mem t) s || (s \in BAD) || (t \in BAD)) L14) L14.
Proof. by []. Qed.

(** ** No chordless cycle through the vertices of a failing extension *)

Lemma r5_hole (c : seq R5G) (s : seq R5G) :
  chordless_cycle c -> uniq s -> 3 < size s -> {subset s <= c} -> hole c.
Proof.
move=> [uc [_ ch]] us ss sub; split => //; split => //.
by apply: (leq_trans ss); exact: uniq_leq_size.
Qed.

Lemma next_prev_neq (c : seq R5G) (x : R5G) :
  uniq c -> x \in c -> 2 < size c -> next c x != path.prev c x.
Proof.
move=> uc xc sz.
have pc : path.prev c x \in c by rewrite path.mem_prev.
have := iter_next_neq uc pc (_ : 0 < 2 < size c); rewrite /= (next_prev uc).
by apply; rewrite sz.
Qed.

Lemma two_cycle_neighbours (c : seq R5G) (x a b : R5G) :
  hole c -> x \in c -> (forall y, x -- y -> (y == a) || (y == b)) -> (a \in c) && (b \in c).
Proof.
move=> hc xc nb.
have uc := hole_uniq hc; have cy := hole_cycle hc; have sz := hole_size hc.
have xn : x -- next c x by exact: (next_cycle cy xc).
have xp : x -- path.prev c x by rewrite sg_sym; exact: (prev_cycle cy xc).
have ne := next_prev_neq uc xc (ltnW sz).
have nc : next c x \in c by rewrite mem_next.
have pc : path.prev c x \in c by rewrite path.mem_prev.
case/orP: (nb _ xn) => /eqP en; case/orP: (nb _ xp) => /eqP ep.
- by move: ne; rewrite en ep eqxx.
- by rewrite -en -ep nc pc.
- by rewrite -en -ep nc pc.
- by move: ne; rewrite en ep eqxx.
Qed.

Lemma nbr4 (y : R5G) : w4 -- y -> (y == w3) || (y == w0).
Proof. by case: y => [[|[|[|[|[|[|y]]]]]] Hy]. Qed.

Lemma nbr2 (y : R5G) : w2 -- y -> (y == w1) || (y == w3).
Proof. by case: y => [[|[|[|[|[|[|y]]]]]] Hy]. Qed.

Lemma no_cycle_12345 (c : seq R5G) :
  chordless_cycle c -> w1 \in c -> w2 \in c -> w3 \in c -> w4 \in c -> w5 \in c -> False.
Proof.
move=> cc c1 c2 c3 c4 c5.
have hc : hole c.
  by apply: (@r5_hole c [:: w1; w2; w3; w4; w5]) => //; apply/allP; rewrite /= c1 c2 c3 c4 c5.
have /andP [c3' c0] := two_cycle_neighbours hc c4 nbr4.
exact: (hole_no_triangle hc c0 c1 c5).
Qed.

Lemma no_cycle_02345 (c : seq R5G) :
  chordless_cycle c -> w0 \in c -> w2 \in c -> w3 \in c -> w4 \in c -> w5 \in c -> False.
Proof.
move=> cc c0 c2 c3 c4 c5.
have hc : hole c.
  by apply: (@r5_hole c [:: w0; w2; w3; w4; w5]) => //; apply/allP; rewrite /= c0 c2 c3 c4 c5.
have /andP [c1 c3'] := two_cycle_neighbours hc c2 nbr2.
exact: (hole_no_triangle hc c0 c1 c5).
Qed.

(** ** The four paths with one triangle vertex are not avoidable *)

Lemma bad_not_avoidable (p : seq R5G) : map val p \in BAD -> ~ x91_avoidable_path p.
Proof.
have mv (s : seq R5G) : map val p = map val s -> p = s by apply: inj_map; exact: val_inj.
rewrite !inE => /or4P [] /eqP.
- move=> /(mv [:: w1; w2; w3]) -> [_ av].
  have ip : nonempty_induced_path [:: w5; w1; w2; w3; w4] by apply/r5_ipbP.
  have [c [cc sub]] := av w5 w4 ip.
  by apply: (no_cycle_12345 cc); apply: sub.
- move=> /(mv [:: w3; w2; w1]) -> [_ av].
  have ip : nonempty_induced_path [:: w4; w3; w2; w1; w5] by apply/r5_ipbP.
  have [c [cc sub]] := av w4 w5 ip.
  by apply: (no_cycle_12345 cc); apply: sub.
- move=> /(mv [:: w0; w4; w3]) -> [_ av].
  have ip : nonempty_induced_path [:: w5; w0; w4; w3; w2] by apply/r5_ipbP.
  have [c [cc sub]] := av w5 w2 ip.
  by apply: (no_cycle_02345 cc); apply: sub.
- move=> /(mv [:: w3; w4; w0]) -> [_ av].
  have ip : nonempty_induced_path [:: w2; w3; w4; w0; w5] by apply/r5_ipbP.
  have [c [cc sub]] := av w2 w5 ip.
  by apply: (no_cycle_02345 cc); apply: sub.
Qed.

(** ** No two disjoint avoidable paths on three vertices *)

Lemma P3_shape (p : seq R5G) : size p = 3 -> nonempty_induced_path p -> map val p \in L14.
Proof.
case: p => [|a [|b [|c [|d p]]]] // _ /r5_ipbP.
exact: P3_in_L14.
Qed.

Lemma no_two_disjoint_avoidable :
  ~ exists p q : seq R5G,
      [/\ size p = 3, size q = 3, x91_avoidable_path p, x91_avoidable_path q & [disjoint p & q]].
Proof.
move=> [p [q [sp sq ap aq dpq]]].
have pL := P3_shape sp (proj1 ap); have qL := P3_shape sq (proj1 aq).
have := allP pairs_bad _ pL => /allP /(_ _ qL).
have dval : ~~ has (mem (map val q)) (map val p).
  rewrite has_map; apply: contraL dpq => /hasP [x xp /=]; rewrite (mem_map val_inj) => xq.
  by rewrite disjoint_has negbK; apply/hasP; exists x.
rewrite (negbTE dval) /=.
by case/orP => [pB | qB]; [exact: bad_not_avoidable pB ap | exact: bad_not_avoidable qB aq].
Qed.

(** ** The disproof *)

Theorem two_disjoint_avoidable_paths_disproved : ~ two_disjoint_avoidable_paths_statement.
Proof.
move=> H; case: (H 3 isT R5G) => [HA | HB].
- by apply: HA; have [p [q [sp sq ip iq d]]] := two_disjoint_P3; exists p, q.
- exact: no_two_disjoint_avoidable HB.
Qed.

Print Assumptions two_disjoint_avoidable_paths_disproved.
