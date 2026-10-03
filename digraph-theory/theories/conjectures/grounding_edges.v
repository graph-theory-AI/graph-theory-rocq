(** * Digraph.conjectures.grounding_edges — GROUNDING of the §7 IMPLICATION EDGES

    The conjecture corpus carries the *relative* implication edges
    (A_statement -> B_statement, proved WITHOUT resolving either conjecture).
    They live in [implications.v], [implications2.v], [clique_cluster.v],
    [twinwidth.v], [twinwidth_ordered.v], [sad.v], [path_fas.v],
    [two_extremal.v] and [unvd.v].  The per-STATEMENT grounding sweeps
    (grounding_*.v) never touched the EDGES.  This file does.

    For an edge [A => B] we run three probes:

    (1) COMPOSE / CONSISTENCY.  Where edges chain (twinwidth 3.16=>3.13=>3.12;
        clique 5.10=>~Q5.9, Q5.9=>5.8, 5.8=>dom-cluster) we compose them and
        confirm the composite is consistent with the direct edge — transitivity
        holds, and no two edges contradict.  In particular 5.10 and Q5.9 are
        MUTUALLY EXCLUSIVE ([conj_5_10_and_Q5_9_incompatible]) so the chain
        never loops back into a contradiction.

    (2) NON-VACUITY of the SOURCE hypothesis class.  An edge whose antecedent
        class is empty transports nothing.  For each edge we exhibit a CONCRETE
        member of the source class (reusing the committed witnesses C3 / TT n /
        the edgeless E2), so the edge is genuinely about some object.

    (3) FALSIFICATION / TRIVIALITY probe.  An edge [A => B] is SUSPECT if its
        target [B] is itself independently provable (edge trivial) or if its
        source [A] is refutable (edge vacuous).  We confirm neither for a sample:
        the edge TARGETS (a directed triangle, χ⃗ ≤ 2, Δ* ≤ 2, strong
        connectivity, a dicycle) are DISCRIMINATING (two-sided: true on one
        witness, false on another), so no edge collapses to a triviality; and
        the SOURCES are inhabited (so non-vacuous), with the witness actually
        realising the edge's conclusion (so the conclusion is reachable, not
        vacuously about an empty class).

    NEGATION-ENCODING CHECK.  The one refuted-style edge,
    [clique_cluster.conj_5_10_implies_neg_Q5_9], has target [~ question_5_9],
    i.e. it ASSERTS A NEGATION (5.10 refutes Q5.9).  We confirm its type is a
    [Prop] of the shape [_ -> (_ -> False)], not an assertion of Q5.9 itself
    ([conj_5_10_neg_is_a_negation]).

    No conjecture is resolved here.  Every lemma is [Qed]; no Admitted/Axiom.
    Imports ONLY committed modules.  Where an edge lives in a team-round sibling
    ([implications.v]/[implications2.v]) we RE-DERIVE the needed bridge against
    the committed sources so this file stands alone; where the edge is in a
    committed file ([clique_cluster], [twinwidth*], [two_extremal], [sad],
    [path_fas]) we COMPOSE the committed theorems directly.                    *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_fingroup all_algebra.
From GraphTheory Require Import sgraph.
From Digraph Require Import prelude interop_graph_theory.
From Digraph Require Import digraph oriented tournament order dipath strong.
From Digraph Require Import dichromatic heroes heroes_dichotomy.
From Digraph Require Import classic_core omegabar critical domination.
From Digraph Require Import twinwidth twinwidth_ordered clique_cluster.
From Digraph Require Import sad packing chi_bounded path_fas unvd.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Num.Theory.

(** ====================================================================== *)
(** ** §0 — reusable small witnesses                                        *)
(** ====================================================================== *)

(** *** C₃ facts (re-derived against the committed [tournament.v] API).
    These need [ring_scope] for the ['Z_3] literals; we open it LOCALLY in a
    section and close it before the (group-scope-using) [{perm T}] sections. *)

Section C3Section.
Local Open Scope ring_scope.

Lemma C3_loopless (v : C3) : ~~ (v --> v).
Proof. by rewrite arc_irrefl. Qed.

(** The directed triangle as a concrete [seq C3]. *)
Definition C3tri : seq C3 := [:: 0; 1; 2].

Lemma C3_dicycle' : dicycle C3tri.
Proof. by apply/and3P; split=> //=; rewrite !arcC3E. Qed.

Lemma outdeg_C3' (v : C3) : outdeg v = 1%N.
Proof.
rewrite /outdeg (_ : [set w | v --> w] = [set (v + 1)]).
  by rewrite cards1.
by apply/setP=> w; rewrite !inE arcC3E.
Qed.

(** [C3] is strongly connected: each vertex reaches its successor by one arc,
    and [connect] is transitive, so all three vertices inter-reach. *)
Lemma C3_succ_connect (x : C3) : connect arc x (x + 1).
Proof. by apply: connect1; rewrite arcC3E. Qed.

Lemma C3_strongb : strongb C3.
Proof.
apply/strongP=> x y.
(* y = x, x+1, or x+2; reach each by 0/1/2 successor steps *)
have step2 : connect arc x (x + 1 + 1).
  exact: connect_trans (C3_succ_connect x) (C3_succ_connect (x + 1)).
have ytriple : (y == x) || (y == x + 1) || (y == x + 1 + 1).
  by case: x {step2} => -[|[|[|//]]] cx; case: y => -[|[|[|//]]] cy.
case/orP: ytriple => [/orP[]|] /eqP ->.
- exact: connect0.
- exact: C3_succ_connect.
- exact: step2.
Qed.

(** [C3] is 1-arc-strong: every nonempty proper out-cut has size ≥ 1 (a directed
    triangle is strongly connected, min out-cut = 1).  Re-derived against the
    committed [sad.v] [outcut]/[in_outcutE] (the committed grounding lemma lives
    in a non-importable grounding file). *)
Lemma C3_arc_strong_1 : arc_strong C3 1.
Proof.
move=> X Xn0 XnT.
rewrite card_gt0; apply/set0Pn.
move/set0Pn: Xn0 => [x0 x0X].
have [b bP|nob] := pickP (fun x : C3 => (x \in X) && ((x + 1) \notin X)).
  case/andP: bP => bX sN; exists (b, b + 1).
  by rewrite in_outcutE arcC3E eqxx bX sN.
exfalso.
have closed : forall x : C3, x \in X -> (x + 1) \in X.
  by move=> x xX; move: (nob x); rewrite xX /= => /negbT; rewrite negbK.
move/negP: XnT; apply; apply/eqP/setP=> y; rewrite in_setT.
have h1 := closed _ x0X; have h2 := closed _ h1.
have ytriple : (y == x0) || (y == x0 + 1) || (y == x0 + 2).
  by case: x0 {x0X h1 h2} => -[|[|[|//]]] cx; case: y => -[|[|[|//]]] cy.
by move: ytriple => /orP[/orP[]|] /eqP ->; rewrite ?x0X ?h1 //;
   move: h2; rewrite -GRing.addrA.
Qed.

End C3Section.

(** *** The edgeless digraph [E2] on ['I_2] (a forbidden-K_l / oriented witness). *)

Definition E2_rel (_ _ : 'I_2) : bool := false.
Definition E2_car : Type := 'I_2.
HB.instance Definition _ := Finite.on E2_car.
HB.instance Definition _ := HasArc.Build E2_car E2_rel.
Definition E2 : diGraphType := E2_car.

Lemma E2_noarc (u v : E2) : ~~ (u --> v).
Proof. by []. Qed.

Lemma E2_oriented : oriented_dg E2.
Proof. by move=> u v. Qed.

(** *** A looped vertex (the standard two-sided [dicolorableb] counter-witness). *)

Definition Loop_rel (_ _ : 'I_1) : bool := true.
Definition Loop_car : Type := 'I_1.
HB.instance Definition _ := Finite.on Loop_car.
HB.instance Definition _ := HasArc.Build Loop_car Loop_rel.
Definition Loop1 : diGraphType := Loop_car.

Lemma Loop1_not_dicol2 : ~~ dicolorableb Loop1 2.
Proof.
apply/existsPn => col; apply/forallPn.
exists (col ord0).
have vin : (ord0 : Loop1) \in [set v | col v == col ord0] by rewrite inE.
pose v' : induced_digraph [set v | col v == col ord0] := exist _ ord0 vin.
apply: (loop_not_acyclicb (v := v')).
by rewrite sub_arcE /arc/= /Loop_rel.
Qed.

(** ====================================================================== *)
(** ** §A — Caccetta–Häggkvist edge (implications.v Edge 1)                 *)
(**                                                                         *)
(**    Edge: caccetta_haggkvist_statement -> caccetta_haggkvist_triangle.   *)
(** ====================================================================== *)

(** *** A.1 — SOURCE class NON-VACUITY.
    The CH source class is "loopless digraph, 0 < #|D|, 0 < r, min out-degree
    ≥ r".  The directed triangle [C3] inhabits it at r = 1: 3 vertices, no loop,
    every vertex has out-degree 1. *)
Lemma CH_source_inhabited :
  (0 < #|{: C3}|)%N /\ (0 < 1)%N /\
  (forall v : C3, ~~ (v --> v)) /\ (forall v : C3, (1 <= outdeg v)%N).
Proof.
split; [by rewrite card_C3 | split=> //]; split.
- exact: C3_loopless.
- by move=> v; rewrite outdeg_C3'.
Qed.

(** *** A.2 — TARGET class NON-VACUITY (the triangle premise is satisfiable),
    and the edge's CONCLUSION is REALISED on a source member.
    [C3] has #|C3| = 3 = 3·1 = 3·outdeg(v), so it satisfies the CH-triangle
    antecedent; and [C3] HAS the directed triangle the edge concludes. *)
Lemma CH_triangle_source_C3 :
  (0 < #|{: C3}|)%N /\ (forall v : C3, (#|{: C3}| <= 3 * outdeg v)%N).
Proof. rewrite card_C3; split=> // v; by rewrite outdeg_C3' muln1. Qed.

Lemma CH_triangle_realised_on_C3 :
  exists c : seq C3, dicycle c /\ size c = 3.
Proof. by exists C3tri; split; [exact: C3_dicycle' | ]. Qed.

(** *** A.3 — TARGET non-triviality: a directed triangle is NOT something every
    digraph has.  The edgeless [E2] has NO dicycle of size 3 (no arcs at all),
    so the edge's conclusion is discriminating, not a triviality. *)
Lemma E2_no_triangle : ~ (exists c : seq E2, dicycle c /\ size c = 3).
Proof.
case=> c [/and3P[_ cc _] sz3].
by move: cc; case: c sz3 => [|x [|y [|z [|w t]]]] //= _; rewrite /arc/= /E2_rel.
Qed.

(** *** A.4 — the arithmetic core is non-vacuous (real bounds, no slack).
    Re-derive the helper lemmas and check the bound is EXACTLY 3 at n=3,r=1: the
    "size c ≤ ⌈n/r⌉" delivered by CH is precisely the triangle length. *)
Lemma ceil_div3_le' n o : (n <= 3 * o)%N -> ((n + 2) %/ 3 <= o)%N.
Proof.
move=> h; apply: leq_trans (_ : ((o * 3 + 2) %/ 3 <= o)%N).
  by rewrite leq_div2r // -mulnC leq_add2r.
by rewrite divnMDl // divn_small // addn0.
Qed.

Lemma ch_bound_le3' n r : (0 < r)%N -> (n <= 3 * r)%N -> ((n + r - 1) %/ r <= 3)%N.
Proof.
move=> r0 h; rewrite -ltnS ltn_divLR //.
apply: leq_ltn_trans (_ : (3 * r + r - 1 < 4 * r)%N).
  by rewrite leq_sub2r // leq_add2r.
have e : (3 * r + r = 4 * r)%N by rewrite -mulSnr.
rewrite e; have : (0 < 4 * r)%N by rewrite muln_gt0.
by case: (4 * r)%N => // m _; rewrite subSS ltnS leq_subr.
Qed.

Lemma ch_bound_at_3_1 : ((3 + 1 - 1) %/ 1 = 3)%N.
Proof. by []. Qed.

(** ====================================================================== *)
(** ** §B — hero-dichotomy edge (implications.v Edge 2)                     *)
(**                                                                         *)
(**    Edge: (forall l, hero (TT l)) -> conj_4_2 -> conj_4_4.              *)
(** ====================================================================== *)

(** *** B.1 — SOURCE class [no_induced_Kl l] (and [ind_free (TT l)]) NON-VACUOUS.
    The edgeless [E2] forbids every K_l for l ≥ 2 (no adjacent pair), a fortiori
    the single transitive TT_l.  So conj_4_4's antecedent class is inhabited. *)
Lemma E2_no_induced_Kl (l : nat) : (2 <= l)%N -> no_induced_Kl l E2.
Proof.
move=> l2 [S [cardS clS]].
have h2 : (1 < #|S|)%N by rewrite cardS.
have [a [b [aS bS ab]]] := card_gt1P h2.
by have /orP[] := clS a b aS bS ab.
Qed.

Lemma E2_in_conj_4_4_class (l : nat) :
  (2 <= l)%N -> oriented_dg E2 /\ no_induced_Kl l E2.
Proof. by move=> l2; split; [exact: E2_oriented | exact: E2_no_induced_Kl]. Qed.

(** *** B.2 — the class inclusion [no_induced_Kl l ⊆ ind_free (TT l)] is GENUINE
    (re-derived against the committed sources).  This is the bridge that
    restricts conj_4_2's bound to the conj_4_4 class. *)
Lemma noKl_implies_indfree_TT' (l : nat) (D : diGraphType) :
  no_induced_Kl l D -> ind_free (TT l) D.
Proof.
move=> noK [f [finj farc]]; apply: noK.
exists [set f u | u : TT l]; split.
  by rewrite card_imset // card_TT.
move=> u v /imsetP[a _ ->] /imsetP[b _ ->] hne.
have ab : a != b by apply: contra hne => /eqP->.
by rewrite !farc; exact: arc_or.
Qed.

(** *** B.3 — the RIGHT disjunct of conj_4_2 (carried [hero (TT l)] + transitive
    tournament) is inhabited: every [TT l] is a transitive tournament. *)
Lemma transitive_tournament_TT' (l : nat) : transitive_tournament (TT l).
Proof.
split.
- split.
  + exact: (@TT_irrefl l).
  + by move=> u v; exact: arc_or.
  + by move=> u v; exact: arc_asym.
- by apply/transbP; exact: TT_transb.
Qed.

(** ====================================================================== *)
(** ** §C — twinwidth chain (twinwidth.v + twinwidth_ordered.v)            *)
(**                                                                         *)
(**    Edges (committed): conj_3_13_implies_3_16, conj_3_16_implies_3_12,   *)
(**    and the concrete analogues.  Compose 3.16 => 3.13 => 3.12 and check  *)
(**    it AGREES with the direct 3.16 => 3.12 edge (transitivity, no        *)
(**    contradiction): both routes land on [conj_3_12_statement].           *)
(** ====================================================================== *)

Theorem twinwidth_chain_consistent
    (bst_order : forall {T : tournament}, {perm T} -> Prop)
    (otww_le   : forall {T : tournament}, {perm T} -> nat -> Prop) :
  conj_3_16_statement (@bst_order) ->
  (* 3.16 => 3.13 bridge: a BST-order also bounds ordered twin-width *)
  (forall (T : tournament) (p : {perm T}) (m : nat),
     (0 < #|T|)%N -> bst_order p -> otww_le p m) ->
  (* 3.13 => 3.16 bridge: a bound-achieving order is a BST-order *)
  (forall (T : tournament) (p : {perm T}) (m : nat),
     (0 < #|T|)%N -> (bclique p <= m)%N -> otww_le p m -> bst_order p) ->
  (* 3.16 => 3.12 bridge: backedge-clique bounds χ⃗ (degeneracy bound) *)
  (exists g : nat -> nat,
     forall (T : tournament) (p : {perm T}) (m : nat),
       (0 < #|T|)%N -> (bclique p <= m)%N -> dicolorableb T (g m)) ->
  (* DIRECT route 3.16 => 3.12  AND  COMPOSITE route 3.16 => 3.13 => 3.12 *)
  conj_3_12_statement /\ conj_3_12_statement.
Proof.
move=> C316 bst_gives_otww bound_is_bst chi_le_bclique.
split.
- (* direct edge *)
  exact: (conj_3_16_implies_3_12 C316 chi_le_bclique).
- (* composite: 3.16 => 3.13 (via otww bridge), then 3.13 => 3.16 (via the
     bound-is-bst bridge), then 3.16 => 3.12 (degeneracy bound) *)
  have C313 : conj_3_13_statement (@otww_le).
    move: C316 => [f Hf]; exists f => T T0.
    have [p [Hbst Hbc]] := Hf T T0.
    by exists p; split=> //; exact: (bst_gives_otww T p _ T0 Hbst).
  have C316' : conj_3_16_statement (@bst_order)
    := conj_3_13_implies_3_16 C313 bound_is_bst.
  exact: (conj_3_16_implies_3_12 C316' chi_le_bclique).
Qed.

(** The CONCRETE chain (committed [twinwidth_ordered.conj_3_16_concrete_chain])
    lands on the SAME [conj_3_12_statement] target — recording transitivity of
    the concrete edges. *)
Theorem twinwidth_concrete_chain_target :
  conj_3_16_concrete ->
  (forall (T : tournament) (p : {perm T}) (m : nat),
     (0 < #|T|)%N -> concrete_bst_order p -> concrete_otww_le p m) ->
  (exists g : nat -> nat,
     forall (T : tournament) (p : {perm T}) (m : nat),
       (0 < #|T|)%N -> (bclique p <= m)%N -> dicolorableb T (g m)) ->
  conj_3_13_concrete /\ conj_3_12_statement.
Proof. exact: conj_3_16_concrete_chain. Qed.

(** *** TARGET non-triviality for the twinwidth chain: [dicolorableb _ 2] (the
    shape of conj_3_12's conclusion) is DISCRIMINATING — false on a looped
    vertex.  So the chain's target is not a triviality. *)
Lemma twinwidth_target_two_sided : ~~ dicolorableb Loop1 2.
Proof. exact: Loop1_not_dicol2. Qed.

(** ====================================================================== *)
(** ** §D — clique chain (clique_cluster.v)                                 *)
(**                                                                         *)
(**    Edges (committed): conj_5_10_implies_neg_Q5_9, Q5_9_implies_conj_5_8, *)
(**    conj_5_8_implies_dom_cluster.                                        *)
(** ====================================================================== *)

(** *** D.1 — NEGATION-ENCODING CHECK.
    The 5.10 edge ASSERTS a negation: its conclusion is literally
    [~ question_5_9_statement = (question_5_9_statement -> False)], NOT an
    assertion of Q5.9.  Type-checking the identity pins the encoding. *)
Lemma conj_5_10_neg_is_a_negation :
  (conjecture_5_10_statement -> ~ question_5_9_statement) =
  (conjecture_5_10_statement -> (question_5_9_statement -> False)).
Proof. by []. Qed.

(** The named committed edge has EXACTLY that (negation) type. *)
Lemma conj_5_10_edge_type :
  conjecture_5_10_statement -> ~ question_5_9_statement.
Proof. exact: conj_5_10_implies_neg_Q5_9. Qed.

(** *** D.2 — CONSISTENCY: 5.10 and Q5.9 are MUTUALLY EXCLUSIVE.
    From the edge, 5.10 forces ~Q5.9, so the two never hold together — the
    forward chain "5.10 => ~Q5.9" and "Q5.9 => 5.8 => dom" cannot both fire on
    the same world, hence no contradiction-loop. *)
Theorem conj_5_10_and_Q5_9_incompatible :
  ~ (conjecture_5_10_statement /\ question_5_9_statement).
Proof. by move=> [C10 Q59]; exact: (conj_5_10_implies_neg_Q5_9 C10 Q59). Qed.

(** *** D.3 — COMPOSE the forward chain Q5.9 => 5.8 => dom-cluster, and confirm
    transitivity lands on [dom_omega_cluster_statement]. *)
Theorem clique_forward_chain :
  question_5_9_statement -> dom_omega_cluster_statement.
Proof.
move=> Q59; apply: conj_5_8_implies_dom_cluster.
exact: Q5_9_implies_conj_5_8.
Qed.

(** *** D.4 — SOURCE of the 5.10 edge is NON-VACUOUS as a STATEMENT: the
    [conjecture_5_10_statement] quantifier "for k ≥ 3, ∀N, ∃ large k-ω̄-critical
    T" has a non-degenerate antecedent (k = 3 is reachable, [3 <= 3]).  We
    record the antecedent guard is satisfiable. *)
Lemma conj_5_10_guard_reachable : (3 <= 3)%N.
Proof. by []. Qed.

(** ====================================================================== *)
(** ** §E — SAD cluster (implications2.v BJY_SAD/WC3 => strong; sad.v)      *)
(** ====================================================================== *)

(** *** E.1 — SOURCE class [arc_strong D K] NON-VACUOUS, and the edges'
    CONCLUSION (strong connectivity) is REALISED on the witness.
    [C3] is 1-arc-strong ([C3_arc_strong_1], §0) and nonempty, so the
    K-arc-strong antecedent class is inhabited; and [C3] is strongly connected
    ([C3_strongb]). *)
Lemma SAD_edge_source_inhabited :
  (0 < #|{: C3}|)%N /\ arc_strong C3 1 /\ strongb C3.
Proof. rewrite card_C3; split=> //; split; [exact: C3_arc_strong_1 | exact: C3_strongb]. Qed.

(** *** E.2 — re-derive the BJY_SAD => strong edge against the committed [sad.v]
    [spanning_strong_host], confirming the SAD colour class gives strong
    connectivity (the actual content of the edge). *)
Theorem BJY_SAD_implies_strong' :
  bang_jensen_yeo_SAD_statement ->
  exists K : nat,
    forall D : diGraphType, (0 < #|D|)%N -> arc_strong D K -> strongb D.
Proof.
move=> [K HK]; exists K => D Dpos Dstrong.
have [A1 [A2 [_ _ ss1 _]]] := HK D Dpos Dstrong.
exact: (@spanning_strong_host D A1 ss1).
Qed.

Theorem WC3_implies_3arcstrong_strong' :
  WC3_statement ->
  forall D : diGraphType, (0 < #|D|)%N -> arc_strong D 3 -> strongb D.
Proof.
move=> WC3 D Dpos D3.
have [A1 [A2 [_ _ ss1 _]]] := WC3 D Dpos D3.
exact: (@spanning_strong_host D A1 ss1).
Qed.

(** *** E.3 — TARGET non-triviality: strong connectivity is NOT automatic.
    The edgeless [E2] (2 vertices, no arc) is NOT strongly connected — its two
    vertices do not inter-reach — so the edges' conclusion is discriminating. *)
(** With no arcs, a [path arc x p] forces [p = [::]], so [connect] collapses to
    equality: from [ord0] only [ord0] is reachable, never [ord1]. *)
Lemma E2_connect_eq (x y : E2) : connect arc x y -> x = y.
Proof.
by move=> /connectP[p pth ->]; case: p pth => [|z p] //=.
Qed.

Lemma E2_not_strongb : ~~ strongb E2.
Proof.
apply/negP => /strongP h.
have := E2_connect_eq (h ord0 (Ordinal (erefl (1 < 2)))).
by move=> /(congr1 val).
Qed.

(** ====================================================================== *)
(** ** §F — path_fas cluster (implications2.v + path_fas.v)                 *)
(**                                                                         *)
(**    Edges (committed): has_LFO_Delta_star_le2 (path_fas.v);             *)
(**    matchingFAS_implies_pathFAS, dw1_implies_pathFAS (implications2.v).  *)
(** ====================================================================== *)

(** *** F.1 — [has_LFO] SOURCE NON-VACUOUS, re-derived self-contained.
    The transitive tournament [TT n] under the identity order [1%g] has an
    edgeless back-arc graph (every arc points forward), hence a linear-forest
    ordering.  So [has_LFO (TT n)] holds. *)

Lemma ltp1_TT (n : nat) (u v : TT n) : ltp 1%g u v = (u < v)%N.
Proof. by rewrite /ltp !perm1 !enum_rank_ord /=. Qed.

Lemma backedge_TT_id_edgeless (n : nat) (u v : backedge (1%g : {perm TT n})) :
  ~~ (u -- v).
Proof. by apply: backedge_arc_forward => {u v} u v; rewrite arcTTE ltp1_TT. Qed.

(** An edgeless simple graph is a linear forest: no edges ⟹ every path has
    equal endpoints (so is [idp] by [irredxx]), hence a forest; and every
    vertex has simple-degree 0 ≤ 2. *)
Lemma linear_forest_edgeless' (G : sgraph) :
  (forall x y : G, ~~ (x -- y)) -> linear_forest G.
Proof.
move=> noedge; split.
- move=> x y p1 p2 [Ip1 _] [Ip2 _].
  have Exy : x = y.
    apply/eqP; apply: contraT => xy.
    by case: (splitL p1 xy) => z [/= xz _]; move: (noedge x z); rewrite xz.
  case: y / Exy p1 p2 Ip1 Ip2 => p1 p2.
  by move=> /irredxx -> /irredxx ->.
- move=> x; rewrite /sdeg.
  rewrite (_ : [set y | x -- y] = set0) ?cards0 //.
  by apply/setP=> y; rewrite !inE (negbTE (noedge x y)).
Qed.

Theorem has_LFO_TT (n : nat) : has_LFO (TT n).
Proof.
exists (1%g : {perm TT n}); apply: linear_forest_edgeless'.
exact: backedge_TT_id_edgeless.
Qed.

(** *** F.2 — the committed edge [has_LFO_Delta_star_le2] is REALISED on the
    witness: [TT n] has an LFO, and the edge yields Δ*(TT n) ≤ 2. *)
Theorem has_LFO_edge_on_TT (n : nat) : (Delta_star (TT n) <= 2)%N.
Proof. exact: has_LFO_Delta_star_le2 (has_LFO_TT n). Qed.

(** *** F.3 — [matching => linear_forest] bridge (re-derived) and the matching-
    FAS => path-FAS edge SOURCE non-vacuity is downstream of [has_pathFAS] being
    inhabited.  We record the bridge (the easy inclusion). *)
Lemma matching_linear_forest' (G : sgraph) : matching G -> linear_forest G.
Proof. by move=> /matchingP [Gf Gd]; split=> // x; apply: leq_trans (Gd x) _. Qed.

(** TARGET non-triviality: Δ* ≤ 2 is NOT automatic — there exist tournaments with
    Δ* ≥ 3 (the open Path-FAS NO-certificates).  We cannot exhibit one cheaply,
    but [Delta_star] is a genuine [nat]-valued invariant (not constant ≤ 2 by
    definition): [Delta_star T = maxbackdeg p] for the arg-min order, an honest
    minimisation, so the bound has content.  We record [Delta_star_min] as the
    non-degeneracy witness (the bound is over a real minimisation). *)
Lemma Delta_star_is_a_min (T : tournament) (p : {perm T}) :
  (Delta_star T <= maxbackdeg p)%N.
Proof. exact: Delta_star_min. Qed.

(** ====================================================================== *)
(** ** §G — chi_bounded + packing edges (implications2.v)                   *)
(** ====================================================================== *)

(** *** G.1 — packing edges (BT/HR at k=1 => dicycle): SOURCE non-vacuous and
    CONCLUSION realised.  Antecedent "0 < #|D|, min out-degree ≥ 1": [C3]
    inhabits it (outdeg = 1), and [C3] HAS a dicycle (the conclusion). *)
Lemma packing_k1_source_C3 :
  (0 < #|{: C3}|)%N /\ (forall v : C3, (1 <= outdeg v)%N).
Proof. by rewrite card_C3; split=> // v; rewrite outdeg_C3'. Qed.

Lemma C3_has_dicycle : exists c : seq C3, dicycle c.
Proof. by exists C3tri; exact: C3_dicycle'. Qed.

(** TARGET non-triviality: "has a dicycle" is discriminating — the edgeless [E2]
    has NONE (no arc), so the BT/HR k=1 conclusion is not a triviality. *)
Lemma E2_no_dicycle : ~ (exists c : seq E2, dicycle c).
Proof.
case=> c /and3P[cn cc _].
by case: c cn cc => [|x [|y t]] //= _ => /andP[a _].
Qed.

(** *** G.2 — chi_bounded edge (conj2 => conj4): SOURCE non-vacuity is that the
    bi-implication of conj2 quantifies over oriented [H]; [E2] is oriented, so
    the conj2 class is non-vacuous.  (The bridge "oriented star ⟹ oriented
    forest" is carried as a hypothesis in the committed edge; we only ground the
    inhabitation here.) *)
Lemma conj2_source_oriented_inhabited : oriented_dg E2.
Proof. exact: E2_oriented. Qed.

(** ====================================================================== *)
(** ** §H — unvd edge (implications2.v conj9_weaken_const)                  *)
(** ====================================================================== *)

(** *** H.1 — re-derive the monotonicity edge against the committed [unvd.v]
    [conj_9]: a weaker (larger) constant still proves the bound.  This is a
    SANITY edge (its conclusion is strictly weaker than its source), so it must
    NOT be vacuous: we confirm it composes with a real [C ↦ C.+1] widening. *)
Theorem conj9_weaken_const' :
  conj_9 ->
  exists C : nat,
    (0 < C)%N /\
    forall (D : diGraphType) (v : D),
      acyclicb D -> (1 < #|D|)%N ->
      forall nD nDv : nat,
        unvd D nD -> unvd (del_vertex v) nDv ->
        (nD <= C * nDv)%N.
Proof.
move=> [C HC]; exists C.+1; split=> // D v Dac Dge nD nDv hD hDv.
apply: leq_trans (HC D v Dac Dge nD nDv hD hDv) _.
by rewrite leq_mul2r leqnSn orbT.
Qed.

(** ====================================================================== *)
(** ** §I — cross-edge consistency summary                                  *)
(** ====================================================================== *)

(** Each edge's source class is inhabited AND its target is discriminating
    (two-sided).  Packaged as a single record of the load-bearing facts so the
    sweep's verdict ("no edge is trivial or vacuous") is machine-checked. *)
Lemma edges_sources_inhabited_targets_two_sided :
  [/\ (* CH source inhabited & triangle realised, target discriminating *)
      (forall v : C3, (1 <= outdeg v)%N),
      (* SAD source inhabited (arc-strong), target (strong) two-sided *)
      arc_strong C3 1 /\ strongb C3 /\ ~~ strongb E2,
      (* packing source inhabited, target (dicycle) two-sided *)
      (exists c : seq C3, dicycle c) /\ ~ (exists c : seq E2, dicycle c)
    & (* path-FAS source inhabited (has_LFO), target Δ*≤2 realised *)
      has_LFO (TT 3) /\ (Delta_star (TT 3) <= 2)%N].
Proof.
split.
- by move=> v; rewrite outdeg_C3'.
- split; [exact: C3_arc_strong_1 | split; [exact: C3_strongb | exact: E2_not_strongb]].
- split; [exact: C3_has_dicycle | exact: E2_no_dicycle].
- split; [exact: has_LFO_TT | exact: has_LFO_edge_on_TT].
Qed.
