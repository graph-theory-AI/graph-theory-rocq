(** * Cycle.conjectures.implications_D1 — milestone D1 dependency-graph EDGES

    Machine-checked implication / refutation EDGES between the fifteen committed
    D1 FLOW-theory conjecture statements (see [D1.v]).  As in the sibling
    [implications_U6.v] / [implications_U10.v] layers, every SCHEDULED edge is a
    *relative* theorem: a [Qed]-closed [Theorem A_statement -> B_statement]
    provable WITHOUT resolving (proving or refuting) either endpoint.  Bridge
    facts that would otherwise need resolving a conjecture or heavy
    out-of-scope machinery are carried as EXPLICIT hypotheses (declared as
    [external_*_statement] [Prop]s, never [Admitted], never [Axiom]); the file
    stays axiom-free.

    ════════════════════════════════════════════════════════════════════════════
    SCHEDULED EDGE (verified-literature):
        Jaeger's modular-orientation conjecture  ⟹  Tutte's 3-flow conjecture
    ════════════════════════════════════════════════════════════════════════════

      jaegers_modular_orientation_statement  ⟹  three_flow_statement

    Endpoints (verbatim from [D1.v]):
      • Jaeger's modular orientation (Row 10):
          forall (k : nat) (G : mgraph),
            0 < #|edge G| -> 0 < k -> edge_connected G (4 * k) ->
            exists o : edge G -> bool,
              forall v, exists q : int, imbalance o v = ((2*k+1)%N)%:R * q.
      • Tutte's 3-flow (Row 4):
          forall G : mgraph,
            0 < #|edge G| -> edge_connected G 4 -> has_nz_kflow G 3.

    Mathematics.  Jaeger's conjecture at [k = 1] reads: every [4]-edge-connected
    graph has an orientation whose imbalance (indegree − outdegree) is
    [≡ 0 (mod 3)] at every vertex — this is exactly the [k = 1] specialisation,
    since [4*1 = 4] and [2*1+1 = 3].  Tutte's modular-flow / orientation duality
    then turns a mod-[(2k+1)] orientation into a nowhere-zero [(2k+1)]-flow
    (here: a mod-3 orientation into a nowhere-zero 3-flow).  That duality is the
    standard, but separately-formalised, theorem; it is carried here as the
    explicit hypothesis [external_modular_orientation_to_flow_statement] — so the
    edge is the genuine "Jaeger generalises 3-flow" reduction and nothing is
    [Admitted].

    Citation.  Jaeger, "Nowhere-zero flow problems", in Selected Topics in Graph
    Theory 3 (1988) 71–95 (the modular orientation conjecture); the [k = 1] case
    is Tutte's 3-flow conjecture (Tutte 1954).  The orientation⇄flow duality is
    Tutte's theorem (Tutte, "A contribution to the theory of chromatic
    polynomials", Canad. J. Math. 6 (1954) 80–91).  Status: verified-literature
    (re-derived below under the EXACT [D1.v] formulations, modulo the cited
    duality external).

    ────────────────────────────────────────────────────────────────────────────
    SUPPORTING LEMMAS + AUDIT of the remaining node pairs.
    ────────────────────────────────────────────────────────────────────────────

    The three integer-flow conjectures 3-flow (Row 4) / 4-flow (Row 6) / 5-flow
    (Row 7) form an ANTICHAIN under direct relative implication: the nowhere-zero
    [k]-flow CONCLUSION is monotone increasing in [k] ([has_nz_kflow_mono]
    below), while the HYPOTHESIS classes weaken as [k] grows
    (4-edge-connected ⊊ bridgeless-without-Petersen-minor ⊊ bridgeless,
    [edge_connected_4_bridgeless] below).  Hypothesis-strength and
    conclusion-strength therefore move in OPPOSITE directions, so no direct
    [A_statement -> B_statement] closes between any two of them — which is the
    classical fact that the 3-/4-/5-flow conjectures are mutually independent.
    These non-edges are recorded as machine-readable [candidate] annotations
    (none scheduled).  Two further genuine literature relationships
    (Row 13 ⟹ Row 11, and Row 1 generalising Row 14) are likewise [candidate]:
    each is a real implication that does NOT close under the committed
    formulations without substantial extra content (the flow-polynomial's
    leading term / a real-root sign argument for the first; a [t]-range gap plus
    the class-1 ⇒ odd-cut lemma for the second). *)

From GraphTheory Require Import mgraph sgraph treewidth.
From GTBase Require Import base.
From Cycle.foundations Require Import matchings_cuts comp_reduce.
(* [X212] (like the foundations) does not load the algebra library: it must be
   imported BEFORE [all_algebra], otherwise re-exporting [base] after it hides
   the ring structure of [int] ("1 : int" fails to typecheck). *)
From Cycle.conjectures Require Import X212.
From mathcomp Require Import all_algebra all_fingroup.
From Cycle.conjectures Require Import D1.
(* [implications_U6] re-exports [base], which must not come after [all_algebra]
   (see above): it is only Required, and the gc:e184 section uses its inflation
   lemmas through local abbreviations. *)
From Cycle.conjectures Require implications_U6.

Import GRing.Theory Num.Theory.
Set SsrOldRewriteGoalsOrder.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope ring_scope.

(** ================================================================= *)
(** ** Supporting lemmas (the 3-/4-/5-flow antichain is genuine) *)

(** Nowhere-zero flows are monotone in the modulus: a nz [k]-flow is a nz
    [k.+1]-flow (the bound [|phi e| <= k-1] relaxes to [|phi e| <= k]). *)
Lemma has_nz_kflow_mono (G : mgraph) (k : nat) :
  has_nz_kflow G k -> has_nz_kflow G k.+1.
Proof.
move=> [phi [Hcons Hbnd]]; exists phi; split => //.
move=> e; have [Hlo Hhi] := Hbnd e; split => //.
case: k Hhi {Hbnd Hlo} => [|n] Hhi //.
apply: (order.Order.POrderTheory.le_trans Hhi).
by rewrite ler_nat leqnSn.
Qed.

(** (Hypothesis-strength side of the antichain: 4-edge-connectivity is strictly
    stronger than bridgelessness — a bridge is a 1-edge cut and [1 < 4] — so the
    3-flow hypothesis class is contained in the 5-flow one.  Stated in the audit
    prose rather than as a lemma, as the directed-vs-undirected walk encodings
    [walk]/[uwalk] of [is_bridge] and [connected_del_edges] make it tangential
    to the scheduled edge.) *)

(** ================================================================= *)
(** ** External duality (cited, separately formalised — NOT [Admitted]) *)

(** External theorem: W. T. Tutte, A contribution to the theory of chromatic
    polynomials, Canad. J. Math. 6 (1954) 80-91 (the Z_k-flow / k-flow
    equivalence, DOI 10.4153/CJM-1954-010-9), in the modular-orientation form
    used by F. Jaeger, Nowhere-zero flow problems, in Selected Topics in Graph
    Theory 3 (1988) 71-95.
    Claim: for every k >= 1, if a multigraph carries an orientation whose
    imbalance (indegree minus outdegree) is a multiple of 2k+1 at every vertex,
    then it has a nowhere-zero integer (2k+1)-flow. (The constant weighting 1 on
    such an orientation is a nowhere-zero Z_(2k+1)-flow, and Tutte's theorem
    turns a nowhere-zero Z_m-flow into a nowhere-zero integer m-flow.)
    Proved below as [modular_orientation_to_flow] (2026-10-25,
    classical-lemmas TODO 7), by augmenting paths; the reduction that takes it
    as a hypothesis is kept.
    GUARD [0 < k] (2026-09-24, edge-wave audit): without it the statement is
    axiom-free REFUTABLE at k = 0, where the hypothesis is vacuous (every
    integer is a multiple of 1) while the conclusion [has_nz_kflow G 1] demands
    [1 <= |phi e| <= 0] and so fails on every multigraph with an edge; the
    conditional edge below only ever uses k = 1. *)
Definition external_modular_orientation_to_flow_statement : Prop :=
  forall (k : nat) (G : mgraph),
    (0 < k)%N ->
    (exists o : edge G -> bool,
       forall v : G, exists q : int, imbalance o v = ((2 * k + 1)%N)%:R * q) ->
    has_nz_kflow G (2 * k + 1).

(** ================================================================= *)
(** ** The scheduled edge *)

(** The reduction, with the orientation/flow duality as an explicit
    hypothesis.  (Until 2026-10-25 this was the edge gc:e093,
    [status=conditional]; its annotation now sits on
    [unconditional_jaegers_modular_orientation_implies_three_flow] below,
    after [modular_orientation_to_flow].) *)
Theorem jaegers_modular_orientation_implies_three_flow :
  external_modular_orientation_to_flow_statement ->
  jaegers_modular_orientation_statement -> three_flow_statement.
Proof.
move=> Hdual Hjaeger G Hedge H4ec.
have Horient := Hjaeger 1%N G Hedge (ltn0Sn 0) H4ec.
exact: (Hdual 1%N G (ltn0Sn 0) Horient).
Qed.

(** ================================================================= *)
(** ** Row 1 (circular flow numbers of r-graphs) at [t = 2] => Tutte's 3-flow *)

(** External theorem: E. Steffen, Edge-colorings and circular flow numbers on
    regular graphs, J. Graph Theory 79 (2015) 1-7, arXiv:1310.8441
    (DOI 10.1002/jgt.21778), where it is stated that Tutte's 3-flow conjecture
    is EQUIVALENT to the statement that the circular flow number of every
    5-graph is at most 3 (stated there without proof; the direction used here
    is a theorem via M. Kochol, An equivalent version of the 3-flow conjecture,
    J. Combin. Theory Ser. B 83 (2001) 258-261, with the circular flow number
    attained, Goddyn-Tarsi-Zhang 1998); see also the Open Problem Garden context of
    opg:circular_flow_numbers_of_r_graphs, "For t = 2 it is Tutte's 3-flow
    conjecture".
    Claim: the direction of that equivalence used here -- if every 5-graph (a
    5-regular multigraph in which every odd vertex set has an edge cut of at
    least five edges) has circular flow number at most 3, then every
    4-edge-connected multigraph with an edge has a nowhere-zero integer 3-flow.
    Proved below as [steffen_3flow_5graphs] (2026-10-25, classical-lemmas
    TODO 5), without Kochol's reduction: a 4-edge-connected graph inflates to a
    5-graph, whose rational flow rounds to an integer 3-flow; the reduction
    that takes it as a hypothesis is kept. *)
Definition external_steffen_3flow_5graphs_statement : Prop :=
  (forall G : mgraph, (0 < #|G|)%N -> is_2t1_graph G 2 ->
     circular_flow_number_le G 3%:R) ->
  forall G : mgraph, (0 < #|edge G|)%N -> edge_connected G 4 -> has_nz_kflow G 3.

(** [2 + 2/t] at [t = 2] is [3]. *)
Lemma cfn_bound_t2 : 2%:R + 2%:R / 2%:R = 3%:R :> rat.
Proof. by rewrite divff ?pnatr_eq0 // natr1. Qed.

(** The reduction, with Steffen's direction as an explicit hypothesis.  (Until
    2026-10-25 this was the edge gc:e184, [status=conditional]; its annotation
    now sits on [unconditional_circular_flow_numbers_of_r_graphs_implies_three_flow]
    below, after [steffen_3flow_5graphs].) *)
Theorem circular_flow_numbers_of_r_graphs_implies_three_flow :
  external_steffen_3flow_5graphs_statement ->
  circular_flow_numbers_of_r_graphs_statement -> three_flow_statement.
Proof.
move=> Hsteffen Hr; apply: Hsteffen => G Hn H5.
by have := Hr 2%N G (ltnSn 1) Hn H5; rewrite cfn_bound_t2.
Qed.

(** ================================================================= *)
(** ** Row 1 (circular flow numbers of r-graphs) => Row 14 (regular class 1) *)

(** A loopless [(2t+1)]-regular CLASS-1 multigraph with at least one vertex is a
    [(2t+1)]-graph: its maximum degree is [2t+1], so class 1 means chromatic
    index [2t+1], the [2t+1] colour classes are perfect matchings
    ([matchings_cuts.class1_pm_partition]), and each of them meets every odd
    edge cut in an ODD, hence positive, number of edges
    ([matchings_cuts.pm_cut_parity]); being pairwise disjoint they force
    [2t+1 <= #|cut X|] for every odd [X]
    ([matchings_cuts.reg_class1_odd_cut]). *)
Lemma class1_is_2t1 (G : mgraph) (t : nat) :
  (0 < #|G|)%N -> loopless G -> mreg G (2 * t + 1)%N -> is_class1 G ->
  is_2t1_graph G t.
Proof.
move=> Hn hll hreg hc1.
have hD : mDelta G = (2 * t + 1)%N.
  apply/eqP; rewrite eqn_leq; apply/andP; split.
    by apply/bigmax_leqP => v _; rewrite hreg.
  have /card_gt0P[v0 _] : (0 < #|[set: G]|)%N by rewrite cardsT.
  by rewrite -(hreg v0); exact: leq_bigmax.
split => // X hX.
apply: (reg_class1_odd_cut hll hreg) => //.
by rewrite hc1 hD.
Qed.

(** External theorem: W. T. Tutte, On the imbedding of linear graphs in
    surfaces, Proc. London Math. Soc. 51 (1949) 474-483, and A contribution to
    the theory of chromatic polynomials, Canad. J. Math. 6 (1954) 80-91
    (DOI 10.4153/CJM-1954-010-9): a cubic graph has a nowhere-zero 4-flow if and
    only if it is 3-edge-colourable, so a 3-edge-colourable cubic graph has flow
    number, hence circular flow number, at most 4 -- "Tutte's characterization of
    cubic graphs with flow number 4", as cited by E. Steffen,
    Edge-colorings and circular flow numbers on regular graphs, J. Graph Theory
    79 (2015) 1-7, arXiv:1310.8441.
    Claim: every loopless 3-regular class-1 multigraph with at least one vertex
    has circular flow number at most 4, that is, a nowhere-zero rational r-flow
    for every rational r > 4.
    It is needed only for the residual [t = 1] case of the target row, which
    the source row (quantified over [1 < t]) does not cover.  Proved below as
    [tutte_class1_cubic] (2026-10-24, classical-lemmas TODO 6; the direction
    used, from a 3-edge-colouring to a nowhere-zero 4-flow); the reduction
    that takes it as a hypothesis is kept. *)
Definition external_tutte_class1_cubic_statement : Prop :=
  forall G : mgraph,
    (0 < #|G|)%N -> loopless G -> mreg G 3 -> is_class1 G ->
    circular_flow_number_le G 4%:R.

(** [2 + 2/t] at [t = 1] is [4]. *)
Lemma cfn_bound_t1 : 2%:R + 2%:R / 1%:R = 4%:R :> rat.
Proof. by rewrite divr1 -natrD. Qed.

(** The reduction, with Tutte's theorem as an explicit hypothesis.  (Until
    2026-10-24 this was the edge gc:e096, [status=conditional]; its annotation
    now sits on
    [unconditional_circular_flow_numbers_of_r_graphs_implies_circular_flow_number_of_regular_class_1_graphs]
    below, after [tutte_class1_cubic].) *)
Theorem circular_flow_numbers_of_r_graphs_implies_circular_flow_number_of_regular_class_1_graphs :
  external_tutte_class1_cubic_statement ->
  circular_flow_numbers_of_r_graphs_statement ->
  circular_flow_number_of_regular_class_1_graphs_statement.
Proof.
move=> Htutte Hr t G ht Hn hll hreg hc1.
case: (ltnP 1 t) => [h1t|ht1].
  exact: Hr t G h1t Hn (class1_is_2t1 Hn hll hreg hc1).
have ht1' : t = 1 by apply/eqP; rewrite eqn_leq ht1 ht.
rewrite ht1' in hreg *.
rewrite cfn_bound_t1.
by apply: Htutte.
Qed.

(** ================================================================= *)
(** ** gc:e246 -- orientable 5-cycle double cover => 5-flow (unconditional) *)

(** An orientable double cover by five even subgraphs [C i] with balanced
    orientations [d i] yields the integer 5-flow [sum_i i * osgn (C i) (d i)]:
    every summand is a circulation, and every edge lies in exactly two members
    with opposite signs, so its value is [+-(i - j)] with [i != j] in ['I_5].
    Since the source row needs a CONNECTED carrier and the target row only a
    bridgeless one, the source is applied to the collapsed graph
    [comp_reduce.Hc r0] (same edge type), and conservation is transported back
    vertex by vertex, the component representatives by a component-sum
    argument. *)

(** indicator sums over int *)
Lemma sum_indz (T : finType) (C : {set T}) (P : pred T) :
  \sum_(x | P x) (if x \in C then (1 : int) else 0) = #|[set x in C | P x]|%:R.
Proof.
transitivity (\sum_(x : T) (if (x \in C) && P x then (1 : int) else 0)).
  rewrite big_mkcond /=; apply: eq_bigr => x _.
  by case: (P x); rewrite ?andbT ?andbF //; case: (x \in C).
rewrite card_setIsum natr_sum [RHS]big_mkcond /=; apply: eq_bigr => x _.
by case: (x \in C) => //=; case: (P x).
Qed.

Lemma int_natsub_bound5 (m n : nat) : m != n -> (m < 5)%N -> (n < 5)%N ->
  (1 <= `|(m%:R - n%:R : int)|) /\ (`|(m%:R - n%:R : int)| <= 4%:R).
Proof.
move=> hne hm hn.
case: (ltngtP m n) => [h|h|/eqP]; last by rewrite (negbTE hne).
- rewrite -opprB -natrB ?(ltnW h) // normrN normr_nat; split.
    by rewrite ler1n subn_gt0.
  by rewrite ler_nat; apply: (leq_trans (leq_subr m n)); rewrite -ltnS.
- rewrite -natrB ?(ltnW h) // normr_nat; split.
    by rewrite ler1n subn_gt0.
  by rewrite ler_nat; apply: (leq_trans (leq_subr n m)); rewrite -ltnS.
Qed.

Lemma iconservativeZ (G : mgraph) (a : int) (phi : edge G -> int) :
  iconservative phi -> iconservative (fun e => a * phi e).
Proof. by move=> h v; rewrite -!mulr_sumr h. Qed.

Lemma iconservative_bigsum (G : mgraph) (I : finType) (F : I -> edge G -> int) :
  (forall i : I, iconservative (F i)) ->
  iconservative (fun e => \sum_(i : I) F i e).
Proof.
move=> hF v; rewrite exchange_big [RHS]exchange_big /=.
by apply: eq_bigr => i _; exact: (hF i v).
Qed.

Definition osgn (G : mgraph) (C : {set edge G}) (d : edge G -> bool)
    (e : edge G) : int := if e \in C then (if d e then 1 else -1) else 0.

Lemma osgn_conservative (G : mgraph) (C : {set edge G}) (d : edge G -> bool) :
  x212_balanced C d -> iconservative (osgn C d).
Proof.
move=> hb v.
pose ind := fun e : edge G => if e \in C then (1 : int) else 0.
have key : forall P : pred (edge G),
    \sum_(e | P e) osgn C d e
    = \sum_(e | P e && d e) ind e - \sum_(e | P e && ~~ d e) ind e.
  move=> P; rewrite (bigID d) /=; congr (_ + _).
    by apply: eq_bigr => e /andP[_ he]; rewrite /osgn /ind he.
  rewrite -sumrN; apply: eq_bigr => e /andP[_ he].
  by rewrite /osgn /ind (negbTE he); case: (e \in C); rewrite ?oppr0.
have hbal : \sum_(e | x212_tail d e == v) ind e
          = \sum_(e | x212_head d e == v) ind e.
  by rewrite /ind !sum_indz hb.
have esplit : forall (Q : pred (edge G)),
    \sum_(e | Q e) ind e
    = \sum_(e | Q e && d e) ind e + \sum_(e | Q e && ~~ d e) ind e.
  by move=> Q; rewrite (bigID d) /=.
have e1 : \sum_(e | (x212_tail d e == v) && d e) ind e
        = \sum_(e | (source e == v) && d e) ind e.
  by apply: eq_bigl => e; rewrite /x212_tail; case: (d e); rewrite ?andbF.
have e2 : \sum_(e | (x212_tail d e == v) && ~~ d e) ind e
        = \sum_(e | (target e == v) && ~~ d e) ind e.
  by apply: eq_bigl => e; rewrite /x212_tail; case: (d e); rewrite ?andbF.
have e3 : \sum_(e | (x212_head d e == v) && d e) ind e
        = \sum_(e | (target e == v) && d e) ind e.
  by apply: eq_bigl => e; rewrite /x212_head; case: (d e); rewrite ?andbF.
have e4 : \sum_(e | (x212_head d e == v) && ~~ d e) ind e
        = \sum_(e | (source e == v) && ~~ d e) ind e.
  by apply: eq_bigl => e; rewrite /x212_head; case: (d e); rewrite ?andbF.
move: hbal; rewrite (esplit (fun e => x212_tail d e == v))
                    (esplit (fun e => x212_head d e == v)) e1 e2 e3 e4 => h.
rewrite (key (fun e => source e == v)) (key (fun e => target e == v)).
apply/eqP; rewrite subr_eq.
have -> : \sum_(e | (target e == v) && d e) ind e
        = \sum_(e | (source e == v) && d e) ind e
          + \sum_(e | (target e == v) && ~~ d e) ind e
          - \sum_(e | (source e == v) && ~~ d e) ind e.
  by rewrite h addrK.
by rewrite addrAC subrK addrK.
Qed.

Definition oflow (G : mgraph) (C : 'I_5 -> {set edge G})
    (d : 'I_5 -> edge G -> bool) (e : edge G) : int :=
  \sum_(i : 'I_5) (val i)%:R * osgn (C i) (d i) e.

Lemma oflow_conservative (G : mgraph) (C : 'I_5 -> {set edge G})
    (d : 'I_5 -> edge G -> bool) :
  (forall i : 'I_5, x212_balanced (C i) (d i)) -> iconservative (oflow C d).
Proof.
move=> hb; apply: iconservative_bigsum => i.
exact: (iconservativeZ _ (osgn_conservative (hb i))).
Qed.

Lemma oflow_bounded (G : mgraph) (C : 'I_5 -> {set edge G})
    (d : 'I_5 -> edge G -> bool) :
  (forall e : edge G, #|[set i : 'I_5 | e \in C i]| = 2) ->
  (forall (e : edge G) (i j : 'I_5),
     i != j -> e \in C i -> e \in C j -> d i e != d j e) ->
  int_bounded 5 (oflow C d).
Proof.
move=> hcov hopp e.
have /cards2P[i [j [hij hS]]] : #|[set k : 'I_5 | e \in C k]| == 2.
  by rewrite hcov.
have hi : e \in C i by have := set21 i j; rewrite -hS inE.
have hj : e \in C j by have := set22 i j; rewrite -hS inE.
have hz : forall k : 'I_5, k \notin [set i; j] ->
    (val k)%:R * osgn (C k) (d k) e = 0.
  by move=> k; rewrite -hS inE => hk; rewrite /osgn (negbTE hk) mulr0.
have hsum : oflow C d e
          = (val i)%:R * osgn (C i) (d i) e + (val j)%:R * osgn (C j) (d j) e.
  rewrite /oflow (bigID (fun k : 'I_5 => k \in [set i; j])) /=.
  rewrite [X in _ + X]big1; last by move=> k /hz ->.
  by rewrite addr0 big_setU1 ?big_set1 // inE.
have hd := hopp e i j hij hi hj.
have hvij : val i != val j by rewrite val_eqE.
have hvji : val j != val i by rewrite eq_sym.
rewrite hsum /osgn hi hj.
case hdi : (d i e); case hdj : (d j e).
- by move: hd; rewrite hdi hdj eqxx.
- rewrite mulr1 mulrN1.
  exact: int_natsub_bound5 hvij (ltn_ord i) (ltn_ord j).
- rewrite mulrN1 mulr1 addrC.
  exact: int_natsub_bound5 hvji (ltn_ord j) (ltn_ord i).
- by move: hd; rewrite hdi hdj eqxx.
Qed.

Lemma orient5_has_nz_kflow (G : mgraph) :
  x212_orientable_5_even_double_cover G -> has_nz_kflow G 5.
Proof.
move=> [C [d [hev hbal hcov hopp]]].
exists (oflow C d); split; first exact: oflow_conservative hbal.
exact: oflow_bounded hcov hopp.
Qed.

(** ** Conservation transfers back from the collapsed graph *)

Lemma sum_ep_comp (G : mgraph) (phi : edge G -> int) (b : bool) (S : {set G}) :
  \sum_(v in S) \sum_(e | endpoint b e == v) phi e
  = \sum_(e | endpoint b e \in S) phi e.
Proof.
rewrite (exchange_big_dep (fun e => endpoint b e \in S)) /=; last first.
  by move=> v e hv /eqP ->.
apply: eq_bigr => e he; rewrite (big_pred1 (endpoint b e)) // => v /=.
by rewrite eq_sym andb_idl // => /eqP ->.
Qed.

Lemma iconservative_rep (G : mgraph) (phi : edge G -> int) (r : G) :
  (forall v, v \in mcomp r -> v != r ->
     \sum_(e | source e == v) phi e = \sum_(e | target e == v) phi e) ->
  \sum_(e | source e == r) phi e = \sum_(e | target e == r) phi e.
Proof.
move=> h.
have htot : \sum_(v in mcomp r) \sum_(e | source e == v) phi e
          = \sum_(v in mcomp r) \sum_(e | target e == v) phi e.
  rewrite !sum_ep_comp; apply: eq_bigl => e; apply/idP/idP.
  - exact: (@mcomp_closed G r e false).
  - exact: (@mcomp_closed G r e true).
rewrite (bigD1 r (mcomp_id r)) [RHS](bigD1 r (mcomp_id r)) /= in htot.
have hrest : \sum_(v in mcomp r | v != r) \sum_(e | source e == v) phi e
           = \sum_(v in mcomp r | v != r) \sum_(e | target e == v) phi e.
  by apply: eq_bigr => v /andP[hv hvr]; exact: h.
by move: htot; rewrite hrest => /addIr.
Qed.

Lemma iconservative_collapse (G : mgraph) (r0 : G) (phi : edge G -> int) :
  mroot r0 = r0 -> @iconservative (Hc r0) phi -> iconservative phi.
Proof.
move=> hr0 hc.
have hnr : forall w : G, mroot w != w ->
    \sum_(e | source e == w) phi e = \sum_(e | target e == w) phi e.
  move=> w hw.
  have hv : vpred r0 w by rewrite /vpred hw.
  have key : forall b : bool,
      \sum_(e | @endpoint _ _ (Hc r0) b e == Sub w hv) phi e
      = \sum_(e | endpoint b e == w) phi e.
    move=> b; apply: eq_bigl => e.
    by rewrite Hc_ep -val_eqE val_prj SubK (pr_eqE _ hr0 hw).
  by rewrite -(key false) -(key true); exact: (hc (Sub w hv)).
move=> v; case: (boolP (mroot v == v)) => [/eqP hvr|]; last exact: hnr.
apply: iconservative_rep => w hw hwv; apply: hnr.
apply/negP => /eqP hww; move/negP: hwv; apply.
by rewrite (mroot_unique hvr hw hww).
Qed.

(*@EDGE from=orientable_five_cycle_double_cover_statement to=five_flow_statement kind=implies status=verified proof=orientable_five_cycle_double_cover_implies_five_flow cite="gc:e246" note="Unconditional. From an orientable 5-even-subgraph double cover (C,d) the integer weighting oflow e = sum_{i in I_5} i * osgn_i e (osgn_i e = +1/-1 by d i e on C i, 0 elsewhere) is a nowhere-zero integer 5-flow: each osgn_i is Kirchhoff because x212_balanced is (osgn_conservative), iconservative is closed under integer combinations (iconservativeZ, iconservative_bigsum), and on an edge in exactly the two members i != j with opposite orientations oflow e = +-(i-j), so 1 <= |oflow e| <= 4 (oflow_bounded). The connected-vs-bridgeless gap: the source is applied to the collapsed graph comp_reduce.Hc (connected, bridgeless, same edge type: Hc_mconnected, Hc_bridgeless), and Kirchhoff transfers back since non-representatives keep their incidences and a representative is balanced because the flow summed over its whole component cancels (iconservative_collapse, iconservative_rep, sum_ep_comp)." *)
Theorem orientable_five_cycle_double_cover_implies_five_flow :
  orientable_five_cycle_double_cover_statement -> five_flow_statement.
Proof.
move=> Hsrc G hedge hbl.
case/card_gt0P: hedge => e0 _.
pose r0 := mroot (source e0).
have hr0 : mroot r0 = r0 := mroot_root (source e0).
have [phi [hc hb]] : has_nz_kflow (Hc r0) 5.
  apply: orient5_has_nz_kflow; apply: Hsrc.
    exact: (Hc_card_gt0 r0 (source e0)).
  by split; [exact: Hc_mconnected hr0 | exact: Hc_bridgeless hbl].
by exists phi; split; [exact: iconservative_collapse hr0 hc | exact: hb].
Qed.

(** ================================================================= *)
(** ** gc:e096 at [t = 1]: Tutte's theorem for class-1 cubic multigraphs
       (classical-lemmas TODO 6, the direction used) *)

(** A 3-edge-colouring of a loopless cubic multigraph yields a nowhere-zero
    integer 4-flow.  The colour classes are perfect matchings
    ([matchings_cuts.class1_pm_partition]), so the complement of a class is a
    2-regular edge set.  Balanced orientations [dA] of the complement [A] of
    one class and [dB] of the complement [B] of another give the Kirchhoff
    weighting [osgn A dA + 2 * osgn B dB]; since no edge lies outside both
    complements, its values are in {+-1, +-2, +-3}.  Balanced orientations of
    even edge sets come from closed routes: [spath_step_route] and
    [has_closed_route] are [cycle_space.spath_step] and [has_circuit] returning
    the closed route with distinct edges instead of the circuit it spans, and
    following such a route orients its edges in a balanced way. *)

Lemma spath_step_route (G : mgraph) (C : {set edge G}) (x : G)
    (r : seq (edge G * bool)) :
  (forall v : G, subdeg C v != 1) -> r != [::] -> spath C x r ->
  (exists (y : G) (s : seq (edge G * bool)),
     [/\ s != [::], rwalk y s, rlast y s = y, uniq (redges s)
       & all (fun a : edge G * bool => a.1 \in C) s]) \/
  (exists a : edge G * bool, spath C x (rcons r a)).
Proof.
move=> Cdeg rn0 /and4P[wr aC ue uv].
have esC : eset r \subset C := eset_sub aC.
have htl := rwalk_tails wr.
have uh : uniq (map (@rhd G) r) by move: uv => /andP[].
have ynotl : rlast x r \notin map (@rtl G) r.
  move: uv; rewrite -htl cat_uniq => /and3P[_ h _].
  by move: h; rewrite /= orbF.
have yhd : rlast x r \in map (@rhd G) r.
  rewrite /rlast; apply: last_mem.
  by rewrite -size_eq0 size_map size_eq0.
have hdeg : subdeg (eset r) (rlast x r) = 1.
  rewrite (subdeg_eset _ ue).
  have -> : count (fun a : edge G * bool => rtl a == rlast x r) r = 0.
    apply/eqP; rewrite -leqn0 leqNgt -has_count.
    apply/negP => /hasP[a ar /eqP ha].
    by move: ynotl; rewrite -ha (map_f _ ar).
  rewrite add0n.
  have := count_uniq_mem (rlast x r) uh.
  by rewrite count_map yhd.
have ygt : (0 < subdeg (C :\: eset r) (rlast x r))%N.
  have hsum := subdeg_setD (rlast x r) esC.
  rewrite hdeg in hsum.
  case: (posnP (subdeg (C :\: eset r) (rlast x r))) => // h0.
  by move: (Cdeg (rlast x r)); rewrite hsum h0 addn0 eqxx.
have [f fD [b hb]] := subdeg_gt0P ygt.
move: fD; rewrite in_setD inE => /andP[fnotr fC].
case: (boolP (endpoint (~~ b) f \in x :: map (@rhd G) r)) => [zin|znot]; last first.
- right; exists (f, b); apply/and4P; split.
  + by rewrite rwalk_rcons wr /=; apply/eqP; exact: hb.
  + by rewrite all_rcons /= fC.
  + rewrite /redges map_rcons rcons_uniq.
    by apply/andP; split; [exact: fnotr | exact: ue].
  + rewrite map_rcons -rcons_cons rcons_uniq.
    by apply/andP; split; [exact: znot | exact: uv].
- left.
  have [r1 [r2 [req r1z]]] := rverts_split zin.
  have wr2 : rwalk (endpoint (~~ b) f) r2.
    by move: wr; rewrite req rwalk_cat -r1z => /andP[].
  have l2 : rlast (endpoint (~~ b) f) r2 = rlast x r.
    by rewrite -r1z -rlast_cat -req.
  exists (endpoint (~~ b) f), (r2 ++ [:: (f, b)]); split.
  + by rewrite -size_eq0 size_cat /= addn1.
  + by rewrite rwalk_cat wr2 /= l2 andbT; apply/eqP; exact: hb.
  + by rewrite rlast_cat /= l2.
  + rewrite redges_cat cat_uniq /=.
    apply/and3P; split; last by [].
    * by move: ue; rewrite req redges_cat cat_uniq => /and3P[_ _].
    * rewrite orbF; apply/negP => hf.
      move: fnotr; rewrite req redges_cat mem_cat hf orbT.
      by move/negP; apply.
  + rewrite all_cat; apply/andP; split; last by rewrite /= fC.
    by move: aC; rewrite req all_cat => /andP[].
Qed.

Lemma has_closed_route_bound (G : mgraph) (C : {set edge G}) (n : nat) :
  (forall v : G, subdeg C v != 1) ->
  forall (x : G) (r : seq (edge G * bool)),
    spath C x r -> r != [::] -> (#|G| <= size r + n)%N ->
    exists (y : G) (s : seq (edge G * bool)),
      [/\ s != [::], rwalk y s, rlast y s = y, uniq (redges s)
        & all (fun a : edge G * bool => a.1 \in C) s].
Proof.
move=> Cdeg; elim: n => [|n IH] x r sp rn0 hb.
- have uv : uniq (x :: map (@rhd G) r) by case/and4P: sp.
  have h := uniq_size_leq uv.
  rewrite /= size_map in h; rewrite addn0 in hb.
  by move: (leq_trans h hb); rewrite ltnn.
- have [hs|[a spa]] := spath_step_route Cdeg rn0 sp; first exact: hs.
  apply: (IH x (rcons r a) spa).
  + by rewrite -size_eq0 size_rcons.
  + by rewrite size_rcons addSn -addnS.
Qed.

Lemma has_closed_route (G : mgraph) (C : {set edge G}) :
  C != set0 -> (forall v : G, subdeg C v != 1) ->
  exists (y : G) (s : seq (edge G * bool)),
    [/\ s != [::], rwalk y s, rlast y s = y, uniq (redges s)
      & all (fun a : edge G * bool => a.1 \in C) s].
Proof.
move=> /set0Pn[e eC] Cdeg.
case: (boolP (source e == target e)) => [/eqP loop|nloop].
- exists (source e), [:: (e, false)]; split.
  + by [].
  + by rewrite /= eqxx.
  + by rewrite /rlast /rhd /= -loop.
  + by [].
  + by rewrite /= eC.
- apply: (@has_closed_route_bound G C #|G| Cdeg (source e) [:: (e, false)]).
  + rewrite /spath; apply/and4P; split.
    * by rewrite /= eqxx.
    * by rewrite /= eC.
    * by rewrite /redges /=.
    * rewrite /= andbT mem_seq1; apply/negP => /eqP h.
      by move: nloop; rewrite h /rhd /= eqxx.
  + by [].
  + by rewrite /= add1n; exact: leqnSn.
Qed.

(** A route with distinct edges traverses each of its edges in one direction. *)
Lemma route_dir_unique (G : mgraph) (s : seq (edge G * bool)) (e : edge G)
    (b b' : bool) :
  uniq (redges s) -> (e, b) \in s -> (e, b') \in s -> b = b'.
Proof.
move=> u /(nthP (e, b))[i hi ei] /(nthP (e, b))[j hj ej].
have hij : i = j.
  apply: (uniqP e u); rewrite ?inE ?size_map //.
  by rewrite /redges !(nth_map (e, b)) // ei ej.
by move: ei ej; rewrite hij => -> [].
Qed.

(** A closed route leaves every vertex as often as it enters it. *)
Lemma closed_route_count (G : mgraph) (y : G) (s : seq (edge G * bool)) (v : G) :
  rwalk y s -> rlast y s = y ->
  count (fun a : edge G * bool => rtl a == v) s
  = count (fun a : edge G * bool => rhd a == v) s.
Proof.
move=> w l.
have htl : map (@rtl G) s ++ [:: y] = y :: map (@rhd G) s.
  by have := rwalk_tails w; rewrite l.
have h := congr1 (count (pred1 v)) htl.
apply/eqP; move: h; rewrite count_cat /= addn0 addnC !count_map.
by move/eqP; rewrite eqn_add2l.
Qed.

(** Following a closed route with distinct edges orients its edge set in a
    balanced way: an edge keeps its reference direction iff the route
    traverses it forwards. *)
Lemma closed_route_balanced (G : mgraph) (y : G) (s : seq (edge G * bool)) :
  rwalk y s -> rlast y s = y -> uniq (redges s) ->
  x212_balanced (eset s) (fun e => (e, false) \in s).
Proof.
move=> w l u v.
set d := fun e => (e, false) \in s.
have htl : {in s, forall a, x212_tail d a.1 = rtl a}.
  case=> e [] ha; rewrite /x212_tail /d /rtl /=; last by rewrite ha.
  by case: ifP => // hf; have := route_dir_unique u ha hf.
have hhd : {in s, forall a, x212_head d a.1 = rhd a}.
  case=> e [] ha; rewrite /x212_head /d /rhd /=; last by rewrite ha.
  by case: ifP => // hf; have := route_dir_unique u ha hf.
have hcnt : forall (F : edge G -> G) (g : edge G * bool -> G),
    {in s, forall a, F a.1 = g a} ->
    #|[set e in eset s | F e == v]| = count (fun a => g a == v) s.
  move=> F g hFg.
  have -> : [set e in eset s | F e == v] = [set e in redges s | F e == v].
    by apply/setP => e; rewrite !inE.
  rewrite (card_seq_filter _ u) count_map.
  by apply: eq_in_count => a ha /=; rewrite hFg.
by rewrite (hcnt _ _ htl) (hcnt _ _ hhd) (closed_route_count v w l).
Qed.

(** Every even edge set has a balanced orientation: peel off one closed route
    and recurse on the rest (as in [cycle_space.even_circuit_decomposition]). *)
Lemma even_balanced_bound (G : mgraph) (n : nat) (C : {set edge G}) :
  (#|C| <= n)%N -> (forall v : G, ~~ odd (subdeg C v)) ->
  exists d : edge G -> bool, x212_balanced C d.
Proof.
elim: n C => [|n IH] C hn Ce.
  have C0 : C = set0 by apply/eqP; rewrite -cards_eq0 -leqn0.
  by exists xpredT => v; rewrite C0; apply: eq_card => e; rewrite !inE.
case: (boolP (C == set0)) => [/eqP C0|Cn0].
  by exists xpredT => v; rewrite C0; apply: eq_card => e; rewrite !inE.
have Cd1 : forall v : G, subdeg C v != 1.
  by move=> v; apply: contraNneq (Ce v) => ->.
have [y [s [sn0 w l u aC]]] := has_closed_route Cn0 Cd1.
have DsubC : eset s \subset C := eset_sub aC.
have Dev : forall v : G, ~~ odd (subdeg (eset s) v).
  move=> v; rewrite (subdeg_eset v u) (closed_route_count v w l).
  by rewrite addnn odd_double.
have [a sa] : exists a, a \in s.
  by move: sn0; case: (s) => [//|a s0] _; exists a; rewrite in_cons eqxx.
have hlt : (#|C :\: eset s| <= n)%N.
  rewrite cardsD (setIidPr DsubC).
  have hD1 : (1 <= #|eset s|)%N.
    by apply/card_gt0P; exists a.1; rewrite inE; exact: map_f sa.
  apply: (leq_trans (leq_sub2l #|C| hD1)).
  by rewrite leq_subLR add1n.
have Dev' : forall v : G, ~~ odd (subdeg (C :\: eset s) v).
  move=> v; apply: subdeg_setD_even;
    [exact: DsubC | exact: Ce v | exact: Dev v].
have [d' hd'] := IH _ hlt Dev'.
have hr := closed_route_balanced w l u.
set dr := fun e => (e, false) \in s in hr.
pose dd := fun e => if e \in eset s then dr e else d' e.
exists dd => v.
have key : forall P : pred (edge G),
    #|[set e in C | P e]|
    = #|[set e in eset s | P e]| + #|[set e in C :\: eset s | P e]|.
  move=> P; rewrite -(cardsID (eset s) [set e in C | P e]).
  congr (_ + _); apply: eq_card => e; rewrite !inE; last by rewrite andbA.
  case he: (e \in redges s); rewrite ?andbF ?andbT //=.
  by have := subsetP DsubC e; rewrite inE he => /(_ isT) ->.
have hdd : forall (S : {set edge G}) (d : edge G -> bool)
    (F : (edge G -> bool) -> edge G -> G),
    (forall d0 e, F d0 e = if d0 e then F xpredT e else F xpred0 e) ->
    {in S, dd =1 d} ->
    #|[set e in S | F dd e == v]| = #|[set e in S | F d e == v]|.
  move=> S d F hF hS; apply: eq_card => e; rewrite !inE.
  by case eS: (e \in S) => //=; rewrite hF [in RHS]hF hS.
have hT : forall (d0 : edge G -> bool) (e : edge G),
    x212_tail d0 e = if d0 e then x212_tail xpredT e else x212_tail xpred0 e.
  by move=> d0 e; rewrite /x212_tail; case: (d0 e).
have hH : forall (d0 : edge G -> bool) (e : edge G),
    x212_head d0 e = if d0 e then x212_head xpredT e else x212_head xpred0 e.
  by move=> d0 e; rewrite /x212_head; case: (d0 e).
have hin : {in eset s, dd =1 dr} by move=> e he; rewrite /dd he.
have hout : {in C :\: eset s, dd =1 d'}.
  by move=> e; rewrite inE => /andP[he _]; rewrite /dd (negbTE he).
rewrite !key (hdd _ _ _ hT hin) (hdd _ _ _ hH hin).
by rewrite (hdd _ _ _ hT hout) (hdd _ _ _ hH hout) (hr v) (hd' v).
Qed.

Lemma even_balanced (G : mgraph) (C : {set edge G}) :
  (forall v : G, ~~ odd (subdeg C v)) ->
  exists d : edge G -> bool, x212_balanced C d.
Proof. exact: (even_balanced_bound (leqnn #|C|)). Qed.

(** The complement of a perfect matching of a cubic multigraph is 2-regular. *)
Lemma cubic_pm_compl_even (G : mgraph) (M : {set edge G}) :
  mreg G 3 -> (forall v : G, subdeg M v = 1) ->
  forall v : G, ~~ odd (subdeg (~: M) v).
Proof.
move=> hreg hM v.
have h := subdeg_setD v (subsetT M).
rewrite setTD hM in h.
have h3 : subdeg [set: edge G] v = 3 by exact: hreg v.
have -> : subdeg (~: M) v = 2 by apply/eqP; rewrite -(eqn_add2l 1) -h h3.
by [].
Qed.

(** A loopless cubic multigraph of chromatic index 3 has a nowhere-zero
    integer 4-flow. *)
Lemma class1_cubic_nz_4flow (G : mgraph) :
  loopless G -> mreg G 3 -> chromatic_index G = 3 -> has_nz_kflow G 4.
Proof.
move=> hll hreg hci.
have [P [hP3 hpart hpm]] := class1_pm_partition hll hreg hci.
have /card_gt1P[Ma [Mb [hMa hMb hab]]] : (1 < #|P|)%N by rewrite hP3.
have htriv : trivIset P by case/and3P: hpart.
have hdis : [disjoint Ma & Mb] := trivIsetP htriv Ma Mb hMa hMb hab.
have [dA hA] := even_balanced (cubic_pm_compl_even hreg (hpm Ma hMa)).
have [dB hB] := even_balanced (cubic_pm_compl_even hreg (hpm Mb hMb)).
exists (fun e => osgn (~: Ma) dA e + 2%:R * osgn (~: Mb) dB e); split.
  move=> v; rewrite !big_split /= -!mulr_sumr.
  by rewrite (osgn_conservative hA v) (osgn_conservative hB v).
move=> e; rewrite /osgn !inE.
case hea : (e \in Ma); case heb : (e \in Mb) => /=.
- by move: (disjointFr hdis hea); rewrite heb.
- by case: (dB e).
- by case: (dA e).
- by case: (dA e); case: (dB e).
Qed.

(** Tutte's theorem, the direction used by gc:e096: a loopless 3-regular
    class-1 multigraph has circular flow number at most 4 (its integer 4-flow
    is a rational r-flow for every r > 4). *)
Theorem tutte_class1_cubic : external_tutte_class1_cubic_statement.
Proof.
move=> G Hn hll hreg hc1.
have hD : mDelta G = 3%N.
  apply/eqP; rewrite eqn_leq; apply/andP; split.
    by apply/bigmax_leqP => v _; rewrite hreg.
  have /card_gt0P[v0 _] : (0 < #|[set: G]|)%N by rewrite cardsT.
  by rewrite -(hreg v0); exact: leq_bigmax.
have [phi [hc hb]] := class1_cubic_nz_4flow hll hreg (etrans hc1 hD).
move=> r hr; exists (fun e => (phi e)%:~R); split.
  by move=> v; rewrite -!rmorph_sum /= (hc v).
move=> e; have [h1 h3] := hb e.
rewrite -intr_norm; split; first by rewrite ler1z.
apply: (@mathcomp.order.order.Order.POrderTheory.le_trans _ _ 3%:R).
  by move: h3; rewrite -(ler_int rat).
rewrite lerBrDr natr1; exact: mathcomp.order.order.Order.POrderTheory.ltW.
Qed.

(*@EDGE from=circular_flow_numbers_of_r_graphs_statement to=circular_flow_number_of_regular_class_1_graphs_statement kind=implies status=verified proof=unconditional_circular_flow_numbers_of_r_graphs_implies_circular_flow_number_of_regular_class_1_graphs cite="gc:e096" note="For t>1 the hypothesis class is contained: class1_is_2t1 turns loopless + (2t+1)-regular + class 1 into a (2t+1)-graph, via the 2t+1 colour classes being perfect matchings (matchings_cuts.class1_pm_partition) each meeting every odd cut in an odd number of edges (matchings_cuts.pm_cut_parity), so Row 1 applies verbatim. The residual t=1 case, which Row 1 (1<t) does not cover, is Tutte's characterization of cubic graphs with flow number 4, proved as tutte_class1_cubic: the complements A, B of two colour classes are 2-regular, balanced orientations of them (from closed routes) give osgn A dA + 2 osgn B dB, a nowhere-zero integer 4-flow, hence a rational r-flow for every r > 4" *)
Theorem unconditional_circular_flow_numbers_of_r_graphs_implies_circular_flow_number_of_regular_class_1_graphs :
  circular_flow_numbers_of_r_graphs_statement ->
  circular_flow_number_of_regular_class_1_graphs_statement.
Proof.
exact: circular_flow_numbers_of_r_graphs_implies_circular_flow_number_of_regular_class_1_graphs
  tutte_class1_cubic.
Qed.


(** ================================================================= *)
(** ** gc:e093: Tutte's orientation/flow duality at [2k+1], [k >= 1]
       (classical-lemmas TODO 7)

    An orientation [o] whose imbalance is [m * q v] at every vertex
    ([m = 2k+1]) gives a nowhere-zero integer [m]-flow: along [o], put [1] on
    the edges outside an edge set [X] and [1 - m] on those of [X].  The result
    is conservative exactly when the net inflow of [X] along [o] is [q v] at
    every vertex, and such an [X] exists ([odiff_demand]) by augmenting paths.
    Toggling the edges of a residual path ([ores], [odiff_path]) moves one unit
    of deviation from its start to its end.  When no residual path from a
    deficit vertex reaches a surplus vertex, the set [S] such paths reach is
    closed, so [S] receives exactly its entering edges ([odiff_closed]); the
    cut count ([imbalance_cut]) and [m >= 1] then make the deviation over [S]
    non-negative, a contradiction. *)

Section ModOrient.
Variables (G : mgraph) (o : edge G -> bool).

(** Net inflow, along [o], of the edge set [X] at [v]. *)
Definition odiff (X : {set edge G}) (v : G) : int :=
  (#|[set e in X | ohead o e == v]|)%:R - (#|[set e in X | otail o e == v]|)%:R.

(** Residual steps: [a -> b] through an edge outside [X] entering [a] from
    [b], or an edge of [X] leaving [a] towards [b]. *)
Definition ores (X : {set edge G}) : rel G := fun a b =>
  [exists e, ((e \notin X) && (ohead o e == a) && (otail o e == b))
          || ((e \in X) && (otail o e == a) && (ohead o e == b))].

Definition otoggle (X : {set edge G}) (e : edge G) : {set edge G} :=
  if e \in X then X :\ e else e |: X.

Lemma card_otoggle (X : {set edge G}) (e : edge G) (P : pred (edge G)) :
  (#|[set f in otoggle X e | P f]|%:R : int)
  = #|[set f in X | P f]|%:R + (if e \in X then - (P e)%:R else (P e)%:R).
Proof.
rewrite /otoggle; case: ifP => he.
  have -> : [set f in X :\ e | P f] = [set f in X | P f] :\ e.
    by apply/setP => f; rewrite !inE andbA.
  rewrite [in RHS](cardsD1 e [set f in X | P f]) inE he /= natrD.
  by rewrite addrC addKr.
case hP: (P e).
  rewrite (_ : [set f in e |: X | P f] = e |: [set f in X | P f]); last first.
    by apply/setP => f; rewrite !inE; case: eqP => // ->; rewrite hP.
  by rewrite cardsU1 inE he /= natrD addrC.
rewrite (_ : [set f in e |: X | P f] = [set f in X | P f]); last first.
  by apply/setP => f; rewrite !inE; case: eqP => // ->; rewrite hP he.
by rewrite addr0.
Qed.

Lemma odiff_step (X : {set edge G}) (a b : G) :
  ores X a b -> exists e,
    (forall v, odiff (otoggle X e) v = odiff X v + (v == a)%:R - (v == b)%:R)
    /\ (forall a' b', a' != a -> b' != a -> ores X a' b' ->
          ores (otoggle X e) a' b').
Proof.
case/existsP => e he; exists e.
have hea : (ohead o e == a) || (otail o e == a).
  by case/orP: he => /andP[/andP[_ ->]] //= _; rewrite orbT.
split.
  move=> v; rewrite /odiff !card_otoggle.
  case/orP: he => /andP[/andP[hX /eqP hh] /eqP ht];
    rewrite ?(negbTE hX) ?hX hh ht ![_ == v]eq_sym.
    by rewrite opprD addrACA addrA.
  rewrite opprB.
  set h := (#|[set f in X | ohead o f == v]|%:R : int).
  set t := (#|[set f in X | otail o f == v]|%:R : int).
  rewrite -!addrA; congr (_ + _); rewrite addrCA [RHS]addrCA; congr (_ + _).
  by rewrite addrC.
(* A residual step between two vertices other than [a] uses an edge other
   than [e], whose membership the toggle does not change. *)
move=> a' b' ha hb /existsP[f hf]; apply/existsP; exists f.
have hfe : f != e.
  apply/eqP => fe; rewrite fe in hf.
  move/eqP: ha => ha; move/eqP: hb => hb.
  by case/orP: hf => /andP[/andP[_ /eqP h1] /eqP h2];
    case/orP: hea => /eqP h3; congruence.
have hmem : (f \in otoggle X e) = (f \in X).
  by rewrite /otoggle; case: ifP => _; rewrite !inE (negbTE hfe).
by rewrite hmem.
Qed.

Lemma odiff_path (p : seq G) (u : G) (X : {set edge G}) :
  path (ores X) u p -> uniq (u :: p) ->
  exists X', forall v, odiff X' v = odiff X v + (v == u)%:R - (v == last u p)%:R.
Proof.
elim: p u X => [|w p IH] u X /=.
  by move=> _ _; exists X => v; rewrite addrK.
case/andP => huw hp; case/andP => hu hup.
have [e [he hpres]] := odiff_step huw.
have hp' : path (ores (otoggle X e)) w p.
  apply: (@sub_in_path _ [pred x | x != u] (ores X)) hp.
    by move=> a' b' ha hb; exact: hpres.
  by apply/allP => x hx; apply/eqP => xu; move: hu; rewrite -xu hx.
have [X' hX'] := IH w (otoggle X e) hp' hup.
by exists X' => v; rewrite hX' he subrK.
Qed.

Lemma odiff_sum (X : {set edge G}) : \sum_v odiff X v = 0.
Proof.
have hcnt : forall f : edge G -> G,
    \sum_v (#|[set e in X | f e == v]|%:R : int) = #|X|%:R.
  move=> f; transitivity (\sum_e (if e \in X then (1 : int) else 0)).
    rewrite (partition_big f xpredT) //=; apply: eq_bigr => v _.
    by rewrite -sum_indz; exact: eq_bigl.
  rewrite (sum_indz X xpredT); congr (_%:R).
  by apply: eq_card => e; rewrite !inE andbT.
by rewrite /odiff sumrB !hcnt subrr.
Qed.

Lemma odiff_sum_set (X : {set edge G}) (S : {set G}) :
  \sum_(v in S) odiff X v
  = #|[set e in X | ohead o e \in S]|%:R - #|[set e in X | otail o e \in S]|%:R.
Proof.
have hcnt : forall f : edge G -> G, \sum_(v in S) (#|[set e in X | f e == v]|%:R : int)
                                    = #|[set e in X | f e \in S]|%:R.
  move=> f; rewrite -sum_indz (partition_big f (mem S)) //=.
  apply: eq_bigr => v hv; rewrite -sum_indz; apply: eq_bigl => e.
  by case: (f e =P v) => [->|]; rewrite ?hv ?andbF.
by rewrite /odiff sumrB !hcnt.
Qed.

Lemma imbalance_odiff (v : G) : imbalance o v = odiff [set: edge G] v.
Proof.
by rewrite /imbalance /odiff; congr (_%:R - _%:R); apply: eq_card => e; rewrite !inE.
Qed.

(** No residual step leaves [S]: then [S] receives exactly its entering
    edges, all of them in [X]. *)
Lemma odiff_closed (X : {set edge G}) (S : {set G}) :
  (forall a b, a \in S -> ores X a b -> b \in S) ->
  \sum_(v in S) odiff X v
  = #|[set e | (ohead o e \in S) && (otail o e \notin S)]|%:R.
Proof.
move=> hcl; rewrite odiff_sum_set.
(* An edge of [X] leaving [S] is a residual step out of [S]; an edge outside
   [X] entering [S] is one too. *)
have hB : [set e in X | otail o e \in S] \subset [set e in X | ohead o e \in S].
  apply/subsetP => e; rewrite !inE => /andP[hX ht]; rewrite hX /=.
  by apply: (hcl _ _ ht); apply/existsP; exists e; rewrite hX !eqxx orbT.
have hD : [set e in X | ohead o e \in S] :\: [set e in X | otail o e \in S]
        = [set e | (ohead o e \in S) && (otail o e \notin S)].
  apply/setP => e; rewrite !inE; case hX: (e \in X) => /=; first by rewrite andbC.
  case hh: (ohead o e \in S) => //=.
  by rewrite (hcl _ _ hh) //; apply/existsP; exists e; rewrite hX !eqxx.
rewrite -hD -[in LHS](cardsID [set e in X | otail o e \in S]
                              [set e in X | ohead o e \in S]).
by rewrite (setIidPr hB) natrD addrC addKr.
Qed.

Lemma imbalance_cut (S : {set G}) :
  \sum_(v in S) imbalance o v
  = #|[set e | (ohead o e \in S) && (otail o e \notin S)]|%:R
    - #|[set e | (otail o e \in S) && (ohead o e \notin S)]|%:R.
Proof.
rewrite (eq_bigr _ (fun v _ => imbalance_odiff v)) odiff_sum_set.
(* Split the edges with one end in [S] by where the other end lies. *)
have hsplit : forall f g : edge G -> G,
    #|[set e in [set: edge G] | f e \in S]|
    = (#|[set e | (f e \in S) && (g e \notin S)]|
       + #|[set e | (f e \in S) && (g e \in S)]|)%N.
  move=> f g.
  rewrite -(cardsID [set e | g e \in S] [set e in [set: edge G] | f e \in S]).
  rewrite addnC; congr (_ + _); apply: eq_card => e; rewrite !inE.
    by case: (f e \in S); case: (g e \in S).
  by case: (f e \in S); case: (g e \in S).
rewrite (hsplit (ohead o) (otail o)) (hsplit (otail o) (ohead o)) !natrD.
rewrite (_ : #|[set e | otail o e \in S & ohead o e \in S]|
           = #|[set e | ohead o e \in S & otail o e \in S]|); last first.
  by apply: eq_card => e; rewrite !inE andbC.
by rewrite opprD addrACA subrr addr0.
Qed.

Lemma absz_addr1_lt (x : int) : x < 0 -> (absz (x + 1)%R < absz x)%N.
Proof.
case: x => // n _; rewrite NegzE abszN.
by rewrite -[n.+1]addn1 PoszD opprD subrK abszN /= addn1.
Qed.

Lemma absz_subr1_lt (x : int) : 0 < x -> (absz (x - 1)%R < absz x)%N.
Proof.
by case: x => [[|n]|n] //= _; rewrite subn1.
Qed.

(** The demands [q] with [imbalance o = m * q] are met by some edge set. *)
Lemma odiff_demand (m : nat) (q : G -> int) :
  (0 < m)%N -> (forall v, imbalance o v = m%:R * q v) ->
  exists X : {set edge G}, forall v, odiff X v = q v.
Proof.
(* Minimise [phi X], the total deviation from the demands.  If some vertex
   [v0] has a deficit, either a residual path from [v0] reaches a vertex with
   a surplus (toggle it: [phi] decreases), or the set [S] that residual paths
   from [v0] reach is closed, and the deviation over [S] is negative by
   choice of [v0] yet non-negative by the cut count. *)
move=> hm hq.
pose r X v := odiff X v - q v.
pose phi X := (\sum_v absz (r X v))%N.
have hq0 : \sum_v q v = 0.
  apply: (mulfI (_ : (m%:R : int) != 0)); first by rewrite pnatr_eq0 -lt0n.
  rewrite mulr0 mulr_sumr (eq_bigr _ (fun v _ => esym (hq v))).
  by rewrite (eq_bigr _ (fun v _ => imbalance_odiff v)); exact: odiff_sum.
have hr0 : forall X, \sum_v r X v = 0.
  by move=> X; rewrite sumrB odiff_sum hq0 subrr.
have done0 : forall X, phi X = 0%N -> exists X', forall v, odiff X' v = q v.
  move=> X h0; exists X => v; apply/eqP; rewrite -subr_eq0 -absz_eq0.
  by rewrite -leqn0 -h0 /phi (bigD1 v) //=; exact: leq_addr.
suff hind : forall n X, (phi X <= n)%N -> exists X', forall v, odiff X' v = q v.
  exact: (hind _ set0 (leqnn _)).
elim=> [|n IH] X hX.
  by apply: done0; apply/eqP; rewrite -leqn0; exact: hX.
case: (eqVneq (phi X) 0%N) => [/done0 //|hne].
suff [X' hlt] : exists X', (phi X' < phi X)%N.
  by apply: (IH X'); rewrite -ltnS (leq_trans hlt hX).
have [v0 hv0] : exists v0, r X v0 < 0.
  case: (pickP (fun v => r X v < 0)) => [v0 hv0|hall]; first by exists v0.
  have hge : forall v, 0 <= r X v.
    by move=> v; rewrite mathcomp.order.order.Order.TotalTheory.leNgt hall.
  have hz := psumr_eq0P (fun v _ => hge v) (hr0 X).
  by exfalso; move/eqP: hne; apply; apply: big1 => v _; rewrite hz.
pose S := [set w | connect (ores X) v0 w].
case: (pickP (fun w => (w \in S) && (0 < r X w))) => [w /andP[hwS hw]|hnone].
  rewrite inE in hwS; case/connectP: hwS => p hp hwl; rewrite hwl in hw.
  move: hw; case: (shortenP hp) => p' hp' hu _ hw.
  have [X' hX'] := odiff_path hp' hu.
  set w' := last v0 p' in hw hX'.
  have hneq : (w' == v0) = false.
    apply/eqP => e; move: hw; rewrite e => h.
    have := mathcomp.order.order.Order.POrderTheory.lt_trans hv0 h.
    by rewrite mathcomp.order.order.Order.POrderTheory.ltxx.
  have hr' : forall v, r X' v = r X v + (v == v0)%:R - (v == w')%:R.
    by move=> v; rewrite /r hX' addrAC; congr (_ - _); rewrite addrAC.
  exists X'.
  rewrite /phi (bigD1 v0) //= [X in (_ < X)%N](bigD1 v0) //=.
  rewrite -addSn; apply: leq_add.
    by rewrite hr' eqxx eq_sym hneq subr0; exact: absz_addr1_lt.
  apply: leq_sum => v hv; rewrite hr' (negbTE hv) addr0.
  case: (eqVneq v w') => [hvw|hvw]; last by rewrite subr0.
  by rewrite hvw; apply: ltnW; exact: absz_subr1_lt.
exfalso.
have hcl : forall a b, a \in S -> ores X a b -> b \in S.
  by move=> a b; rewrite !inE => ha hab; exact: connect_trans ha (connect1 hab).
have hS0 : v0 \in S by rewrite inE connect0.
have hle : forall v, v \in S -> r X v <= 0.
  move=> v hv; move: (hnone v); rewrite /= hv /= => /negbT.
  by rewrite -mathcomp.order.order.Order.TotalTheory.leNgt.
have hneg : \sum_(v in S) r X v < 0.
  rewrite (bigD1 v0) //=.
  have hrest : \sum_(v in S | v != v0) r X v <= 0.
    by apply: sumr_le0 => v /andP[hv _]; exact: hle.
  by rewrite -(addr0 0) ltr_leD.
have hm' : (0 : int) < m%:R by rewrite ltr0n.
have hpos : 0 <= \sum_(v in S) r X v.
  rewrite -(pmulr_rge0 _ hm') /r sumrB mulrBr.
  have hsq : m%:R * \sum_(i in S) q i = \sum_(i in S) imbalance o i.
    by rewrite mulr_sumr; apply: eq_bigr => v _; rewrite hq.
  rewrite hsq imbalance_cut (odiff_closed hcl) opprB addrA -natrM.
  rewrite -natrD -natrB ?ler0n //.
  exact: leq_trans (leq_pmull _ hm) (leq_addr _ _).
by move: hneg; rewrite mathcomp.order.order.Order.TotalTheory.ltNge hpos.
Qed.

(** The demands [q] are met by some edge set as soon as they sum to zero and no
    set [S] demands more than the number of edges entering it. *)
Lemma odiff_demand_cut (q : G -> int) :
  \sum_v q v = 0 ->
  (forall S : {set G},
     \sum_(v in S) q v <= #|[set e | (ohead o e \in S) && (otail o e \notin S)]|%:R) ->
  exists X : {set edge G}, forall v, odiff X v = q v.
Proof.
(* As for [odiff_demand]: minimise the total deviation [phi X].  A deficit
   vertex either reaches a surplus by a residual path (toggle it), or the set
   [S] it reaches is closed; then [S] receives exactly its entering edges
   ([odiff_closed]), which the cut condition makes at least [\sum_S q], while
   the deviation over [S] is negative. *)
move=> hq0 hcut.
pose r X v := odiff X v - q v.
pose phi X := (\sum_v absz (r X v))%N.
have hr0 : forall X, \sum_v r X v = 0.
  by move=> X; rewrite sumrB odiff_sum hq0 subrr.
have done0 : forall X, phi X = 0%N -> exists X', forall v, odiff X' v = q v.
  move=> X h0; exists X => v; apply/eqP; rewrite -subr_eq0 -absz_eq0.
  by rewrite -leqn0 -h0 /phi (bigD1 v) //=; exact: leq_addr.
suff hind : forall n X, (phi X <= n)%N -> exists X', forall v, odiff X' v = q v.
  exact: (hind _ set0 (leqnn _)).
elim=> [|n IH] X hX.
  by apply: done0; apply/eqP; rewrite -leqn0; exact: hX.
case: (eqVneq (phi X) 0%N) => [/done0 //|hne].
suff [X' hlt] : exists X', (phi X' < phi X)%N.
  by apply: (IH X'); rewrite -ltnS (leq_trans hlt hX).
have [v0 hv0] : exists v0, r X v0 < 0.
  case: (pickP (fun v => r X v < 0)) => [v0 hv0|hall]; first by exists v0.
  have hge : forall v, 0 <= r X v.
    by move=> v; rewrite mathcomp.order.order.Order.TotalTheory.leNgt hall.
  have hz := psumr_eq0P (fun v _ => hge v) (hr0 X).
  by exfalso; move/eqP: hne; apply; apply: big1 => v _; rewrite hz.
pose S := [set w | connect (ores X) v0 w].
case: (pickP (fun w => (w \in S) && (0 < r X w))) => [w /andP[hwS hw]|hnone].
  rewrite inE in hwS; case/connectP: hwS => p hp hwl; rewrite hwl in hw.
  move: hw; case: (shortenP hp) => p' hp' hu _ hw.
  have [X' hX'] := odiff_path hp' hu.
  set w' := last v0 p' in hw hX'.
  have hneq : (w' == v0) = false.
    apply/eqP => e; move: hw; rewrite e => h.
    have := mathcomp.order.order.Order.POrderTheory.lt_trans hv0 h.
    by rewrite mathcomp.order.order.Order.POrderTheory.ltxx.
  have hr' : forall v, r X' v = r X v + (v == v0)%:R - (v == w')%:R.
    by move=> v; rewrite /r hX' addrAC; congr (_ - _); rewrite addrAC.
  exists X'.
  rewrite /phi (bigD1 v0) //= [X in (_ < X)%N](bigD1 v0) //=.
  rewrite -addSn; apply: leq_add.
    by rewrite hr' eqxx eq_sym hneq subr0; exact: absz_addr1_lt.
  apply: leq_sum => v hv; rewrite hr' (negbTE hv) addr0.
  case: (eqVneq v w') => [hvw|hvw]; last by rewrite subr0.
  by rewrite hvw; apply: ltnW; exact: absz_subr1_lt.
exfalso.
have hcl : forall a b, a \in S -> ores X a b -> b \in S.
  by move=> a b; rewrite !inE => ha hab; exact: connect_trans ha (connect1 hab).
have hS0 : v0 \in S by rewrite inE connect0.
have hle : forall v, v \in S -> r X v <= 0.
  move=> v hv; move: (hnone v); rewrite /= hv /= => /negbT.
  by rewrite -mathcomp.order.order.Order.TotalTheory.leNgt.
have hneg : \sum_(v in S) r X v < 0.
  rewrite (bigD1 v0) //=.
  have hrest : \sum_(v in S | v != v0) r X v <= 0.
    by apply: sumr_le0 => v /andP[hv _]; exact: hle.
  by rewrite -(addr0 0) ltr_leD.
have hpos : 0 <= \sum_(v in S) r X v.
  by rewrite /r sumrB (odiff_closed hcl) subr_ge0; exact: hcut.
by move: hneg; rewrite mathcomp.order.order.Order.TotalTheory.ltNge hpos.
Qed.

(** An orientation in which no set has more than twice as many edges leaving as entering carries a
    nowhere-zero 3-flow: the demands [- imbalance o] meet the cut condition, so some [X] meets them
    ([odiff_demand_cut]), and [1 + [e in X]] along [o] is conservative. *)
Lemma cut_orientation_flow3 :
  (forall S : {set G},
     (#|[set e | (otail o e \in S) && (ohead o e \notin S)]|
      <= 2 * #|[set e | (ohead o e \in S) && (otail o e \notin S)]|)%N) ->
  has_nz_kflow G 3.
Proof.
move=> hcut.
have hq0 : \sum_v (- imbalance o v) = 0.
  by rewrite sumrN (eq_bigr _ (fun v _ => imbalance_odiff v)) odiff_sum oppr0.
(* [\sum_S - imbalance] is the number of edges leaving [S] minus those entering it. *)
have hqcut : forall S : {set G}, \sum_(v in S) (- imbalance o v)
    <= #|[set e | (ohead o e \in S) && (otail o e \notin S)]|%:R.
  move=> S; rewrite sumrN imbalance_cut opprB lerBlDr -natrD ler_nat.
  by rewrite addnn -mul2n; exact: hcut.
have [X hX] := odiff_demand_cut hq0 hqcut.
(* Along [o], the value is [1] off [X] and [2] on [X]. *)
pose a e : int := 1 + (e \in X)%:R.
exists (fun e => if o e then a e else - a e); split.
  move=> v; apply/eqP; rewrite -subr_eq0.
  have hc : forall (C : {set edge G}) (P : pred (edge G)),
      \sum_e ((e \in C) && P e)%:R = #|[set e in C | P e]|%:R :> int.
    move=> C P; rewrite -sum_indz [RHS]big_mkcond; apply: eq_bigr => e _.
    by case: (P e); case: (e \in C).
  have hc' : forall P : pred (edge G),
      \sum_e (P e)%:R = #|[set e | P e]|%:R :> int.
    move=> P; rewrite -(_ : [set e in [set: edge G] | P e] = [set e | P e]);
      last by apply/setP => e; rewrite !inE.
    by rewrite -hc; apply: eq_bigr => e _; rewrite in_setT.
  rewrite (big_mkcond (fun e => source e == v)).
  rewrite (big_mkcond (fun e => target e == v)) -sumrB.
  rewrite (eq_bigr (fun e => ((otail o e == v)%:R - (ohead o e == v)%:R)
    + (((e \in X) && (otail o e == v))%:R
       - ((e \in X) && (ohead o e == v))%:R))); last first.
    move=> e _.
    have h1 : forall (b : bool) (x : int), (if b then x else 0) = x * b%:R.
      by move=> [] x; rewrite ?mulr1 ?mulr0.
    have h2 : (if o e then a e else - a e)
                * ((source e == v)%:R - (target e == v)%:R)
              = a e * ((otail o e == v)%:R - (ohead o e == v)%:R).
      by rewrite /otail /ohead; case: (o e); rewrite // mulNr -mulrN opprB.
    have h3 : forall b1 b2 : bool, ((b1 && b2)%:R : int) = b1%:R * b2%:R.
      by move=> [] []; rewrite ?mulr1 ?mulr0.
    by rewrite !h1 -mulrBr h2 !h3 -mulrBr /a mulrDl mul1r.
  rewrite big_split /= !sumrB !hc !hc'.
  have e1 : (#|[set e | otail o e == v]|%:R
             - #|[set e | ohead o e == v]|%:R : int) = - imbalance o v.
    by rewrite /imbalance opprB.
  have e2 : (#|[set e in X | otail o e == v]|%:R
             - #|[set e in X | ohead o e == v]|%:R : int) = imbalance o v.
    by rewrite -[RHS]opprK -(hX v) /odiff opprB.
  by rewrite e1 e2 addNr.
move=> e /=.
have -> : `|if o e then a e else - a e| = `|a e| by case: (o e); rewrite ?normrN.
by rewrite /a; case: (e \in X) => /=; rewrite ?addr0 ?normr1 //; split.
Qed.


End ModOrient.

Theorem modular_orientation_to_flow : external_modular_orientation_to_flow_statement.
Proof.
move=> k G hk [o ho].
pose m := (2 * k + 1)%N.
have [q hq] : exists q : G -> int, forall v, imbalance o v = m%:R * q v.
  have ho' : forall v, exists q : int, imbalance o v == m%:R * q.
    by move=> v; have [q hq] := ho v; exists q; apply/eqP.
  by exists (fun v => xchoose (ho' v)) => v; apply/eqP; exact: (xchooseP (ho' v)).
have hm : (0 < m)%N by rewrite /m addn1.
have [X hX] := odiff_demand hm hq.
(* Along [o], the value is [1] off [X] and [1 - m] on [X]. *)
pose a e : int := 1 - m%:R * (e \in X)%:R.
exists (fun e => if o e then a e else - a e); split.
  move=> v; apply/eqP; rewrite -subr_eq0.
  have hc : forall (C : {set edge G}) (P : pred (edge G)),
      \sum_e ((e \in C) && P e)%:R = #|[set e in C | P e]|%:R :> int.
    move=> C P; rewrite -sum_indz [RHS]big_mkcond; apply: eq_bigr => e _.
    by case: (P e); case: (e \in C).
  have hc' : forall P : pred (edge G),
      \sum_e (P e)%:R = #|[set e | P e]|%:R :> int.
    move=> P; rewrite -(_ : [set e in [set: edge G] | P e] = [set e | P e]);
      last by apply/setP => e; rewrite !inE.
    by rewrite -hc; apply: eq_bigr => e _; rewrite in_setT.
  rewrite (big_mkcond (fun e => source e == v)).
  rewrite (big_mkcond (fun e => target e == v)) -sumrB.
  rewrite (eq_bigr (fun e => ((otail o e == v)%:R - (ohead o e == v)%:R)
    - m%:R * (((e \in X) && (otail o e == v))%:R
              - ((e \in X) && (ohead o e == v))%:R))); last first.
    move=> e _.
    have h1 : forall (b : bool) (x : int), (if b then x else 0) = x * b%:R.
      by move=> [] x; rewrite ?mulr1 ?mulr0.
    have h2 : (if o e then a e else - a e)
                * ((source e == v)%:R - (target e == v)%:R)
              = a e * ((otail o e == v)%:R - (ohead o e == v)%:R).
      by rewrite /otail /ohead; case: (o e); rewrite // mulNr -mulrN opprB.
    have h3 : forall b1 b2 : bool, ((b1 && b2)%:R : int) = b1%:R * b2%:R.
      by move=> [] []; rewrite ?mulr1 ?mulr0.
    by rewrite !h1 -mulrBr h2 !h3 -mulrBr /a mulrBl mul1r -mulrA.
  rewrite sumrB -mulr_sumr !sumrB !hc !hc'.
  have e1 : (#|[set e | otail o e == v]|%:R
             - #|[set e | ohead o e == v]|%:R : int) = - (m%:R * q v).
    by rewrite -hq /imbalance opprB.
  have e2 : (#|[set e in X | otail o e == v]|%:R
             - #|[set e in X | ohead o e == v]|%:R : int) = - q v.
    by rewrite -(hX v) /odiff opprB.
  by rewrite e1 e2 mulrN opprK addNr.
move=> e; rewrite addn1 /=.
have -> : `|if o e then a e else - a e| = `|a e|.
  by case: (o e); rewrite ?normrN.
rewrite /a /m; case: (e \in X) => /=.
  rewrite mulr1 addn1 -natr1 opprD addrCA subrr addr0 normrN normr_nat.
  by split => //; rewrite ler1n muln_gt0.
by rewrite mulr0 subr0 normr1; split => //; rewrite ler1n muln_gt0.
Qed.


(*@EDGE from=jaegers_modular_orientation_statement to=three_flow_statement kind=implies status=verified proof=unconditional_jaegers_modular_orientation_implies_three_flow cite="Jaeger, Nowhere-zero flow problems, Selected Topics in Graph Theory 3 (1988) 71-95; Tutte 1954 (3-flow conjecture and orientation/flow duality)" note="Jaeger's modular-orientation conjecture at k=1 (4*1=4 edge-connected, 2*1+1=3) is Tutte's 3-flow conjecture; the mod-3 orientation is converted to a nowhere-zero 3-flow by the orientation/flow duality, proved as modular_orientation_to_flow: along the orientation put 1 off an edge set X and 1-m on X, where X meets the demands imbalance/m (found by augmenting paths)" *)
Theorem unconditional_jaegers_modular_orientation_implies_three_flow :
  jaegers_modular_orientation_statement -> three_flow_statement.
Proof.
exact: jaegers_modular_orientation_implies_three_flow modular_orientation_to_flow.
Qed.

(** ================================================================= *)
(** ** gc:e184: the direction of Steffen's equivalence used by Row 1 => Tutte's
       3-flow (classical-lemmas TODO 5)

    No reduction of Kochol, no splitting of Mader and no attainment of the
    circular flow number: the premise is used at one graph and one rational.
    - The doubled inflation [inf2G G] (implications_U6's [infG] with every
      cycle edge doubled) is 5-regular ([inf2_mdeg]).  A set that splits the
      ends of a vertex cuts its doubled cycle in at least four edges
      ([inf2_cut_split]); a union of whole vertex classes cuts the copies of a
      cut of [G] ([inf2_cut_union]), which [edge_connected G 4] makes at least
      four when the union is odd ([inf2_union_proper], [edge_connected_cut]).
      An odd set of a 5-regular multigraph has an odd cut, so [inf2G G] is a
      5-graph ([inf2_2t1]).
    - The premise at [r = 3 + 1/(m+1)] gives a nowhere-zero rational flow;
      along its signs no set has more than twice as many edges leaving as
      entering ([rflow_cut_orientation]), and [odiff_demand_cut] turns that
      orientation into an integer flow with values 1 and 2
      ([cut_orientation_flow3]).
    - Contracting the cycles keeps a flow on the copies of the edges of [G]
      ([inf2_contract_flow]). *)

(* [implications_U6] is only Required (see the header): its inflation lemmas
   are used through these abbreviations. *)
Local Notation inf_end := implications_U6.inf_end.
Local Notation inf_nxt := implications_U6.inf_nxt.
Local Notation inf_prv := implications_U6.inf_prv.
Local Notation inf_end_nxt := implications_U6.inf_end_nxt.
Local Notation inf_prv_nxt := implications_U6.inf_prv_nxt.
Local Notation inf_nxt_prv := implications_U6.inf_nxt_prv.
Local Notation inf_reach := implications_U6.inf_reach.

(** A [k]-edge-connected multigraph has at least [k] edges across every cut that separates two vertices:
    deleting the cut would leave a walk between them, which [uwalk_crosses] makes cross it. *)
Lemma edge_connected_cut (G0 : mgraph) (k : nat) (S : {set G0}) (x y : G0) :
  edge_connected G0 k -> x \in S -> y \notin S -> (k <= #|cut S|)%N.
Proof.
move=> hk hx hy; rewrite leqNgt; apply/negP => hlt.
have [w [hw hall]] := hk (cut S) hlt x y.
have hxy : (x \in S) != (y \in S) by rewrite hx (negbTE hy).
have [f hfw hfc] := uwalk_crosses hw hxy.
by move: (allP hall f hfw); rewrite hfc.
Qed.

(** Along an orbit of [f], a predicate that holds at the start and fails later is left at some step. *)
Lemma iter_cross (T : Type) (f : T -> T) (P : pred T) (z : T) (n : nat) :
  P z -> ~~ P (iter n f z) -> exists i, P (iter i f z) && ~~ P (iter i.+1 f z).
Proof.
move=> hz; elim: n => [|n IH] /=; first by rewrite hz.
case hn: (P (iter n f z)).
  by move=> hn1; exists n; rewrite hn hn1.
by move=> _; apply: IH; rewrite hn.
Qed.

Section Inflate2.
Variable G : mgraph.

(** The doubled inflation: [inl e] joins the two ends of [e]; [inr (a, c)], for
    [c : bool], joins [a] to the next end at the same vertex, so every cycle
    edge of [infG] comes twice. *)
Definition inf2_endpoint (b : bool) (f : edge G + ((edge G * bool) * bool))
    : edge G * bool :=
  match f with
  | inl e => (e, b)
  | inr ac => if b then inf_nxt ac.1 else ac.1
  end.

Definition inf2G : mgraph :=
  @Graph unit unit (edge G * bool)%type (edge G + ((edge G * bool) * bool))%type
    inf2_endpoint (fun _ => tt) (fun _ => tt).

(** Each end [a] is the [b]-end of one copy when [a.2 = b], and of two cycle
    edges: [inr (a, _)] for [b = false], [inr (inf_prv a, _)] for [b = true]. *)
Lemma inf2_ends_at (b : bool) (a : inf2G) :
  #|ends_at [set: edge inf2G] b a| = ((a.2 == b) + 2)%N.
Proof.
set x0 := if b then inf_prv a else a.
have hP : forall f : edge inf2G, (f \in ends_at [set: edge inf2G] b a)
    = match f with inl e => (e == a.1) && (a.2 == b) | inr p => p.1 == x0 end.
  move=> -[e|[x c]]; rewrite !inE /= /inf2_endpoint /=.
    by case: a {x0} => e' b'; rewrite xpair_eqE /= eq_sym [b == _]eq_sym.
  rewrite /x0; case: b {x0} => //=.
  by apply/eqP/eqP => [<-|->]; [rewrite inf_prv_nxt | rewrite inf_nxt_prv].
have hS : ends_at [set: edge inf2G] b a
    = (@inl (edge G) ((edge G * bool) * bool) @: [set e : edge G | (e == a.1) && (a.2 == b)])
      :|: (@inr (edge G) ((edge G * bool) * bool) @: [set (x0, false); (x0, true)]).
  apply/setP => f; rewrite hP inE; case: f => [e|p].
    rewrite (mem_imset _ _ (@inl_inj _ _)) inE orbC.
    by case: imsetP => // -[y _].
  rewrite orbC (mem_imset _ _ (@inr_inj _ _)) !inE.
  case: imsetP => [[y _]|] //=.
  move=> _; case: p => x c /=; rewrite orbF !xpair_eqE; case: c; rewrite ?andbT ?andbF ?orbF //.
rewrite hS cardsU (_ : _ :&: _ = set0); last first.
  apply/setP => f; rewrite !inE; apply/negP => /andP[/imsetP[y _ ->] /imsetP[z _]] //.
rewrite cards0 subn0 !card_imset; try by [exact: inl_inj | exact: inr_inj].
rewrite cards2 xpair_eqE eqxx /=; congr (_ + _)%N.
case: (a.2 == b).
  by rewrite (_ : [set e | e == a.1 & true] = [set a.1]) ?cards1 //; apply/setP => x; rewrite !inE andbT.
by rewrite (_ : [set e | e == a.1 & false] = set0) ?cards0 //; apply/setP => x; rewrite !inE andbF.
Qed.

Lemma inf2_mdeg (a : inf2G) : mdeg a = 5%N.
Proof. by rewrite /mdeg /subdeg !inf2_ends_at; case: a => e []. Qed.

Lemma inf2_card : #|inf2G| = (2 * #|edge G|)%N.
Proof. by rewrite card_prod card_bool mulnC. Qed.

(** A set that splits the ends of one vertex cuts its doubled cycle twice: at least four edges. *)
Lemma inf2_cut_split (X : {set inf2G}) (a b : inf2G) :
  a \in X -> b \notin X -> inf_end b = inf_end a -> (4 <= #|cut X|)%N.
Proof.
move=> ha hb hab.
have [n hn] := inf_reach hab.
have hbn : ~~ ((iter n (@inf_nxt G) a : inf2G) \in X) by rewrite hn.
have [i /andP[hi hi1]] := @iter_cross _ (@inf_nxt G) (fun x : inf2G => x \in X) a n ha hbn.
have [n' hn'] := inf_reach (esym hab).
have han : ~~ ~~ ((iter n' (@inf_nxt G) b : inf2G) \in X) by rewrite hn' ha.
have [j /andP[hj hj1]] := @iter_cross _ (@inf_nxt G) (fun x : inf2G => x \notin X) b n' hb han.
move: hi1 hj1 => /= hi1 hj1; rewrite negbK in hj1.
set x1 := iter i (@inf_nxt G) a in hi hi1.
set x2 := iter j (@inf_nxt G) b in hj hj1.
(* Each crossing step of the walk round the cycle is a pair of parallel cut edges. *)
have hc : forall (x : edge G * bool) (c : bool),
    ((x : inf2G) \in X) != ((@inf_nxt G x : inf2G) \in X) -> (inr (x, c) : edge inf2G) \in cut X.
  by move=> x c h; rewrite inE /source /target /=; case: (x \in X) h; case: (inf_nxt x \in X).
pose E4 : {set edge inf2G} := [set (inr (x1, c) : edge inf2G) | c in [set: bool]]
                              :|: [set (inr (x2, c) : edge inf2G) | c in [set: bool]].
have hsub : E4 \subset cut X.
  apply/subsetP => f; rewrite inE => /orP[] /imsetP[c _ ->]; apply: hc.
    by rewrite hi hi1.
  by rewrite (negbTE hj) hj1.
have hx12 : x1 != x2 by apply: contraNneq hj => <-.
have hcard : #|E4| = 4%N.
  rewrite cardsU (_ : _ :&: _ = set0) ?cards0 ?subn0; last first.
    apply/setP => f; rewrite !inE; apply/negP => /andP[/imsetP[c _ ->] /imsetP[d _ [h _]]].
    by move: hx12; rewrite h eqxx.
  by rewrite !card_imset ?cardsT ?card_bool // => c d [].
by apply: leq_trans (subset_leq_card hsub); rewrite hcard.
Qed.

(** A union of whole vertex classes cuts exactly the copies of the edges of the cut of [G]. *)
Lemma inf2_cut_union (S : {set G}) :
  #|cut [set a : inf2G | inf_end a \in S]| = #|cut S|.
Proof.
have hinj : injective (fun e : edge G => (inl e : edge inf2G)) by move=> x y [].
rewrite -(card_imset (cut S) hinj); apply: eq_card => f.
case: f => [e|[x c]].
  rewrite (mem_imset _ _ hinj) !inE /source /target /=.
  by rewrite /inf_end /=.
(* A cycle edge has both ends at the same vertex of [G]. *)
rewrite !inE /source /target /= inf_end_nxt addbb; apply/esym/negbTE/imsetP => -[y _] //.
Qed.

(** An odd union of whole vertex classes comes from a proper nonempty vertex set of [G]. *)
Lemma inf2_union_proper (S : {set G}) :
  odd #|[set a : inf2G | inf_end a \in S]| -> exists x y, x \in S /\ y \notin S.
Proof.
move=> hodd.
case: (pickP (mem S)) => [x hx|hS0]; last first.
  move: hodd; rewrite (_ : [set a : inf2G | inf_end a \in S] = set0) ?cards0 //.
  by apply/setP => a; rewrite !inE; exact: (hS0 (inf_end a)).
case: (pickP (predC (mem S))) => [y hy|hS1]; first by exists x, y.
(* [S] is every vertex: the union is all ends, an even number ([inf2_card]). *)
move: hodd; rewrite (_ : [set a : inf2G | inf_end a \in S] = setT) ?cardsT ?inf2_card ?oddM //.
apply/setP => a; rewrite !inE; have := hS1 (inf_end a).
by rewrite /= => /negbFE.
Qed.

Lemma inf2_2t1 : edge_connected G 4 -> is_2t1_graph inf2G 2.
Proof.
move=> hk; split; first by move=> a; rewrite inf2_mdeg.
move=> X hX.
(* In a 5-regular multigraph an odd set has an odd cut, so four crossing edges make five. *)
have hpar : odd #|cut X| by rewrite (@reg_cut_parity _ 5 X inf2_mdeg) oddM hX.
suff h4 : (4 <= #|cut X|)%N.
  move: h4; rewrite leq_eqVlt => /orP[/eqP h|//].
  by move: hpar; rewrite -h.
case: (boolP [exists a : inf2G, exists b : inf2G, [&& a \in X, b \notin X & inf_end b == inf_end a]]).
  by case/existsP => a /existsP[b /and3P[ha hb /eqP hab]]; exact: inf2_cut_split ha hb hab.
(* Otherwise [X] is a union of whole vertex classes, of a proper nonempty set of vertices of [G]. *)
move=> hno.
set S := [set v : G | [exists a : inf2G, (a \in X) && (inf_end a == v)]].
have hXS : X = [set a : inf2G | inf_end a \in S].
  apply/setP => a; rewrite !inE; apply/idP/idP => [ha|/existsP[a' /andP[ha' /eqP he]]].
    by apply/existsP; exists a; rewrite ha eqxx.
  apply: contraNT hno => hna; apply/existsP; exists a'; apply/existsP; exists a.
  by rewrite ha' hna he eqxx.
have hodd : odd #|[set a : inf2G | inf_end a \in S]| by rewrite -hXS.
have [x [y [hx hy]]] := @inf2_union_proper S hodd.
by rewrite hXS inf2_cut_union; exact: edge_connected_cut hk hx hy.
Qed.

(** Contracting the cycles: the values on the copies [inl e] form a flow of [G].  Summed over the ends of
    [v], conservation counts every cycle edge of [v] once leaving and once entering, so they cancel. *)
Lemma inf2_contract_flow (k : nat) : has_nz_kflow inf2G k -> has_nz_kflow G k.
Proof.
move=> [phi2 [hcons hbnd]].
exists (fun e => phi2 (inl e)); split; last by move=> e; exact: hbnd.
move=> v.
(* Gather the edges of [inf2G] by the vertex of [G] at their [b]-end. *)
have hside : forall b : bool,
    \sum_(a : inf2G | inf_end a == v) \sum_(f : edge inf2G | endpoint b f == a) phi2 f
    = \sum_(f : edge inf2G | inf_end (endpoint b f) == v) phi2 f.
  move=> b; rewrite [RHS](partition_big (fun f => endpoint b f) (fun a : inf2G => inf_end a == v)) //=.
  apply: eq_bigr => a /eqP ha; apply: eq_bigl => f.
  by case: (inf2_endpoint b f =P a) => [->|]; rewrite ?ha ?eqxx ?andbF ?andbT.
(* The copies give the [b]-side sum of [G]; the cycle edges of [v] give the same sum on both sides. *)
have hsplit : forall b : bool,
    \sum_(f : edge inf2G | inf_end (endpoint b f) == v) phi2 f
    = \sum_(e : edge G | endpoint b e == v) phi2 (inl e)
      + \sum_(p : (edge G * bool) * bool | inf_end p.1 == v) phi2 (inr p).
  move=> b; rewrite big_mkcond big_sumType /=; congr (_ + _).
    by rewrite [RHS]big_mkcond; apply: eq_bigr => e _.
  rewrite [RHS]big_mkcond; apply: eq_bigr => p _.
  by case: b => //=; rewrite inf_end_nxt.
have hc : \sum_(a : inf2G | inf_end a == v) \sum_(f : edge inf2G | endpoint false f == a) phi2 f
        = \sum_(a : inf2G | inf_end a == v) \sum_(f : edge inf2G | endpoint true f == a) phi2 f.
  by apply: eq_bigr => a _; exact: hcons a.
by move: hc; rewrite !hside !hsplit => /addIr.
Qed.

End Inflate2.


(** Rounding: a nowhere-zero rational [r]-flow with [r = 3 + 1/(m+1)], [m] the number of edges, orients
    the edges (along the sign of the flow) so that no set has more than twice as many edges leaving as
    entering.  Over a cut, the absolute values leaving and entering balance; each lies in
    [[1, 2 + 1/(m+1)]], and at most [m] edges enter. *)
Lemma rflow_cut_orientation (H : mgraph) :
  has_nz_rflow H (3%:R + (#|edge H|.+1)%:R^-1) ->
  exists o : edge H -> bool, forall S : {set H},
    (#|[set e | (otail o e \in S) && (ohead o e \notin S)]|
     <= 2 * #|[set e | (ohead o e \in S) && (otail o e \notin S)]|)%N.
Proof.
move=> [phi [hcons hb]].
pose o e := 0 < phi e.
exists o => S.
(* Conservation summed over [S]: the flow on the edges with source in [S] equals the flow on the
   edges with target in [S]. *)
have hend : forall b : bool,
    \sum_(v in S) \sum_(e | endpoint b e == v) phi e = \sum_(e | endpoint b e \in S) phi e.
  move=> b; rewrite [RHS](partition_big (fun e => endpoint b e) (mem S)) //=.
  apply: eq_bigr => v hv; apply: eq_bigl => e.
  by case: (endpoint b e =P v) => [->|]; rewrite ?hv ?andbF ?andbT.
have hST : \sum_(e | source e \in S) phi e = \sum_(e | target e \in S) phi e.
  by rewrite -(hend false) -(hend true); apply: eq_bigr => v _; exact: hcons.
set Out := [set e | otail o e \in S & ohead o e \notin S].
set In := [set e | ohead o e \in S & otail o e \notin S].
(* Along [o], that difference is the absolute flow leaving [S] minus the one entering it. *)
have hpt : forall e, (if source e \in S then phi e else 0) - (if target e \in S then phi e else 0)
    = (if e \in Out then `|phi e| else 0) - (if e \in In then `|phi e| else 0).
  move=> e; rewrite !inE /otail /ohead /o.
  case: (boolP (0 < phi e)) => hp.
    rewrite (gtr0_norm hp).
    by case: (source e \in S); case: (target e \in S); rewrite /= ?subr0 ?sub0r ?subrr.
  rewrite (ler0_norm (_ : phi e <= 0)); last by rewrite order.Order.TotalTheory.leNgt.
  by case: (source e \in S); case: (target e \in S); rewrite /= ?subr0 ?sub0r ?subrr ?opprK.
have hbal : \sum_(e in Out) `|phi e| = \sum_(e in In) `|phi e|.
  apply/eqP; rewrite -subr_eq0 big_mkcond [X in _ - X]big_mkcond -sumrB.
  rewrite -(eq_bigr _ (fun e _ => hpt e)) sumrB -!big_mkcond /=.
  by rewrite hST subrr.
(* Each absolute value lies in [[1, 2 + 1/(m+1)]], and fewer than [m+1] edges enter [S]. *)
set m := #|edge H|.
have hlo : (#|Out|%:R : rat) <= \sum_(e in Out) `|phi e|.
  have -> : (#|Out|%:R : rat) = \sum_(e in Out) 1 by rewrite sumr_const.
  by apply: ler_sum => e _; exact: (hb e).1.
have h31 : (3 : rat) + m.+1%:R^-1 - 1 = 2 + m.+1%:R^-1.
  by rewrite addrAC (_ : (3 : rat) - 1 = 2) //; apply/eqP; rewrite subr_eq.
have hhi : \sum_(e in In) `|phi e| <= #|In|%:R * (2 + m.+1%:R^-1).
  have -> : #|In|%:R * (2 + m.+1%:R^-1) = \sum_(e in In) (2 + m.+1%:R^-1 : rat).
    by rewrite sumr_const mulr_natl.
  by apply: ler_sum => e _; rewrite -h31; exact: (hb e).2.
have hIn : (#|In| < m.+1)%N by rewrite ltnS /m; exact: max_card.
have hfrac : (#|In|%:R : rat) * m.+1%:R^-1 < 1.
  by rewrite ltr_pdivrMr ?ltr0n // mul1r ltr_nat.
have : (#|Out|%:R : rat) < (2 * #|In|).+1%:R.
  apply: (order.Order.POrderTheory.le_lt_trans hlo); rewrite hbal.
  apply: (order.Order.POrderTheory.le_lt_trans hhi).
  have -> : ((2 * #|In|).+1%:R : rat) = #|In|%:R * 2 + 1.
    by rewrite -[(2 * #|In|).+1]addn1 natrD mulnC natrM.
  by rewrite mulrDr ltrD2l.
by rewrite ltr_nat ltnS.
Qed.

(** gc:e184's external, proved: the doubled inflation [inf2G G] of a 4-edge-connected [G] with an edge is a
    5-graph ([inf2_2t1], [inf2_card]); the premise gives it a nowhere-zero [r]-flow for
    [r = 3 + 1/(m+1)], which rounds to an orientation with the cut condition ([rflow_cut_orientation]),
    hence a nowhere-zero 3-flow of [inf2G G] ([cut_orientation_flow3]), which contracts to one of [G]
    ([inf2_contract_flow]). *)
Theorem steffen_3flow_5graphs : external_steffen_3flow_5graphs_statement.
Proof.
move=> Hprem G hE hk.
have hH0 : (0 < #|inf2G G|)%N by rewrite inf2_card muln_gt0.
have hr : (3%:R : rat) < 3%:R + (#|edge (inf2G G)|.+1)%:R^-1.
  by rewrite ltrDl invr_gt0 ltr0n.
have [o ho] := rflow_cut_orientation (Hprem _ hH0 (inf2_2t1 hk) _ hr).
exact: inf2_contract_flow (cut_orientation_flow3 ho).
Qed.

(*@EDGE from=circular_flow_numbers_of_r_graphs_statement to=three_flow_statement kind=implies status=verified proof=unconditional_circular_flow_numbers_of_r_graphs_implies_three_flow cite="gc:e184" note="The t=2 instance of Row 1 is exactly 'every 5-graph has circular flow number at most 2+2/2=3' (cfn_bound_t2); the direction of Steffen's cited equivalence used here is proved as steffen_3flow_5graphs: a 4-edge-connected G inflates (every vertex a doubled cycle through its arc ends) to a 5-graph, whose rational flow at r = 3+1/(m+1) orients the edges so that no set has more than twice as many leaving as entering edges, hence an integer flow with values 1 and 2 (odiff_demand_cut), which contracts to G" *)
Theorem unconditional_circular_flow_numbers_of_r_graphs_implies_three_flow :
  circular_flow_numbers_of_r_graphs_statement -> three_flow_statement.
Proof. exact: circular_flow_numbers_of_r_graphs_implies_three_flow steffen_3flow_5graphs. Qed.

(** ── Audited non-edges (machine-readable; extracted by build_edge_graph.py) ── *)


(*@EDGE from=three_flow_statement to=five_flow_statement kind=implies status=refuted-direction cite="classical: 3-/4-/5-flow conjectures are mutually independent (Jaeger 1979 survey)" note="REFUTED-DIRECTION (metadata wave M, 2026-09-24): classical antichain: 4-edge-connected is a proper subclass of bridgeless and has_nz_kflow_mono runs the wrong way. Earlier note: Antichain: 3-flow's hypothesis (4-edge-connected) is STRICTLY stronger than 5-flow's (bridgeless), so 3-flow covers fewer graphs; the conclusion-monotone has_nz_kflow_mono runs the wrong way to close this. Does not compile." *)
(*@EDGE from=five_flow_statement to=three_flow_statement kind=implies status=refuted-direction cite="classical: 3-/4-/5-flow conjectures are mutually independent" note="REFUTED-DIRECTION (metadata wave M, 2026-09-24): classical antichain: a nowhere-zero 5-flow does not yield a nowhere-zero 3-flow. Earlier note: edge_connected 4 => bridgeless (hypothesis ok) but a nowhere-zero 5-flow does NOT yield a nowhere-zero 3-flow; conclusion implication fails. Does not compile." *)
(*@EDGE from=four_flow_statement to=five_flow_statement kind=implies status=refuted-direction cite="classical antichain" note="REFUTED-DIRECTION (metadata wave M, 2026-09-24): classical antichain (Jaeger 1979 survey): the 3-/4-/5-flow conjectures are mutually independent; corpus e176 is related_only. Earlier note: 4-flow's class (bridgeless, no Petersen minor) is not contained in 5-flow's class (all bridgeless); and nz-4 => nz-5 runs the wrong way against the hypotheses. Does not compile." *)
(*@EDGE from=real_roots_of_the_flow_polynomial_statement to=half_integral_flow_polynomial_values_statement kind=implies status=candidate proved=false cite="gc:e095" note="BLOCKED (E6 audit). Mathematically: for 2-edge-connected G, flow_poly G is monic of degree nullity(E) (S = E is the unique maximiser of nullity when there is no bridge), so it is nonzero; if Phi(11/2) <= 0, the IVT on [11/2, oo) gives a real root >= 11/2 > 4, contradicting Row 13. Missing pieces: (a) NO axiom-free rcfType instance exists in this environment (mathcomp-real-closed, which provides realalg, is not installed; mathcomp-classical reals are axiom-bearing and banned), so Row 13 cannot be instantiated at all -- an external asserting the existence of a real closed field (Cohen 2012, real algebraic numbers) would be needed, or realalg must be formalized; (b) the monic/degree lemma for flow_poly on bridgeless graphs (ncomp monotonicity under edge deletion, ~150 lines over n_comp); (c) the sign argument: rcfType axiom poly_ivt (numfield.v) applied to p - with p.[11/2] <= 0 and p.[x] > 0 for large x (leading term domination bound, ~80 lines), plus the ratr transfer between flow_poly_eval over rat and map_poly into F." *)
(*@EDGE from=real_roots_of_the_flow_polynomial_statement to=five_flow_statement kind=implies status=candidate proved=false cite="gc:e094" note="BLOCKED (E6 audit). Needs everything listed for gc:e095 (existence of an rcfType -- none is available axiom-free here --, flow_poly monic of degree nullity(E) on bridgeless graphs, the IVT sign argument giving flow_poly(5) > 0) PLUS Tutte 1954 counting theorem F28 (the number of nowhere-zero Z_k-flows equals Phi(G,k)) AND Tutte integer/Z_k flow equivalence (a nowhere-zero Z_5-flow yields a nowhere-zero integer 5-flow): D1 defines flow_poly as the alternating subset sum, not by counting, so neither identity is available; both are genuine multi-hundred-line developments or two further externals. Also the target quantifies over possibly disconnected bridgeless G while Row 13 needs flow_poly G != 0, which again comes from (b)." *)

(** ** Axiom audit (gc:e246) *)

Print Assumptions orientable_five_cycle_double_cover_implies_five_flow.

(** ** Axiom audit (gc:e096) *)

Print Assumptions unconditional_circular_flow_numbers_of_r_graphs_implies_circular_flow_number_of_regular_class_1_graphs.

(** ** Axiom audit (gc:e093) *)

Print Assumptions modular_orientation_to_flow.
Print Assumptions unconditional_jaegers_modular_orientation_implies_three_flow.

(** ** Axiom audit (gc:e184) *)

Print Assumptions steffen_3flow_5graphs.
Print Assumptions unconditional_circular_flow_numbers_of_r_graphs_implies_three_flow.
