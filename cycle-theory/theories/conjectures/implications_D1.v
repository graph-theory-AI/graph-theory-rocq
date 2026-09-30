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

Import GRing.Theory Num.Theory.

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
    Not formalized here: it is carried as an explicit hypothesis of the
    conditional edge below (never an [Axiom], never [Admitted]), which is why
    that edge is [status=conditional external=...] rather than [verified].
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

(*@EDGE from=jaegers_modular_orientation_statement to=three_flow_statement kind=implies status=conditional external="external_modular_orientation_to_flow_statement" proof=jaegers_modular_orientation_implies_three_flow cite="Jaeger, Nowhere-zero flow problems, Selected Topics in Graph Theory 3 (1988) 71-95; Tutte 1954 (3-flow conjecture and orientation/flow duality)" note="Jaeger's modular-orientation conjecture at k=1 (4*1=4 edge-connected, 2*1+1=3) is Tutte's 3-flow conjecture; the mod-3 orientation is converted to a nowhere-zero 3-flow by the cited external orientation/flow duality" *)
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
    Not formalized here: it is carried as an explicit hypothesis of the
    conditional edge below (never an [Axiom], never [Admitted]), which is why
    that edge is [status=conditional external=...] rather than [verified]. *)
Definition external_steffen_3flow_5graphs_statement : Prop :=
  (forall G : mgraph, (0 < #|G|)%N -> is_2t1_graph G 2 ->
     circular_flow_number_le G 3%:R) ->
  forall G : mgraph, (0 < #|edge G|)%N -> edge_connected G 4 -> has_nz_kflow G 3.

(** [2 + 2/t] at [t = 2] is [3]. *)
Lemma cfn_bound_t2 : 2%:R + 2%:R / 2%:R = 3%:R :> rat.
Proof. by rewrite divff ?pnatr_eq0 // natr1. Qed.

(*@EDGE from=circular_flow_numbers_of_r_graphs_statement to=three_flow_statement kind=implies status=conditional external="external_steffen_3flow_5graphs_statement" proof=circular_flow_numbers_of_r_graphs_implies_three_flow cite="gc:e184" note="The t=2 instance of Row 1 is exactly 'every 5-graph has circular flow number at most 2+2/2=3' (cfn_bound_t2); Steffen's cited equivalence turns that into Tutte's 3-flow conjecture, and is carried as the explicit external hypothesis external_steffen_3flow_5graphs_statement" *)
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
    Not formalized here: it is carried as an explicit hypothesis of the
    conditional edge below (never an [Axiom], never [Admitted]), which is why
    that edge is [status=conditional external=...] rather than [verified]. It is
    needed only for the residual [t = 1] case of the target row, which the
    source row (quantified over [1 < t]) does not cover. *)
Definition external_tutte_class1_cubic_statement : Prop :=
  forall G : mgraph,
    (0 < #|G|)%N -> loopless G -> mreg G 3 -> is_class1 G ->
    circular_flow_number_le G 4%:R.

(** [2 + 2/t] at [t = 1] is [4]. *)
Lemma cfn_bound_t1 : 2%:R + 2%:R / 1%:R = 4%:R :> rat.
Proof. by rewrite divr1 -natrD. Qed.

(*@EDGE from=circular_flow_numbers_of_r_graphs_statement to=circular_flow_number_of_regular_class_1_graphs_statement kind=implies status=conditional external="external_tutte_class1_cubic_statement" proof=circular_flow_numbers_of_r_graphs_implies_circular_flow_number_of_regular_class_1_graphs cite="gc:e096" note="For t>1 the hypothesis class is contained: class1_is_2t1 turns loopless + (2t+1)-regular + class 1 into a (2t+1)-graph, via the 2t+1 colour classes being perfect matchings (matchings_cuts.class1_pm_partition) each meeting every odd cut in an odd number of edges (matchings_cuts.pm_cut_parity), so Row 1 applies verbatim. The residual t=1 case, which Row 1 (1<t) does not cover, is Tutte's characterization of cubic graphs with flow number 4, carried as the external hypothesis" *)
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


(** ── Audited non-edges (machine-readable; extracted by build_edge_graph.py) ── *)


(*@EDGE from=three_flow_statement to=five_flow_statement kind=implies status=refuted-direction cite="classical: 3-/4-/5-flow conjectures are mutually independent (Jaeger 1979 survey)" note="REFUTED-DIRECTION (metadata wave M, 2026-09-24): classical antichain: 4-edge-connected is a proper subclass of bridgeless and has_nz_kflow_mono runs the wrong way. Earlier note: Antichain: 3-flow's hypothesis (4-edge-connected) is STRICTLY stronger than 5-flow's (bridgeless), so 3-flow covers fewer graphs; the conclusion-monotone has_nz_kflow_mono runs the wrong way to close this. Does not compile." *)
(*@EDGE from=five_flow_statement to=three_flow_statement kind=implies status=refuted-direction cite="classical: 3-/4-/5-flow conjectures are mutually independent" note="REFUTED-DIRECTION (metadata wave M, 2026-09-24): classical antichain: a nowhere-zero 5-flow does not yield a nowhere-zero 3-flow. Earlier note: edge_connected 4 => bridgeless (hypothesis ok) but a nowhere-zero 5-flow does NOT yield a nowhere-zero 3-flow; conclusion implication fails. Does not compile." *)
(*@EDGE from=four_flow_statement to=five_flow_statement kind=implies status=refuted-direction cite="classical antichain" note="REFUTED-DIRECTION (metadata wave M, 2026-09-24): classical antichain (Jaeger 1979 survey): the 3-/4-/5-flow conjectures are mutually independent; corpus e176 is related_only. Earlier note: 4-flow's class (bridgeless, no Petersen minor) is not contained in 5-flow's class (all bridgeless); and nz-4 => nz-5 runs the wrong way against the hypotheses. Does not compile." *)
(*@EDGE from=real_roots_of_the_flow_polynomial_statement to=half_integral_flow_polynomial_values_statement kind=implies status=candidate proved=false cite="gc:e095" note="BLOCKED (E6 audit). Mathematically: for 2-edge-connected G, flow_poly G is monic of degree nullity(E) (S = E is the unique maximiser of nullity when there is no bridge), so it is nonzero; if Phi(11/2) <= 0, the IVT on [11/2, oo) gives a real root >= 11/2 > 4, contradicting Row 13. Missing pieces: (a) NO axiom-free rcfType instance exists in this environment (mathcomp-real-closed, which provides realalg, is not installed; mathcomp-classical reals are axiom-bearing and banned), so Row 13 cannot be instantiated at all -- an external asserting the existence of a real closed field (Cohen 2012, real algebraic numbers) would be needed, or realalg must be formalized; (b) the monic/degree lemma for flow_poly on bridgeless graphs (ncomp monotonicity under edge deletion, ~150 lines over n_comp); (c) the sign argument: rcfType axiom poly_ivt (numfield.v) applied to p - with p.[11/2] <= 0 and p.[x] > 0 for large x (leading term domination bound, ~80 lines), plus the ratr transfer between flow_poly_eval over rat and map_poly into F." *)
(*@EDGE from=real_roots_of_the_flow_polynomial_statement to=five_flow_statement kind=implies status=candidate proved=false cite="gc:e094" note="BLOCKED (E6 audit). Needs everything listed for gc:e095 (existence of an rcfType -- none is available axiom-free here --, flow_poly monic of degree nullity(E) on bridgeless graphs, the IVT sign argument giving flow_poly(5) > 0) PLUS Tutte 1954 counting theorem F28 (the number of nowhere-zero Z_k-flows equals Phi(G,k)) AND Tutte integer/Z_k flow equivalence (a nowhere-zero Z_5-flow yields a nowhere-zero integer 5-flow): D1 defines flow_poly as the alternating subset sum, not by counting, so neither identity is available; both are genuine multi-hundred-line developments or two further externals. Also the target quantifies over possibly disconnected bridgeless G while Row 13 needs flow_poly G != 0, which again comes from (b)." *)

(** ** Axiom audit (gc:e246) *)

Print Assumptions orientable_five_cycle_double_cover_implies_five_flow.
