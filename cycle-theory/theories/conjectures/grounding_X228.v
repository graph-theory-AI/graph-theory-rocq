(** * Cycle.conjectures.grounding_X228 — grounding lemmas for wave X228

    [Qed]-closed, axiom-free sanity results for the flow-pair row of
    [Cycle.conjectures.X228] and for the [x228_kflow] / [x228_half_flow_pair]
    vocabulary it introduces:

      - NON-VACUITY: the hypothesis class is inhabited by a concrete multigraph
        that is [bridgeless] AND has edges ([G2p] of [grounding_U6], two
        parallel edges in the same reference direction), and the conclusion
        [x228_half_flow_pair] is inhabited (all-zero pair on the edgeless
        one-vertex graph, zero [k]-flow on any graph);
      - GUARD HAS TEETH: the all-zero pair, which satisfies both [k]-flow
        conditions, is rejected by the compatibility condition as soon as the
        graph has an edge; and every pair witnesses a nowhere-zero combination;
      - SETTLED CASE: every multigraph with a nowhere-zero 2-flow (an eulerian
        reference orientation) satisfies the conjecture, with [phi_4 = 0]. *)

From mathcomp Require Import all_boot.
From GraphTheory Require Import mgraph sgraph treewidth.
From GTBase Require Import base.
From Cycle.foundations Require Import connectivity.
From Cycle.conjectures Require Import U6 grounding_U6 D1 X228.
(* [all_algebra] LAST: [X228.v] re-exports [GTBase.base], which re-exports
   [all_boot]; importing it after the algebra layer would give back [all_boot]'s
   [%:R] and break the [int] ring numerals (cf. the import note of [D1.v]). *)
From mathcomp Require Import all_algebra all_fingroup.

Import GRing.Theory Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope ring_scope.

(** ** The hypothesis class is inhabited by a graph WITH edges *)

(** [G2p] (two vertices, two PARALLEL edges in the same reference direction) is
    bridgeless: each of its two edges admits an undirected walk between its ends
    avoiding it, namely the other edge.  Since [is_bridge] is stated with the
    UNDIRECTED [uwalk] ([ueseparates] of [Cycle.foundations.connectivity]), the
    reference orientation is irrelevant and the digon [Gd], whose two edges are
    ANTIPARALLEL, is bridgeless for exactly the same reason.  Sharper witnesses
    of the hypothesis class (a simple bridgeless triangle; a genuine cut edge
    that IS a bridge) are in [grounding_X212]. *)
Lemma x228_bridgeless_G2p : bridgeless G2p.
Proof.
move=> e; case: e => [x|] sep.
- move: sep; case: x => [e0|] sep.
  + by move: sep; case: e0 => -[].
  + have [f fE fw] := sep [:: None] isT.
    by move: fE fw; rewrite !inE => /eqP ->.
- have [f fE fw] := sep [:: Some None] isT.
  by move: fE fw; rewrite !inE => /eqP ->.
Qed.

Lemma x228_card_edge_G2p : #|edge G2p| = 2.
Proof. by rewrite /G2p /G1 /G0 !card_option card_sum !card_void. Qed.

Lemma x228_hypothesis_inhabited : (0 < #|edge G2p|)%N /\ bridgeless G2p.
Proof. by split; [rewrite x228_card_edge_G2p | exact: x228_bridgeless_G2p]. Qed.

(** ** [x228_kflow] : the zero flow, and the structural bound *)

(** The all-zero weighting is a [k]-flow for every [k] (non-vacuity of the
    [k]-flow predicate; note that it is NOT a nowhere-zero [k]-flow). *)
Lemma x228_kflow0 (G : mgraph) (k : nat) : @x228_kflow G k (fun _ => 0).
Proof.
split; first by move=> v; rewrite !big1.
by move=> e; rewrite normr0 ler0n.
Qed.

(** A nowhere-zero [k]-flow is in particular a [k]-flow (consistency with
    [D1.has_nz_kflow]). *)
Lemma x228_kflow_of_nz (G : mgraph) (k : nat) (phi : edge G -> int) :
  iconservative phi -> int_bounded k phi -> @x228_kflow G k phi.
Proof. by move=> con bnd; split=> // e; case: (bnd e). Qed.

(** ** Non-vacuity of the conclusion *)

(** The one-vertex (edgeless) multigraph has a 1/2-flow-pair. *)
Lemma x228_half_flow_pair_unit : x228_half_flow_pair U.
Proof.
exists (fun _ => 0), (fun _ => 0); split; try exact: x228_kflow0.
by move=> e; case: e.
Qed.

(** ** Guard has teeth *)

(** [2 <= `|x|] forces [x] to be nonzero. *)
Lemma x228_normr_ge2_neq0 (x : int) : 2%:R <= `|x| -> x != 0.
Proof.
move=> h; apply/negP => /eqP x0; move: h; rewrite x0 normr0.
by rewrite lern0.
Qed.

(** The all-zero pair satisfies both [k]-flow conditions but is rejected by the
    compatibility condition on any graph with an edge: the guard has teeth. *)
Lemma x228_zero_pair_teeth (G : mgraph) :
  (0 < #|edge G|)%N ->
  ~ (forall e : edge G, (fun _ : edge G => 0 : int) e = 0 ->
       2%:R <= `|(fun _ : edge G => 0 : int) e|).
Proof.
move=> /card_gt0P[e _] h.
by have /eqP := x228_normr_ge2_neq0 (h e erefl).
Qed.

(** Every 1/2-flow-pair is nowhere zero in the combined sense: on every edge at
    least one of the two flows is nonzero. *)
Lemma x228_pair_nowhere_zero (G : mgraph) (phi2 phi4 : edge G -> int) :
  (forall e : edge G, phi2 e = 0 -> 2%:R <= `|phi4 e|) ->
  forall e : edge G, (phi2 e != 0) || (phi4 e != 0).
Proof.
move=> h e; apply/orP.
case: (eqVneq (phi2 e) 0) => [e0|ne]; last by left.
by right; exact: x228_normr_ge2_neq0 (h e e0).
Qed.

(** ** Settled case *)

(** Every multigraph carrying a nowhere-zero 2-flow — equivalently, whose
    reference orientation is eulerian — satisfies Conjecture 6.1: take that
    2-flow as [phi_2] and the zero 4-flow as [phi_4]; the compatibility
    condition is vacuous because [phi_2] never vanishes. *)
Lemma x228_half_flow_pair_of_nz2 (G : mgraph) :
  has_nz_kflow G 2 -> x228_half_flow_pair G.
Proof.
case=> phi [con bnd]; exists phi, (fun _ => 0); split.
- exact: x228_kflow_of_nz.
- exact: x228_kflow0.
- move=> e e0; have [le1 _] := bnd e; move: le1; rewrite e0 normr0.
  by rewrite ler10.
Qed.

(** ** Axiom audit ********************************************************* *)

Print Assumptions half_flow_pair_statement.
Print Assumptions x228_bridgeless_G2p.
Print Assumptions x228_card_edge_G2p.
Print Assumptions x228_hypothesis_inhabited.
Print Assumptions x228_kflow0.
Print Assumptions x228_kflow_of_nz.
Print Assumptions x228_half_flow_pair_unit.
Print Assumptions x228_normr_ge2_neq0.
Print Assumptions x228_zero_pair_teeth.
Print Assumptions x228_pair_nowhere_zero.
Print Assumptions x228_half_flow_pair_of_nz2.
