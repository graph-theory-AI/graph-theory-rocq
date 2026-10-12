(** * Extremal.foundations.fractional_hadwiger — the attained fractional Hadwiger number (clique-minor LP)

    Family [fractional-clique-minor] (meta/library_primitives/fractional-clique-minor.json).
    [frac_clique_minor B w r] is a feasible point of the fractional clique-minor LP of [G]: an indexed family of
    branch sets [B : 'I_n -> {set G}] with weights [w : 'I_n -> rat] such that
    - every weight is non-negative;
    - every branch set is NON-EMPTY and connected;
    - two distinct indices have adjacent branch sets (some [x] in [B i], [y] in [B j] with [x -- y]);
    - every vertex is covered by total weight at most 1;
    - [r] is the total weight.
    Branch sets need not be disjoint.  [is_fractional_hadwiger G r] says that [r] is the fractional Hadwiger number
    had_f(G) as an ATTAINED MAXIMUM: some feasible point has value [r], and every feasible point has value at most [r].

    History: this is the body REPAIRED in wave E10 (e61d308, 2026-09-24), unchanged since.  The pre-repair body
    allowed empty branch sets, so the LP was unbounded and the fractional Hadwiger number existed for no graph (the
    D2chr row was vacuously true).  That defective body and its witness stay, verbatim, in
    [Extremal.conjectures.grounding_D2chr] ([old_frac_clique_minor], [old_is_fractional_hadwiger_unsat]) as a
    re-audited historical record; it is not a migration Original of this family.

    Degenerate cases: there is no guard on [G].  The empty family is feasible with value 0
    ([frac_clique_minor_trivial]), so had_f(G) >= 0, and every feasible value is at most the number of vertices
    ([frac_clique_minor_le_card], by non-emptiness): the LP is bounded and had_f('K_0) = 0.  The value is unique
    ([is_fractional_hadwiger_unique]).  Its EXISTENCE for every finite graph is the LP attainment theorem
    [Atlas.foundations.fractional.frac_hadwiger_exists] (through [Extremal.foundations.lp_rational.lp_max_fin]); it is
    not assumed here.

    Distinct notions, not defined here: the integer Hadwiger number [Extremal.conjectures.D2chr.is_hadwiger] (a [K_h]
    minor with maximality, over GraphTheory [minor]); the LP over sets of branch sets in
    [Atlas.foundations.fractional] ([goodb]/[hfeas]/[hopt], local to its existence proof).  The bodies are those of
    [Extremal.conjectures.D2chr.frac_clique_minor] and [Extremal.conjectures.D2chr.is_fractional_hadwiger], whose names
    are transparent aliases of these since the fractional-clique-minor library migration. *)

From GTBase Require Import base.
From mathcomp Require Import all_algebra.
Import GRing.Theory Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.

Definition frac_clique_minor (G : sgraph) (n : nat)
    (B : 'I_n -> {set G}) (w : 'I_n -> rat) (r : rat) : Prop :=
  [/\ (forall i, 0 <= w i),
      (forall i, B i != set0 /\ connected (B i)),
      (forall i j, i != j -> exists x y : G, [/\ x \in B i, y \in B j & x -- y]),
      (forall v : G, (\sum_(i | v \in B i) w i <= 1)%R)
    & r = \sum_i w i].

Definition is_fractional_hadwiger (G : sgraph) (r : rat) : Prop :=
  (exists (n : nat) (B : 'I_n -> {set G}) (w : 'I_n -> rat), frac_clique_minor B w r) /\
  (forall (n : nat) (B : 'I_n -> {set G}) (w : 'I_n -> rat) (r' : rat),
     frac_clique_minor B w r' -> r' <= r).

(** ** Feasible points *)

(** The empty family is feasible, with value 0. *)
Lemma frac_clique_minor_trivial (G : sgraph) :
  @frac_clique_minor G 0 (fun _ => set0) (fun _ => 0) 0.
Proof.
split; try by case.
- by move=> v; rewrite big_ord0.
- by rewrite big_ord0.
Qed.

(** Every branch set of a feasible point is non-empty (the E10 repair). *)
Lemma frac_clique_minor_nonempty (G : sgraph) n (B : 'I_n -> {set G}) w r i :
  frac_clique_minor B w r -> B i != set0.
Proof. by case=> _ /(_ i) []. Qed.

(** Boundedness: since every branch set is non-empty,
    [sum_i w i <= sum_i sum_(v in B i) w i = sum_v sum_(i | v in B i) w i <= |V(G)|]. *)
Lemma frac_clique_minor_le_card (G : sgraph) n (B : 'I_n -> {set G}) w r :
  frac_clique_minor B w r -> r <= (#|G|)%:R.
Proof.
case=> w0 ne _ cov ->.
have step1 : \sum_i w i <= \sum_i \sum_(v in B i) w i.
  apply: ler_sum => i _; rewrite sumr_const.
  have [/set0Pn [x xB] _] := ne i.
  have c1 : (1 <= #|B i|)%N by rewrite card_gt0; apply/set0Pn; exists x.
  case: #|B i| c1 => // k _.
  by rewrite mulrS lerDl mulrn_wge0.
apply: (order.Order.POrderTheory.le_trans step1).
have -> : \sum_i \sum_(v in B i) w i = \sum_(v : G) \sum_(i | v \in B i) w i.
  rewrite (eq_bigr (fun i => \sum_(v : G) (if v \in B i then w i else 0))); last first.
    by move=> i _; rewrite big_mkcond.
  rewrite exchange_big; apply: eq_bigr => v _; by rewrite [RHS]big_mkcond.
rewrite -[X in _ <= X]mulr1n -sumr_const.
by apply: ler_sum => v _; exact: cov.
Qed.

(** ** The attained maximum *)

Lemma is_fractional_hadwiger_unique (G : sgraph) (r1 r2 : rat) :
  is_fractional_hadwiger G r1 -> is_fractional_hadwiger G r2 -> r1 = r2.
Proof.
move=> [E1 UB1] [E2 UB2]; apply: order.Order.POrderTheory.le_anti; apply/andP; split.
- by case: E1 => n1 [B1 [w1 H1]]; apply: (UB2 _ B1 w1).
- by case: E2 => n2 [B2 [w2 H2]]; apply: (UB1 _ B2 w2).
Qed.

Lemma is_fractional_hadwiger_ge0 (G : sgraph) (r : rat) : is_fractional_hadwiger G r -> 0 <= r.
Proof. by case=> _ /(_ 0%N _ _ 0 (frac_clique_minor_trivial G)). Qed.

Lemma is_fractional_hadwiger_le_card (G : sgraph) (r : rat) :
  is_fractional_hadwiger G r -> r <= (#|G|)%:R.
Proof. by case=> -[n [B [w H]]] _; exact: frac_clique_minor_le_card H. Qed.
