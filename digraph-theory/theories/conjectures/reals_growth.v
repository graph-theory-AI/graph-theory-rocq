(** * Digraph.conjectures.reals_growth — P8: the reals / Θ-growth envelopes

    The deferred ASYMPTOTIC layer.  This file states (axiom-free) the real-valued
    Θ-growth envelopes and the real-threshold statements that the combinatorial
    cores in [chi_bounded.v], [sad.v] and [unvd.v] intentionally abstracted away.

    Self-contained Landau machinery over real sequences [nat -> R] (Stdlib
    [Reals]; mathcomp-analysis is NOT installed), coexisting with mathcomp: all
    NAT operations stay in [%N], all REAL operations in [%R], bridged by the
    coercion [INR : nat -> R] applied to the cardinal/value of a digraph.

      - [is_BigO] / [is_BigOmega] / [is_Theta] : the standard one-sided and
        two-sided Landau predicates on real sequences (eventual, with explicit
        positive constants and a threshold [N]).

      - Conjecture 3 (arXiv:2403.02298, oriented triangle-free):
        a⃗(n) = min over n-vertex oriented triangle-free graphs of the acyclic
        number satisfies  a⃗(n) = Θ(√(n·ln n)).
      - Conjecture 4 (same): t⃗(n) = max dichromatic number over the same class
        satisfies  t⃗(n) = Θ(√(n / ln n)).

        a⃗ / t⃗ are NOT built as concrete functions (the n-vertex oriented
        triangle-free class is not a finite enumerable type at [diGraphType]
        level, so a min/max FOLD is awkward and would not be faithful).  Instead
        each is captured by its DEFINING EXTREMAL PROPERTY as a relation
        ([is_avec] / [is_tvec], reusing [chi_bounded.v]'s class predicates and
        [acyclic_number_ge] / [dicolorableb]), and the Θ-conjecture is stated for
        ANY function [av] / [tv] satisfying that relation at every order.  This is
        faithful: any genuine a⃗ / t⃗ satisfies the relation, and the conjecture
        constrains exactly its growth.

      - EC-log threshold (P3, [sad.v]): every Eulerian digraph whose arc-strength
        is at least [6·log₂ n] has a Strong Arc Decomposition (Bang-Jensen–Yeo
        Eulerian logarithmic milestone, with the proven constants C = 6, n₀ = 3;
        see problems/arc_disjoint_strong_spanning_subdigraphs/attack_plan.md and
        CORRECTNESS_REVIEW_2026_05_18.md).  The real threshold [6·log₂ n] uses
        [ln] via [log2 x := ln x / ln 2]; the arc-strength is the nat [arc_strong]
        of [sad.v], compared to the real threshold through [INR].

      - unvd Problem 6 (P5, [unvd.v]): bounded-mad ⟹ a polynomial unavoidability
        bound.  Re-exported verbatim as [unvd.prob_6] (its bound is already a
        concrete polynomial [a·|V|^d + b]; the "exists a polynomial bound" reading
        the assignment asks for); a real-coefficient relaxation is recorded too.

    Degenerate orders are guarded throughout ([0 < n] / [0 < #|D|] / the [N]
    threshold of the Landau predicates), so nothing is vacuously true/false.
    See docs/CONJECTURES_FORMALIZATION_PLAN.md §4 (P8). *)

From HB Require Import structures.
From mathcomp Require Import all_boot.
From Digraph Require Import prelude interop_graph_theory digraph oriented tournament dipath.
From Digraph Require Import dichromatic heroes.
From Digraph Require Import chi_bounded sad unvd.
From Stdlib Require Import Reals.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** All real arithmetic below lives in [R_scope]; we keep nat operations in [%N]
    explicitly so the two layers never clash.  Stdlib's [Reals] steals the [%N]
    delimiter for binary numbers ([N_scope]); we reclaim it for mathcomp's
    [nat_scope] so the [%N] idiom used everywhere else in the corpus keeps
    working. *)
Local Open Scope R_scope.
Delimit Scope nat_scope with N.

(** ** Self-contained Landau predicates over real sequences [f, g : nat -> R]

    [is_BigO f g]      : eventually [f n <= c·g n]               (upper envelope).
    [is_BigOmega f g]  : eventually [c·g n <= f n]               (lower envelope).
    [is_Theta f g]     : both, with two positive constants and a shared
                         threshold [N] — the standard f = Θ(g). *)

Definition is_BigO (f g : nat -> R) : Prop :=
  exists (c : R) (N : nat),
    0 < c /\ forall n : nat, (N <= n)%N -> f n <= c * g n.

Definition is_BigOmega (f g : nat -> R) : Prop :=
  exists (c : R) (N : nat),
    0 < c /\ forall n : nat, (N <= n)%N -> c * g n <= f n.

Definition is_Theta (f g : nat -> R) : Prop :=
  exists (c1 c2 : R) (N : nat),
    [/\ 0 < c1, 0 < c2 &
        forall n : nat, (N <= n)%N -> c1 * g n <= f n /\ f n <= c2 * g n].

(** Sanity edges: Θ is the conjunction of the two one-sided envelopes. *)
Theorem is_Theta_BigO (f g : nat -> R) : is_Theta f g -> is_BigO f g.
Proof.
move=> [c1 [c2 [N [_ Pc2 H]]]]; exists c2, N; split=> // n Nn.
by case: (H n Nn).
Qed.

Theorem is_Theta_BigOmega (f g : nat -> R) : is_Theta f g -> is_BigOmega f g.
Proof.
move=> [c1 [c2 [N [Pc1 _ H]]]]; exists c1, N; split=> // n Nn.
by case: (H n Nn).
Qed.

Theorem BigO_BigOmega_Theta (f g : nat -> R) :
  is_BigO f g -> is_BigOmega f g -> is_Theta f g.
Proof.
move=> [c2 [N2 [Pc2 H2]]] [c1 [N1 [Pc1 H1]]].
exists c1, c2, (maxn N1 N2); split=> // n Nn.
by split; [apply: H1; apply: leq_trans (leq_maxl _ _) Nn
          | apply: H2; apply: leq_trans (leq_maxr _ _) Nn].
Qed.

(** ** Base-2 logarithm and √ envelopes

    [log2 x := ln x / ln 2].  The two extremal envelopes are
    [env_a n := √(n·ln n)] and [env_t n := √(n / ln n)]. *)
Definition log2 (x : R) : R := ln x / ln 2.

Definition env_a (n : nat) : R := sqrt (INR n * ln (INR n)).
Definition env_t (n : nat) : R := sqrt (INR n / ln (INR n)).

(** ** a⃗(n): minimum acyclic number over n-vertex oriented triangle-free graphs

    [is_avec av] : the nat-sequence [av] IS the extremal function a⃗ — for every
    order [n > 0], [av n] is the minimum acyclic number over the (nonempty) class
    of oriented triangle-free graphs of order [n].  Faithful "min" via the two
    defining clauses, reusing [chi_bounded.v]:
      (lower) every order-[n] member has acyclic number ≥ [av n]
              ([acyclic_number_ge D (av n)]);
      (attained) some order-[n] member [D] has acyclic number EXACTLY [av n]
              (it has an acyclic induced set of size [av n] but none of size
              [(av n).+1]).
    The class predicate is [oriented_dg D /\ underlying_triangle_free D]. *)
Definition oriented_tfree (D : diGraphType) : Prop :=
  oriented_dg D /\ underlying_triangle_free D.

Definition is_avec (av : nat -> nat) : Prop :=
  forall n : nat, (0 < n)%N ->
    (forall D : diGraphType, #|D| = n -> oriented_tfree D ->
        acyclic_number_ge D (av n)) /\
    (exists D : diGraphType,
        [/\ #|D| = n, oriented_tfree D,
            acyclic_number_ge D (av n) & ~ acyclic_number_ge D (av n).+1]).

(** ** t⃗(n): maximum dichromatic number over the same class

    [is_tvec tv] : [tv n] is the maximum dichromatic number χ⃗ over n-vertex
    oriented triangle-free graphs.  Faithful "max" (reusing [dicolorableb], whose
    [dicolorableb D k] means χ⃗(D) ≤ k):
      (upper) every order-[n] member is [tv n]-dicolourable (χ⃗ ≤ tv n);
      (attained) some order-[n] member [D] is NOT [(tv n)-1]-dicolourable
              (χ⃗(D) ≥ tv n), so its χ⃗ equals [tv n].
    Guarded [0 < n]. *)
Definition is_tvec (tv : nat -> nat) : Prop :=
  forall n : nat, (0 < n)%N ->
    (forall D : diGraphType, #|D| = n -> oriented_tfree D ->
        dicolorableb D (tv n)) /\
    (exists D : diGraphType,
        [/\ #|D| = n, oriented_tfree D,
            dicolorableb D (tv n) & ~~ dicolorableb D (tv n).-1]).

(** No corpus row: the real-valued asymptotic envelope of Conjecture 3 of arXiv:2403.02298 (the
    minimum acyclic number over oriented triangle-free digraphs of order n is Theta of the
    square root of n times ln n), stated for EVERY function satisfying the extremal relation
    [is_avec]. The corpus carries no row for that paper; its combinatorial core is the likewise
    row-less [avec_core_statement] of conjectures/chi_bounded.v. *)
Definition conj3_avec_Theta_statement : Prop :=
  forall av : nat -> nat,
    is_avec av ->
    is_Theta (fun n => INR (av n)) env_a.

(** No corpus row: the concrete-function reading of the same asymptotic envelope (there EXISTS a
    function satisfying the extremal relation [is_avec] whose real image is Theta of the square
    root of n times ln n); a variant of [conj3_avec_Theta_statement] above, with no corpus row. *)
Definition conj3_avec_exists_statement : Prop :=
  exists av : nat -> nat,
    is_avec av /\ is_Theta (fun n => INR (av n)) env_a.

(** No corpus row: the real-valued asymptotic envelope of Conjecture 4 of arXiv:2403.02298 (the
    maximum dichromatic number over oriented triangle-free digraphs of order n is Theta of the
    square root of n divided by ln n), stated for EVERY function satisfying the extremal
    relation [is_tvec]. No corpus row; the combinatorial core is [tvec_core_statement] of
    conjectures/chi_bounded.v. *)
Definition conj4_tvec_Theta_statement : Prop :=
  forall tv : nat -> nat,
    is_tvec tv ->
    is_Theta (fun n => INR (tv n)) env_t.

(** No corpus row: the concrete-function reading of the same envelope (there EXISTS a function
    satisfying [is_tvec] whose real image is Theta of the square root of n divided by ln n); a
    variant of [conj4_tvec_Theta_statement] above, with no corpus row. *)
Definition conj4_tvec_exists_statement : Prop :=
  exists tv : nat -> nat,
    is_tvec tv /\ is_Theta (fun n => INR (tv n)) env_t.

(** ** EC-log threshold (P3, reuse [sad.v]'s [SAD])

    Eulerianness: in-degree equals out-degree at every vertex.  We give the
    general-digraph in-degree locally ([outdeg] of [oriented.v] is the
    out-degree); [eulerian D] ≡ ∀v, indeg v = outdeg v. *)
Definition indeg (D : diGraphType) (v : D) : nat := #|[set w : D | w --> v]|.

Definition eulerian (D : diGraphType) : Prop :=
  forall v : D, indeg v = outdeg v.

(** No corpus row: the Eulerian logarithmic milestone of the Bang-Jensen-Yeo
    strong-arc-decomposition attack (problems/arc_disjoint_strong_spanning_subdigraphs): there
    is a positive real constant c such that every Eulerian digraph on at least three vertices
    whose arc-strength k satisfies k >= c * log2(n) has a strong arc decomposition. It is a
    proved milestone of the attack, not a corpus conjecture; the corpus row for the conjecture
    itself is on [bang_jensen_yeo_SAD_statement] in conjectures/sad.v. *)
Definition ec_log_statement : Prop :=
  exists c : R,
    0 < c /\
    forall (D : diGraphType) (k : nat),
      (3 <= #|D|)%N ->
      eulerian D ->
      arc_strong D k ->
      INR k >= c * log2 (INR #|D|) ->
      SAD D.

(** No corpus row: the concrete c = 6 instance of [ec_log_statement] above (every Eulerian
    digraph on at least three vertices with arc-strength at least 6 * log2(n) has a strong arc
    decomposition), which implies the existential form through the Qed edge
    [ec_log_c6_implies_exists] of this file. No corpus row. *)
Definition ec_log_c6_statement : Prop :=
  forall (D : diGraphType) (k : nat),
    (3 <= #|D|)%N ->
    eulerian D ->
    arc_strong D k ->
    INR k >= 6 * log2 (INR #|D|) ->
    SAD D.

Theorem ec_log_c6_implies_exists :
  ec_log_c6_statement -> ec_log_statement.
Proof. by move=> H; exists 6; split; [prove_sup0 | exact: H]. Qed.

(** No corpus row: a verbatim re-export of [unvd.prob_6], which owns the corpus row
    arxiv:2410.23566#00 and is documented at its definition in conjectures/unvd.v; this alias
    only surfaces the polynomial unavoidability bound under the asymptotic umbrella of this
    file, together with the real-envelope edge [prob6_nat_bound_real_envelope]. *)
Definition prob6_unvd_statement : Prop := unvd.prob_6.

(** EDGE (Qed-closed): the concrete [nat] polynomial bound of [unvd.prob_6]
    transfers to a genuine REAL polynomial envelope through [INR] — the
    unavoidability number [nD] of any digraph [D] satisfying [nD ≤ a·|V|^d + b]
    is dominated by the real polynomial [INR a · (INR |V|)^d + INR b].  This is
    the asymptotic (real-envelope) reading the P8 cluster wants; [_ ^ d] here is
    Stdlib's real power [pow] on [R]. *)
Theorem prob6_nat_bound_real_envelope
    (D : diGraphType) (a d b nD : nat) :
  (nD <= a * #|D| ^ d + b)%N ->
  INR nD <= INR a * (INR #|D|) ^ d + INR b.
Proof.
move=> H; apply: (Rle_trans _ (INR (a * #|D| ^ d + b))).
  by apply/le_INR; apply/leP.
rewrite plus_INR mult_INR; apply: Rplus_le_compat_r.
by apply: Rmult_le_compat_l; [apply: pos_INR | rewrite pow_INR; apply: Rle_refl].
Qed.

(** ** Relative edge: the EC-log milestone is a partial Bang-Jensen–Yeo SAD result

    Under EC-log, every Eulerian digraph of order ≥ 3 whose arc-strength clears
    the [6·log₂ n] threshold has a SAD — i.e. EC-log discharges the high-λ
    Eulerian regime of [bang_jensen_yeo_SAD_statement] (the residual hard regime
    being the bounded-λ Eulerian and the non-Eulerian cases).  We record the
    direct consequence: EC-log gives, for each qualifying [D], the SAD that
    [bang_jensen_yeo_SAD_statement] would assert. *)
Theorem ec_log_gives_SAD :
  ec_log_statement ->
  exists c : R, 0 < c /\
    forall (D : diGraphType) (k : nat),
      (3 <= #|D|)%N -> eulerian D -> arc_strong D k ->
      INR k >= c * log2 (INR #|D|) -> SAD D.
Proof. by move=> H; exact: H. Qed.
