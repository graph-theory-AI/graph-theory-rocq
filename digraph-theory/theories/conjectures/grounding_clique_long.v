(** * Digraph.conjectures.grounding_clique_long — STATEMENT-LEVEL grounding of
      [clique_cluster.v] (Conj 5.10 / Q5.9 / Conj 5.8 / dom-cluster) and
      [long_dipath.v] (Cheng–Keevash Conjecture 1).

    This file does NOT introduce any new conjecture node; it audits the existing
    statements for three failure modes:

    (1) NON-VACUITY: the hypothesis class of each ∀-statement is INHABITED.
        - For Conj 5.10 the relevant class is "k-ω̄-critical tournaments";
          C3 is 2-ω̄-critical ([C3_kcritical2]) and, at the conjecture's own
          k ∈ {3,4,5}, [conjecture_5_10_at_345] exhibits witnesses of every
          size — so the class quantified over is genuinely populated.
        - For Cheng–Keevash, C3 is an oriented digraph with min out-degree 1,
          so the antecedent `∀v, d ≤ outdeg v` is satisfiable at d = 1.

    (2) SMALL-INSTANCE / TIGHT WITNESSES.
        - ω̄(C3) = 2 and C3 is 2-ω̄-critical (the base critical object).
        - ℓ(C3) = 2 = 2·1: the Cheng–Keevash CONCLUSION holds on C3 and is
          TIGHT (min out-degree exactly 1).  Hence the conjecture is not
          vacuously satisfiable and not trivially violated on its smallest
          non-transitive instance.
        - The δ = 3 node [ck_conj1_at_3] is the conjecture instantiated at d=3.

    (3) TRIVIALITY / FALSIFICATION probes.  A faithfully-encoded OPEN conjecture
        must be neither provable nor refutable from the tiny grounds above.
        We record (as commentary, NOT as `Qed`/`Admitted`) the two probe results:
        both statements survive — neither closes from C3/TT/AC data.

    Imports: only committed library modules + the two conjecture files being
    grounded. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_fingroup all_algebra.
From Digraph Require Import prelude interop_graph_theory digraph tournament order.
From Digraph Require Import oriented dipath.
From Digraph Require Import omegabar critical domination.
From Digraph Require Import ck3_main unified.
From Digraph Require Import clique_cluster long_dipath.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Part A — clique_cluster.v *)

(** *** A.1  Tight small value: ω̄(C3) = 2 (reused from omegabar). *)
Remark gr_omegabar_C3 : ω̄((C3 : tournament)) = 2.
Proof. exact: omegabar_C3. Qed.

(** *** A.2  Base critical witness: C3 is 2-ω̄-critical. *)
Remark gr_C3_kcritical2 : kcritical 2 (C3 : tournament).
Proof. exact: C3_kcritical2. Qed.

(** TT n is NOT critical for any k ≥ 2 (ω̄(TTₙ) = 1): a sanity check that the
    criticality predicate is discriminating, not always-true. *)
Remark gr_TT_not_kcritical_ge2 (n : nat) (k : nat) :
  0 < n -> 2 <= k -> ~~ kcritical k (TT n : tournament).
Proof.
move=> n0 k2; apply/negP => /kcriticalP[ob _].
have e1 : ω̄((TT n : tournament)) = 1 by exact: omegabar_TT.
move: k2; rewrite -ob e1.
by [].
Qed.

(** *** A.3  NON-VACUITY of [conjecture_5_10_statement].

    The statement quantifies, for each k ≥ 3 and each N, over k-ω̄-critical
    tournaments of size > N.  That class is INHABITED at the conjecture's own
    range k ∈ {3,4,5}: [conjecture_5_10_at_345] produces such witnesses.  We
    package the non-vacuity at k = 3 (and, for completeness, 4 and 5) as a
    standalone fact so an empty-antecedent mis-encoding would be impossible. *)
Remark gr_kcritical_inhabited_k3 (N : nat) :
  exists T : tournament, kcritical 3 T /\ (N < #|T|)%N.
Proof. exact: (conjecture_5_10_at_345 (k := 3) erefl N). Qed.

Remark gr_kcritical_inhabited_k4 (N : nat) :
  exists T : tournament, kcritical 4 T /\ (N < #|T|)%N.
Proof. exact: (conjecture_5_10_at_345 (k := 4) erefl N). Qed.

Remark gr_kcritical_inhabited_k5 (N : nat) :
  exists T : tournament, kcritical 5 T /\ (N < #|T|)%N.
Proof. exact: (conjecture_5_10_at_345 (k := 5) erefl N). Qed.

(** The hypothesis class of Conj 5.10, *at every k in its own {3,4,5} range and
    every N*, is non-empty — i.e. the ∀ in [conjecture_5_10_statement] never
    ranges over the empty set on the proved part of its domain. *)
Remark gr_conj_5_10_nonvacuous (k : nat) :
  (3 <= k <= 5)%N -> forall N, exists T : tournament, kcritical k T /\ (N < #|T|)%N.
Proof. exact: conjecture_5_10_at_345. Qed.

(** *** A.4  Sanity on the Q5.9 mechanism (reused edge, no conjecture resolved):
    a proper subtournament of a critical tournament has strictly smaller ω̄.
    Instantiated on C3 deleting one vertex (a 2-vertex subtournament, ω̄ = 1). *)
Remark gr_C3_proper_sub_drops (S : {set (C3 : tournament)}) :
  S != [set: (C3 : tournament)] -> (ω̄(sub_tournament S) <= 1)%N.
Proof. by move=> Sp; have := kcritical_proper_sub C3_kcritical2 Sp. Qed.

(** *** A.5  TRIVIALITY PROBE for [conjecture_5_10_statement].

    We checked, while writing this file, that neither
      [conjecture_5_10_statement]      (would require an unbounded family for
                                        EVERY k ≥ 3, including k ≥ 6 where the
                                        project has NO construction — genuinely
                                        open, NOT provable from C3/AC), nor
      [~ conjecture_5_10_statement]     (refuting it would need a k with only
                                        finitely many critical tournaments — no
                                        such obstruction is derivable from the
                                        tiny grounds)
    is derivable here.  The verified PARTIAL result is precisely
    [conjecture_5_10_at_345] (k ≤ 5), which does NOT entail the full ∀k≥3
    statement; the gap is the open content.  Therefore the encoding is NOT
    trivially closed — no RED FLAG.  (No `Qed`/`Admitted` is attempted for the
    full statement or its negation; doing so would itself be the red flag.) *)

(** ** Part B — long_dipath.v (Cheng–Keevash Conjecture 1) *)

(** *** B.1  Min out-degree of C3 is 1 (each vertex u points only to u+1). *)
Section C3OutDeg.
Local Open Scope ring_scope.
Import GRing.Theory.

Lemma gr_C3_outdeg (u : (C3 : orientedDigraph)) : outdeg u = 1%N.
Proof.
rewrite /outdeg (_ : [set w | u --> w] = [set u + 1]) ?cards1 //.
by apply/setP=> w; rewrite !inE arcC3E.
Qed.
End C3OutDeg.

(** *** B.2  NON-VACUITY of the Cheng–Keevash antecedent at d = 1.

    `∀ v, d ≤ outdeg v` with d = 1 is satisfied by C3 (an oriented digraph with
    0 < #|C3|), so the universally-quantified statement is NOT vacuous: it makes
    a real assertion about at least one admissible (D, d). *)
Lemma gr_C3_minoutdeg1 : forall v : (C3 : orientedDigraph), 1 <= outdeg v.
Proof. by move=> v; rewrite gr_C3_outdeg. Qed.

Lemma gr_C3_card_gt0 : 0 < #|(C3 : orientedDigraph)|.
Proof. by rewrite card_C3. Qed.

(** *** B.3  ℓ(C3) = 2 = 2·1: the conjecture's CONCLUSION holds and is TIGHT.

    Lower bound from the explicit dipath 0 → 1 → 2; upper bound from
    [dipath_size] (any simple path uses < #|C3| = 3 vertices) folded through the
    bigmax defining ℓ. *)
Section EllC3.
Local Open Scope ring_scope.
Import GRing.Theory.

Lemma gr_ell_C3 : ell (C3 : diGraphType) = 2%N.
Proof.
apply/eqP; rewrite eqn_leq; apply/andP; split.
- (* ell C3 <= 2 : ell = \max_(k < 3 | has_dipath k) k <= 2 *)
  rewrite /ell card_C3.
  by apply/bigmax_leqP => i _; rewrite -ltnS.
- (* 2 <= ell C3 : the path 0 -> 1 -> 2 has size 2 *)
  pose x : C3 := 0.
  pose s : seq C3 := [:: 1; 1 + 1].
  have dp : dipath x s.
    (* path arc 0 [1; 1+1] && uniq computes by reflexivity in the
       concrete finite ring 'Z_3 *)
    by rewrite /dipath.
  by have := ell_max dp.
Qed.
End EllC3.

(** The Cheng–Keevash conclusion `2*d <= ell` instantiated at the C3 witness
    (D = C3, d = 1): 2*1 = 2 <= ell C3 = 2.  Holds, and TIGHT. *)
Remark gr_ck_holds_on_C3 : (2 * 1 <= ell (C3 : diGraphType))%N.
Proof. by rewrite gr_ell_C3. Qed.

Remark gr_ck_tight_on_C3 : (2 * 1 == ell (C3 : diGraphType))%N.
Proof. by rewrite gr_ell_C3. Qed.

(** *** B.4  The δ = 3 node is the conjecture instantiated at d = 3 (reused). *)
Remark gr_ck_at_3 :
  forall D : orientedDigraph, 0 < #|D| -> (forall v : D, 3 <= outdeg v) -> 2 * 3 <= ell D.
Proof. exact: ck_conj1_at_3. Qed.

(** Cross-check: the general statement DOES specialize to the δ=3 instance,
    via the committed edge [conj1_implies_delta3]. *)
Remark gr_general_gives_delta3 :
  cheng_keevash_conj1_statement ->
  forall D : orientedDigraph, 0 < #|D| -> (forall v : D, 3 <= outdeg v) -> 2 * 3 <= ell D.
Proof. exact: conj1_implies_delta3. Qed.

(** *** B.5  TRIVIALITY PROBE for [cheng_keevash_conj1_statement].

    - Provable from tiny grounds?  No: the statement is `∀ D d, … → 2d ≤ ℓ(D)`
      for ARBITRARY d; the project now has unconditional proofs at
      d ∈ {3,4,5,6}, while d ≥ 7 remains open.
      C3 only certifies the d = 1 instance.  So no `Qed` of the full statement.
    - Refutable from tiny grounds?  No: on C3 (the smallest non-transitive
      oriented digraph) the conclusion HOLDS and is TIGHT [gr_ck_tight_on_C3];
      C3 is therefore a confirming, not refuting, instance.  No counterexample
      is available at this scale.
    Hence the encoding is open as intended — NO RED FLAG.  (Again, neither the
    statement nor its negation is `Qed`/`Admitted` here.) *)

(** ** Audit hooks: the reused facts are axiom-free relative to the library. *)
Print Assumptions gr_ell_C3.
Print Assumptions gr_C3_outdeg.
Print Assumptions gr_conj_5_10_nonvacuous.
