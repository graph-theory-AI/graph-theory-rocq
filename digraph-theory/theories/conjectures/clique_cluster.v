(** * Digraph.conjectures.clique_cluster — AACL "clique number of tournaments" cluster

    Statement-only formalization (no axioms) of the ω̄-cluster conjectures of
    Aboulker–Aubian–Charbit–Lopes, "The clique number of tournaments" (arXiv:2310.04265),
    together with the literature-stated implication edges between them.
    See docs/CONJECTURES_FORMALIZATION_PLAN.md §1, §5 (P1), §7.

    Here ω̄(T) = [omegabar T] is the tournament clique number (min over vertex orders of
    the clique number of the back-edge graph), [kcritical k T] is k-ω̄-criticality, and
    [domnum T] is the directed domination number; all are reused from the invariants layer.

    Nodes (Definitions of type Prop):
      - [conjecture_5_10_statement]   : for every k ≥ 3, infinitely many k-ω̄-critical
                                        tournaments (the OPEN ∀k generalization; the
                                        k ∈ {3,4,5} instances are PROVED in
                                        applications/unified.v, [conjecture_5_10_at_345]).
      - [question_5_9_statement]      : the f = id "ω̄-cluster" question, positive form —
                                        ω̄(T) ≥ k is witnessed by a subtournament of size
                                        ≤ ℓ(k).
      - [conjecture_5_8_statement]    : the f ≠ id weakening of Q5.9.
      - [dom_omega_cluster_statement] : "large domination number ⇒ ω̄-cluster".

    Edges (Qed-closed relative theorems — provable without resolving any conjecture):
      - [conj_5_10_implies_neg_Q5_9]   : Conjecture 5.10  ⟹  ¬ Question 5.9.
      - [Q5_9_implies_conj_5_8]        : Question 5.9     ⟹  Conjecture 5.8.
      - [conj_5_8_implies_dom_cluster] : Conjecture 5.8   ⟹  dom⇒ω̄-cluster (via dom ≤ ω̄). *)

From HB Require Import structures.
From mathcomp Require Import all_boot.
From Digraph Require Import prelude interop_graph_theory digraph tournament.
From Digraph Require Import omegabar critical domination.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Nodes *)

(** Corpus row: arxiv:2310.04265#10
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/2310.04265__10/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/2310.04265__10.json
    English statement: (Aboulker, Aubian, Charbit, Lopes 2023, Clique number of tournaments, arXiv:2310.04265, Conjecture 5.10)
      For every k >= 3 and every N there is a tournament with more than N vertices that is
      k-omega-bar-critical, that is whose tournament clique number equals k while deleting any
      single vertex drops it to k-1; equivalently there are infinitely many k-omega-bar-critical
      tournaments.
    Definitions: [omegabar T] (written omega-bar) - the tournament clique number, the minimum
      over vertex orderings of the clique number of the back-edge graph (invariants/omegabar.v,
      over core/order.v); [sub_tournament S] (core/tournament.v); [kcritical k T] - omega-bar of
      T equals k and omega-bar of every vertex-deleted tournament equals k-1
      (invariants/critical.v).
    Notes: Infinitely many up to isomorphism is encoded as arbitrarily large, which is
      equivalent here because tournaments of a fixed order form a finite set. The row is marked
      solved (Chen and Wang); the definition encodes the original conjecture. *)
Definition conjecture_5_10_statement : Prop :=
  forall k : nat, (3 <= k)%N ->
    forall N : nat, exists T : tournament, kcritical k T /\ (N < #|T|)%N.

(** Corpus row: arxiv:2310.04265#09
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/2310.04265__09/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/2310.04265__09.json
    English statement: (Aboulker, Aubian, Charbit, Lopes 2023, Clique number of tournaments, arXiv:2310.04265, Question 5.9)
      There is a function ell such that for every tournament T and every k, if the tournament
      clique number of T is at least k then T has a subtournament on at most ell(k) vertices
      whose tournament clique number is still at least k.
    Definitions: [omegabar T] (written omega-bar) - the tournament clique number, the minimum
      over vertex orderings of the clique number of the back-edge graph (invariants/omegabar.v,
      over core/order.v); [sub_tournament S] (core/tournament.v).
    Notes: The positive (f = id) form of the question: the threshold on T is the same k that the
      witness must reach. The row is marked disproved, the refutation being the arbitrarily
      large critical tournaments of [conjecture_5_10_statement]; the edge
      [conj_5_10_implies_neg_Q5_9] in this file proves that implication. *)
Definition question_5_9_statement : Prop :=
  exists ell : nat -> nat,
    forall (T : tournament) (k : nat), (k <= ω̄(T))%N ->
      exists S : {set T}, (#|S| <= ell k)%N /\ (k <= ω̄(sub_tournament S))%N.

(** No corpus row: Conjecture 5.8 of arXiv:2310.04265, the f different from identity weakening
    of Question 5.9 (two functions f and ell such that omega-bar(T) >= f(k) forces a
    subtournament of size at most ell(k) with omega-bar at least k); the corpus has no row for
    it, the neighbouring rows being __09 (Question 5.9, on [question_5_9_statement]) and __07
    (Conjecture 5.3, on [dom_omega_cluster_statement]). It is kept as the middle node of the
    implication chain proved in this file. *)
Definition conjecture_5_8_statement : Prop :=
  exists f ell : nat -> nat,
    forall (T : tournament) (k : nat), (f k <= ω̄(T))%N ->
      exists S : {set T}, (#|S| <= ell k)%N /\ (k <= ω̄(sub_tournament S))%N.

(** Corpus row: arxiv:2310.04265#07
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/2310.04265__07/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/2310.04265__07.json
    English statement: (Aboulker, Aubian, Charbit, Lopes 2023, Clique number of tournaments, arXiv:2310.04265, Conjecture 5.3, large dom implies an omega-bar-cluster)
      There are functions f and ell such that for every tournament T and every k, if the
      directed domination number of T is at least f(k) then T has a subtournament on at most
      ell(k) vertices whose tournament clique number is at least k.
    Definitions: [omegabar T] (written omega-bar) - the tournament clique number, the minimum
      over vertex orderings of the clique number of the back-edge graph (invariants/omegabar.v,
      over core/order.v); [sub_tournament S] (core/tournament.v); [domnum T] - the directed
      domination number, the least size of a set that dominates every vertex
      (invariants/domination.v).
    Notes: The row is marked solved: it follows from Conjecture 5.8 via dom(T) <= omega-bar(T),
      which is the edge [conj_5_8_implies_dom_cluster] proved in this file. *)
Definition dom_omega_cluster_statement : Prop :=
  exists f ell : nat -> nat,
    forall (T : tournament) (k : nat), (f k <= domnum T)%N ->
      exists S : {set T}, (#|S| <= ell k)%N /\ (k <= ω̄(sub_tournament S))%N.

(** ** Edges *)

(** Conjecture 5.10 ⟹ ¬ Question 5.9.  If both held, take (at k = 3) a 3-ω̄-critical T
    larger than ℓ(3); Q5.9 yields a subtournament S with |S| ≤ ℓ(3) < |T|, hence S proper,
    so ω̄(S) ≤ 3−1 = 2 by criticality, contradicting ω̄(S) ≥ 3. *)
Theorem conj_5_10_implies_neg_Q5_9 :
  conjecture_5_10_statement -> ~ question_5_9_statement.
Proof.
move=> C10 [ell HQ].
have [T [crit cardT]] := C10 3 (leqnn 3) (ell 3).
have oT : ω̄(T) = 3 by have /kcriticalP[E _] := crit; exact: E.
have h3 : (3 <= ω̄(T))%N by rewrite oT.
have [S [cardS oS]] := HQ T 3 h3.
have Sproper : S != [set: T].
  apply/eqP => ST.
  move: cardS; rewrite ST cardsT => hTle.
  have habs := leq_ltn_trans hTle cardT.
  by rewrite ltnn in habs.
have hle := kcritical_proper_sub crit Sproper.
have habs2 : (ω̄(sub_tournament S) < ω̄(sub_tournament S))%N.
  by apply: (leq_ltn_trans hle); exact: oS.
by rewrite ltnn in habs2.
Qed.

(** Question 5.9 ⟹ Conjecture 5.8 (it is the special case f = id). *)
Theorem Q5_9_implies_conj_5_8 :
  question_5_9_statement -> conjecture_5_8_statement.
Proof. by case=> ell HQ; exists (fun k => k), ell => T k; exact: (HQ T k). Qed.

(** Conjecture 5.8 ⟹ "large dom ⇒ ω̄-cluster" (via dom(T) ≤ ω̄(T)). *)
Theorem conj_5_8_implies_dom_cluster :
  conjecture_5_8_statement -> dom_omega_cluster_statement.
Proof.
case=> f [ell H58]; exists f, ell => T k hf.
apply: (H58 T k).
exact: leq_trans hf (domnum_le_omegabar T).
Qed.
