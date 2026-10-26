(** Witness hint (A2 source repair, 2026-10-26): an axiom-free REFUTATION of
    [Minor.conjectures.X174.kt_immersion_clique_count_extremal_statement] as encoded before its repair
    (corpus row arxiv:1606.06810#00).

    The body's bound [x174_extremal_bound t n] computes (n - t) + 3 in the naturals.  At t = 2, n = 0 the
    existence half asks for a graph on no vertex with 2^0 * 3 = 3 cliques, but the only such graph has one
    clique, the empty set (cliques are counted with the empty one).  The faithfulness audit of 2026-07-17
    (meta/BLOCKED_RETARGETING_AUDIT.md) recorded the subtraction as a truncation caveat; it makes the body
    false.  With the bound 2^(t-2) * (n + 3 - t) this file no longer compiles (hint-stale-FIX-OK). *)
From GTBase Require Import base clique_counts.
From Minor.conjectures Require Import X174.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** A graph without vertices has exactly one clique, the empty set. *)
Lemma empty_clique_count (G : sgraph) : #|G| = 0 -> x174_clique_count G = 1.
Proof.
move=> h0; change (#|cliques [set: G]| = 1).
have e (K : {set G}) : K = set0.
  by apply/eqP; rewrite -cards_eq0 -leqn0 -h0; exact: max_card.
rewrite (_ : cliques _ = [set set0]) ?cards1 //.
apply/setP => K; rewrite !inE (e K) eqxx sub0set /=.
by apply/cliqueP => x; rewrite inE.
Qed.

Lemma refuted : ~ kt_immersion_clique_count_extremal_statement.
Proof.
move=> h; have [_ [G [hG [_ hc]]]] := h 2 0 (leqnn 2) (leq0n _).
by move: hc; rewrite empty_clique_count.
Qed.

Print Assumptions refuted.
