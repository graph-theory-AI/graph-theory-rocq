(** * Chromatic.conjectures.implications_X238 -- dependency-graph EDGES for wave X238.

    Machine-checked implication edges into the X238 statements.  Every
    SCHEDULED edge is a RELATIVE theorem: a [Qed]-closed [Theorem A -> B] proved
    WITHOUT resolving either endpoint.  Axiom-free: no [Axiom] / [Parameter] /
    [Admitted] / [Conjecture].

    The edge below is a Rocq-only edge (no corpus relation): X238.v's Notes say that
    "every forest is multibounding" (X218, arxiv:2303.11766#00) implies the path question
    arxiv:2202.05557#01 in its tau_d form; this file proves it. *)

From GTBase Require Import base common path_graphs poly_nat complete_multipartite_graphs.
From Chromatic.conjectures Require Import U8 X218 X238.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Every forest is multibounding ==> every path is multibounding (tau_d form) *)

(** [m <= n -> m ^ e <= n ^ e], by induction on [e]. *)
Lemma x238_leq_expn_base (m n e : nat) : m <= n -> m ^ e <= n ^ e.
Proof. by move=> le; elim: e => [|e IH] //; rewrite !expnS leq_mul. Qed.

(** One polynomial with natural coefficients dominates [c * (t + 1) ^ m] on all of nat:
    [a + t * (a * t ^ m)] with [a = c * 2 ^ m]. At [t = 0] both sides are at least [c]; for
    [t >= 1], [t + 1 <= 2 t] gives [(t + 1) ^ m <= 2 ^ m * t ^ m <= t * 2 ^ m * t ^ m]. *)
Lemma x238_shift_dom (c m t : nat) :
  c * t.+1 ^ m <= c * 2 ^ m + t * (c * 2 ^ m * t ^ m).
Proof.
case: t => [|t].
  by rewrite exp1n muln1 mul0n addn0 leq_pmulr // expn_gt0.
apply: leq_trans (leq_addl _ _).
have h2 : t.+2 <= 2 * t.+1 by rewrite mul2n -addnn addnS ltnS leq_addr.
have hx : t.+2 ^ m <= 2 ^ m * t.+1 ^ m by rewrite -expnMn; exact: x238_leq_expn_base.
apply: (@leq_trans (c * 2 ^ m * t.+1 ^ m)); last exact: leq_pmull.
by rewrite -mulnA leq_mul2l hx orbT.
Qed.

(*@EDGE from=every_forest_is_multibounding_statement to=path_free_polynomial_tau_bound_statement kind=implies status=verified proved=true proof=every_forest_is_multibounding_implies_path_free_polynomial_tau_bound note="Rocq-only edge (no corpus relation), stated in X238.v's Notes: every path P_k is a forest, so multibounding gives chi(G) <= c(d) * s^e(d) for every P_k-induced-free G with no K_d(s) subgraph and s >= 1; tau_d(G) = t excludes K_d(t+1), so s = t+1 applies, and c(d) * (t+1)^e(d) is dominated by the natural-coefficient polynomial a + a * t^(e(d)+1), a = c(d) * 2^e(d)." *)
Theorem every_forest_is_multibounding_implies_path_free_polynomial_tau_bound :
  every_forest_is_multibounding_statement -> path_free_polynomial_tau_bound_statement.
Proof.
move=> H k d d1.
have [c [e He]] := H (ordinal_path k) (@ordinal_path_is_forest k).
exists (c d * 2 ^ e d :: (nseq (e d) 0 ++ [:: c d * 2 ^ e d])) => G t free [_ tmax].
have nind : ~ has_induced (ordinal_path k) G.
  by case=> S [i]; apply: (free S); exact: diso_sym i.
have nsub : ~ has_subgraph G (x218_complete_multipartite d t.+1).
  by move=> hs; have := tmax t.+1 hs; rewrite ltnn.
apply: leq_trans (He d d1 t.+1 G isT nind nsub) _.
rewrite horner_nat_cons horner_nat_monomial; exact: x238_shift_dom.
Qed.
