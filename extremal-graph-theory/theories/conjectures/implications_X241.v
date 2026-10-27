(** * Extremal.conjectures.implications_X241 -- dependency-graph EDGES for wave X241.

    Machine-checked implication edges into the X241 statements.  Every
    SCHEDULED edge is a RELATIVE theorem: a [Qed]-closed [Theorem A -> B] proved
    WITHOUT resolving either endpoint.  Axiom-free: no [Axiom] / [Parameter] /
    [Admitted] / [Conjecture].

    The edge below is a Rocq-only edge (no corpus relation): X241.v's Notes say that
    X240's erdos:986 (R(k, n) >> n^{k-1} / (log n)^c for every fixed k >= 3) at k = 4
    implies erdos:166 (R(4, k) >> k^3 / (log k)^{O(1)}); this file proves it. *)

From Extremal.conjectures Require Import XE1 X240 X241.
From GTBase Require Import base common.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** erdos:986 at k = 4 ==> erdos:166 *)

(*@EDGE from=clique_ramsey_polylog_lower_statement to=ramsey_four_cubic_polylog_lower_statement kind=implies status=verified proved=true proof=clique_ramsey_polylog_lower_implies_ramsey_four_cubic_polylog_lower note="Rocq-only edge (no corpus relation), stated in X241.v's Notes: erdos:986 at k = 4 gives c, p > 0 and n0 with n^4 <= p * R(4, n) * n * (trunc_log 2 n)^c for n >= n0; for n >= max(n0, 1) the factor n cancels, which is erdos:166's k^3 <= p * R(4, k) * (trunc_log 2 k)^c with the same c and p." *)
Theorem clique_ramsey_polylog_lower_implies_ramsey_four_cubic_polylog_lower :
  clique_ramsey_polylog_lower_statement -> ramsey_four_cubic_polylog_lower_statement.
Proof.
move=> H; have [c [p [n0 [p0 Hn]]]] := H 4 isT.
exists c, p, (maxn n0 1); split => // k R; rewrite geq_max => /andP [k0 k1] hR.
have := Hn k R k0 hR.
by rewrite expnS mulnAC [_ * k]mulnC -mulnA leq_pmul2l.
Qed.
