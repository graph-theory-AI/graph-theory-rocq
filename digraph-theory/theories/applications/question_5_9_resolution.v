(** Exact connection between the existing k=3 counterexample family and the
    corpus statement of arXiv:2310.04265, Question 5.9 (record __09).
    The construction itself is proved in applications/unified.v. *)
From mathcomp Require Import all_boot.
From Digraph Require Import tournament omegabar critical unified clique_cluster.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Theorem question_5_9_disproved : ~ question_5_9_statement.
Proof.
move=> [ell HQ].
have [T [crit large whole]] := question_5_9_fails_at_k3 (ell 3).
have oT : omegabar T = 3 by have /kcriticalP[E _] := crit; exact: E.
have h3 : (3 <= omegabar T)%N by rewrite oT.
have [S [small high]] := HQ T 3 h3.
have eqS := whole S high.
move: small; rewrite eqS cardsT => small.
have absurd := leq_ltn_trans small large.
by rewrite ltnn in absurd.
Qed.
