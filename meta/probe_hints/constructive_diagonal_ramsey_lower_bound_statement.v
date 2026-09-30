(** Faithfulness probe (second reader, 2026-09-23): the BLOCKED placeholder body of
    bm:bm-037 is not merely "a known theorem instead of the open problem" -- it is
    axiom-free REFUTABLE.  Its guard [0 < k] admits k = 1, where the inequality
    r(1,1) >= c^1 = c > 1 is false: r(1,1) = 1 and K_1 already arrows K_1.
    Taking N = 1, k = 1 the hypothesis [N * q ^ k < p ^ k] is exactly [q < p],
    which the statement itself asserts, so the placeholder demands
    [~ x215_arrows 1 1] -- contradicting the Qed lemma [x215_arrows_1_1] that
    wave X215's own grounding file proves.  Fix: restrict the placeholder to
    [1 < k] (Erdos' bound holds for k >= 2 with c <= sqrt 2). *)
From GTBase Require Export base.
From Extremal.conjectures Require Import X215 grounding_X215.

Set Implicit Arguments.

Lemma refuted : ~ constructive_diagonal_ramsey_lower_bound_statement.
Proof.
case=> p [q [_ qp H]].
apply: (H 1 1 isT _ x215_arrows_1_1).
by rewrite !expn1 mul1n.
Qed.

Print Assumptions refuted.
