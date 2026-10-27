(** * Extremal.conjectures.implications_X242 -- dependency-graph EDGES unlocked by wave X242.

    Machine-checked implication edges with an X242 endpoint.  Every SCHEDULED edge is a
    RELATIVE theorem: a [Qed]-closed [Theorem A -> B] proved WITHOUT resolving either
    endpoint.  Axiom-free: no [Axiom] / [Parameter] / [Admitted] / [Conjecture].

    The edge below is a Rocq-only edge (no corpus relation): X242.v's Notes say that at
    j = 0 the family and the arithmetic of erdos:574 (ex(n; {C_{2k-1}, C_{2k}}) ~
    (n/2)^{1+1/k}, k = j + 2) are X239's erdos:573 (ex(n; {C_3, C_4}) ~ (n/2)^{3/2});
    this file proves the implication 574 => 573. *)

From Extremal.conjectures Require Import D2tur X239 X242.
From GTBase Require Import base common.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** erdos:574 at j = 0 (k = 2) ==> erdos:573 *)

(*@EDGE from=odd_even_cycle_free_turan_asymptotic_statement to=triangle_square_free_turan_asymptotic_statement kind=implies status=verified proved=true proof=odd_even_cycle_free_turan_asymptotic_implies_triangle_square_free_turan_asymptotic note="Rocq-only edge (no corpus relation), stated in X242.v's Notes: erdos:574 at j = 0 (k = 2) is erdos:573 up to conversion: the family {C_{2j+3}, C_{2j+4}} is {C_3, C_4} and the bounds q^(j+2) n^(j+3) <= 2^(j+3) (q+1)^(j+2) m^(j+2) and 2^(j+3) q^(j+2) m^(j+2) <= (q+1)^(j+2) n^(j+3) are 573's with 2^3 = 8." *)
Theorem odd_even_cycle_free_turan_asymptotic_implies_triangle_square_free_turan_asymptotic :
  odd_even_cycle_free_turan_asymptotic_statement -> triangle_square_free_turan_asymptotic_statement.
Proof. move=> H q q1; exact: H 0 q q1. Qed.
