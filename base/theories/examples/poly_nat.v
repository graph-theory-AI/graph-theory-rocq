(** Downstream use of the natural Horner evaluation without corpus imports and without the algebra hierarchy: the empty list,
    coefficient order (lowest degree first, a reversed list differs), evaluation at 0, a monomial, trailing zeros,
    monotonicity, the [foldr] shape, and the domination bound with the counterexample showing that its guard [1 <= t] is
    necessary. *)
From mathcomp Require Import all_boot.
From GTBase Require Import poly_nat.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** The empty coefficient list is the zero polynomial at every point. *)
Example horner_empty (x : nat) : horner_nat [::] x = 0.
Proof. exact: horner_nat_nil. Qed.

(** Lowest degree first: [1 + 2 x + 3 x^2] at 10 is 321; the reversed list is another polynomial (123). *)
Example horner_order :
  horner_nat [:: 1; 2; 3] 10 = 321 /\ horner_nat [:: 3; 2; 1] 10 = 123 /\ horner_nat [:: 3; 2; 1] 10 != 321.
Proof. by rewrite !horner_nat_cons horner_nat_nil. Qed.

(** At 0 the value is the constant coefficient; [d] zeros then [c] is the monomial [c t^d]; trailing zeros are harmless. *)
Example horner_corners (a c d t x : nat) (p : seq nat) :
  [/\ horner_nat (a :: p) 0 = a, horner_nat (nseq d 0 ++ [:: c]) t = c * t ^ d & horner_nat (rcons p 0) x = horner_nat p x].
Proof. by rewrite horner_nat_x0 horner_nat_monomial horner_nat_rcons0. Qed.

(** Monotone in the point, and the [foldr] shape. *)
Example horner_mono_foldr (p : seq nat) (a b x : nat) :
  a <= b -> horner_nat p a <= horner_nat p b /\ horner_nat p x = foldr (fun c r => c + x * r) 0 p.
Proof. by move=> ab; split; [exact: horner_nat_mono | exact: horner_nat_foldr]. Qed.

(** Domination for [1 <= t]; at [t = 0] it fails for [[:: 1; 1]] (value 1, bound 0), so the guard cannot be dropped. *)
Example horner_dom (p : seq nat) (t : nat) :
  1 <= t -> horner_nat p t <= (\sum_(i <- p) i) * t ^ (size p).-1.
Proof. exact: horner_nat_dom. Qed.

Example horner_dom_guard :
  ~~ (horner_nat [:: 1; 1] 0 <= (\sum_(i <- [:: 1; 1]) i) * 0 ^ (size [:: 1; 1]).-1).
Proof. by rewrite !horner_nat_cons horner_nat_nil big_cons big_seq1. Qed.

Print Assumptions horner_empty.
Print Assumptions horner_order.
Print Assumptions horner_corners.
Print Assumptions horner_mono_foldr.
Print Assumptions horner_dom.
Print Assumptions horner_dom_guard.
