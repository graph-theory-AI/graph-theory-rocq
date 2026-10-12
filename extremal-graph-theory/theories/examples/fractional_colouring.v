(** * Extremal.examples.fractional_colouring — public-only client of Extremal.foundations.fractional_colouring

    Imports GTBase ([base], [bfold_colourings]), MathComp and the foundation only; no conjecture or migration
    module.
    - Positive: chi_f(K_1) = 1, chi_f(K_2) = 2 (a (2:1)-colouring, and any (a:b)-colouring of an edge has
      2b <= a), and chi_f = 0 on the empty graph ['K_0].
    - Negative: the value is pinned, so [1] is not chi_f(K_2) and [1] is not chi_f('K_0); and a colouring with
      [b = 0] is no witness (the positive denominator is part of the relation). *)

From GTBase Require Import base bfold_colourings.
From Extremal.foundations Require Import fractional_colouring.
From mathcomp Require Import all_algebra.
Import GRing.Theory Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.

(** ** Positive *)

Example example_K1 : is_fractional_chromatic 'K_1 1.
Proof.
split.
  exists 1%N, 1%N; split=> //; split; last by rewrite divr1.
  exists (fun v : 'K_1 => [set (v : 'I_1)]); split=> [v|x y].
    by rewrite cards1.
  by rewrite (ord1 x) (ord1 y) sg_irrefl.
move=> a b b0 [f hf].
have ba := bfold_colouring_le (ord0 : 'K_1) hf.
by rewrite ler_pdivlMr ?ltr0n // mul1r ler_nat.
Qed.

Example example_K2 : is_fractional_chromatic 'K_2 2.
Proof.
split.
  exists 2%N, 1%N; split=> //; split; last by rewrite divr1.
  exists (fun v : 'K_2 => [set (v : 'I_2)]); split=> [v|x y xy].
    by rewrite cards1.
  by rewrite disjoints1 inE; exact: xy.
move=> a b b0 [f hf].
have e := bfold_colouring_edge hf (isT : (ord0 : 'K_2) -- (ord_max : 'K_2)).
by rewrite ler_pdivlMr ?ltr0n // -natrM ler_nat.
Qed.

Example example_K0 : is_fractional_chromatic 'K_0 0.
Proof. by apply: is_fractional_chromatic_empty; rewrite card_ord. Qed.

(** ** Negative *)

Example example_K2_not_1 : ~ is_fractional_chromatic 'K_2 1.
Proof. by move/(is_fractional_chromatic_unique example_K2). Qed.

Example example_K0_not_1 : ~ is_fractional_chromatic 'K_0 1.
Proof. by move/(is_fractional_chromatic_unique example_K0). Qed.

(** With [b = 0] every map is a b-fold colouring (here [bfold_colouring0] on K_2), yet the minimality clause
    only ranges over [0 < b]: such a colouring does not drag the value below chi_f(K_2) = 2. *)
Example example_b0_not_a_witness :
  bfold_colouring 0 (fun _ : 'K_2 => (set0 : {set 'I_0})) /\ is_fractional_chromatic 'K_2 2.
Proof. by split; [exact: bfold_colouring0 | exact: example_K2]. Qed.
