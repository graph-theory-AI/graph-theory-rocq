(** * Extremal.examples.fractional_hadwiger — public-only client of Extremal.foundations.fractional_hadwiger

    Imports GTBase [base], MathComp and the foundation only; no conjecture or migration module.
    - Positive: had_f('K_0) = 0 (only the empty family is feasible), had_f(K_1) = 1 and had_f(K_2) = 2 (the
      singletons with weight one, matched by the vertex-count bound).
    - Negative: the value is pinned, so [1] is not had_f(K_2); and a family with an EMPTY branch set is not
      feasible, however its weight is chosen (the wave-E10 repair: before it, one empty branch set carried any
      weight and the LP had no maximum). *)

From GTBase Require Import base.
From Extremal.foundations Require Import fractional_hadwiger.
From mathcomp Require Import all_algebra.
Import GRing.Theory Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.

(** ** Positive *)

Example example_K0 : is_fractional_hadwiger 'K_0 0.
Proof.
split; first by exists 0%N, (fun _ => set0), (fun _ => 0); exact: frac_clique_minor_trivial.
by move=> n B w r' /frac_clique_minor_le_card; rewrite card_ord.
Qed.

Example example_K1 : is_fractional_hadwiger 'K_1 1.
Proof.
split.
  exists 1%N, (fun _ => [set ord0]), (fun _ => 1); split => //.
  - by move=> _; split; [apply/set0Pn; exists ord0; rewrite inE | exact: connected1].
  - by move=> i j; rewrite (ord1 i) (ord1 j) eqxx.
  - by move=> v; rewrite (ord1 v) big_mkcond big_ord1 inE eqxx.
  - by rewrite big_ord1.
by move=> n B w r' /frac_clique_minor_le_card; rewrite card_ord.
Qed.

Example example_K2 : is_fractional_hadwiger 'K_2 2.
Proof.
split.
  exists 2%N, (fun i : 'I_2 => [set (i : 'K_2)]), (fun _ => 1); split => //.
  - by move=> i; split; [apply/set0Pn; exists i; rewrite inE | exact: connected1].
  - by move=> i j ij; exists i, j; rewrite !inE !eqxx.
  - move=> v; rewrite (big_pred1 v) // => i; by rewrite inE eq_sym.
  - by rewrite big_ord_recl big_ord1.
by move=> n B w r' /frac_clique_minor_le_card; rewrite card_ord.
Qed.

(** ** Negative *)

Example example_K2_not_1 : ~ is_fractional_hadwiger 'K_2 1.
Proof. by move/(is_fractional_hadwiger_unique example_K2). Qed.

(** An empty branch set is never feasible (it is connected, adjacent to nothing and covers nothing, so before the
    repair it could carry any weight). *)
Example example_empty_branch_set_infeasible (G : sgraph) (w : 'I_1 -> rat) (r : rat) :
  ~ frac_clique_minor (fun _ : 'I_1 => @set0 G) w r.
Proof. by move/(frac_clique_minor_nonempty ord0); rewrite eqxx. Qed.
