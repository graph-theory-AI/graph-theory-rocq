(** * Chromatic.foundations.forest_paths -- every path of a forest is induced

    ONE graph-theoretic fact, needed by the X218 edge
    [polynomial_gyarfas_sumner_tree ==> path_induced_rooted_tree_polynomial_chi_bound]
    (corpus relation e041) and not available in coq-graph-theory:

      in a FOREST, two NON-CONSECUTIVE vertices of a uniq path are non-adjacent,

    i.e. every path of a forest is an induced path.  The argument is the standard
    one: a chord between two vertices at distance at least two along the path
    would give TWO distinct irredundant paths between its ends (the segment of
    the path, of at least two edges, and the chord itself), contradicting
    [forestT_unique].

    The statement is packaged in the "run" form used by [X218.x218_induced_run]:
    [~~ (nth x0 (x :: s) i -- nth x0 (x :: s) j)] for [i.+1 < j], with an
    arbitrary [nth] default, since all indices involved are in range. *)

From GTBase Require Import base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** [nth] does not depend on its default inside the range. *)
Lemma nth_defaultE (A : Type) (u : seq A) (a b : A) (n : nat) :
  n < size u -> nth a u n = nth b u n.
Proof. exact: set_nth_default. Qed.

Section ForestPaths.
Variable T : sgraph.
Hypothesis Tf : is_forest [set: T].

(** The two ENDS of a uniq path with at least two edges are non-adjacent. *)
Lemma forest_last_nonadj (x : T) (s : seq T) :
  path (--) x s -> uniq (x :: s) -> 2 <= size s -> ~~ (x -- last x s).
Proof.
move=> pth uq sz; apply/negP => xy.
have irr1 : irred (Path_of_path pth) by rewrite irredE nodesE; exact: uq.
have irr2 : irred (edgep xy) by exact: irred_edge.
have e := forestT_unique Tf irr1 irr2.
move: sz; rewrite (_ : s = [:: last x s]) //.
by move: e => /(f_equal val).
Qed.

(** The HEAD of a uniq path is non-adjacent to every later vertex except the
    first one: the [j]-th vertex of the tail is at distance [j.+1 >= 2]. *)
Lemma forest_head_nonadj (x x0 : T) (s : seq T) (j : nat) :
  path (--) x s -> uniq (x :: s) -> j < size s -> 1 <= j ->
  ~~ (x -- nth x0 s j).
Proof.
move=> pth uq hj j1.
have hle : j.+1 <= size s by exact: hj.
have E : nth x0 s j = last x (take j.+1 s).
  rewrite -nth_last (size_takel hle) /= nth_take //.
  exact: nth_defaultE hj.
rewrite E; apply: forest_last_nonadj.
- by move: pth; rewrite -{1}(cat_take_drop j.+1 s) cat_path => /andP[].
- rewrite cons_uniq; apply/andP; split.
    move: uq; rewrite cons_uniq => /andP[xs _].
    by apply/negP => /mem_take hin; exact: (negP xs hin).
  apply: take_uniq; by move: uq; rewrite cons_uniq => /andP[].
- by rewrite (size_takel hle).
Qed.

(** Every path of a forest is INDUCED: no two non-consecutive vertices of a
    uniq path are adjacent. *)
Lemma forest_run_nonadj (s : seq T) (x x0 : T) (i j : nat) :
  path (--) x s -> uniq (x :: s) -> j < (size s).+1 -> i.+1 < j ->
  ~~ (nth x0 (x :: s) i -- nth x0 (x :: s) j).
Proof.
elim: s x i j => [|z s IH] x i j pth uq hj hij.
  by move: hj hij; rewrite ltnS leqn0 => /eqP ->; rewrite ltn0.
case: j hj hij => [|j] hj hij; first by rewrite ltn0 in hij.
have hjs : j < (size s).+1 by move: hj; rewrite /= !ltnS.
case: i hij => [|i] hij /=.
  have j1 : 1 <= j by move: hij; rewrite ltnS.
  exact: forest_head_nonadj pth uq hjs j1.
have pthz : path (--) z s by move: pth => /andP[].
have uqz : uniq (z :: s) by move: uq; rewrite cons_uniq => /andP[].
have hij' : i.+1 < j by move: hij; rewrite ltnS.
exact: IH z i j pthz uqz hjs hij'.
Qed.

End ForestPaths.

Print Assumptions forest_last_nonadj.
Print Assumptions forest_head_nonadj.
Print Assumptions forest_run_nonadj.
