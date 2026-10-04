(** * GTBase.balls -- closed vertex balls and seed-set balls

    The vertex canonical is the existing [GTBase.base.ball r x], unchanged: radius 0 is [[set x]] and each step adds
    the neighbours of the previous ball ([ball0], [ballS], [ball_center] in [GTBase.base]).  This module names the
    seed-set ball [set_ball r S], the union of the r-balls over a supplied seed set, and proves the basic API:
    monotonicity in the radius, the exact specialization [ball r x = rel_ball (--) r x] of
    [GTBase.graph_metric.rel_ball], and the empty, zero, singleton, union and monotone views of [set_ball].  No
    connectedness, nonemptiness or radius guard is involved.  A ball never leaves the centre's component, while
    [graph_dist] is truncated at [#|G|] for unreachable pairs, so [ball r x] and the vertices at truncated distance at
    most [r] differ once [r >= #|G|] on a disconnected graph; no unconditional distance bridge is stated.  The
    ambient [radius_at_most] (C16/C23), the internal [ball_in] (C18) and the relation-generic [rel_ball] are other
    contracts.
    Registry: meta/library_primitives/ball.json (A22). *)
From GTBase Require Import base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Balls.
Variable G : sgraph.
Implicit Types (x y : G) (S T : {set G}).

(** The union of the closed r-balls around the vertices of a supplied seed set. *)
Definition set_ball (r : nat) S : {set G} := \bigcup_(x in S) ball r x.

(** One more radius step keeps the ball. *)
Lemma ball_succ_sub (r : nat) x : ball r x \subset ball r.+1 x.
Proof. by rewrite ballS subsetUl. Qed.

Lemma ball_mono (r s : nat) x : r <= s -> ball r x \subset ball s x.
Proof.
elim: s => [|s IH]; first by rewrite leqn0 => /eqP ->.
rewrite leq_eqVlt => /orP [/eqP -> //|]; rewrite ltnS => rs.
exact: subset_trans (IH rs) (ball_succ_sub s x).
Qed.

(** The exact simple-graph specialization of the relation-generic ball. *)
Lemma ball_rel_ballE (r : nat) x : ball r x = rel_ball (--) r x.
Proof. by elim: r => //= r ->. Qed.

Lemma in_set_ball (r : nat) S y : (y \in set_ball r S) = [exists x in S, y \in ball r x].
Proof. by apply/bigcupP/exists_inP => -[x xS yx]; exists x. Qed.

Lemma set_ball0 S : set_ball 0 S = S.
Proof.
apply/setP => y; rewrite in_set_ball; apply/exists_inP/idP => [[x xS]|yS].
  by rewrite ball0 => /set1P ->.
by exists y; rewrite ?ball0 ?set11.
Qed.

Lemma set_ball_set0 (r : nat) : set_ball r set0 = set0.
Proof. by rewrite /set_ball big_set0. Qed.

Lemma set_ball1 (r : nat) x : set_ball r [set x] = ball r x.
Proof. by rewrite /set_ball big_set1. Qed.

Lemma set_ballU (r : nat) S T : set_ball r (S :|: T) = set_ball r S :|: set_ball r T.
Proof. by rewrite /set_ball bigcup_setU. Qed.

(** Every seed belongs to its seed-set ball. *)
Lemma set_ball_sub (r : nat) S : S \subset set_ball r S.
Proof. by apply/subsetP => x xS; apply/bigcupP; exists x => //; exact: ball_center. Qed.

Lemma set_ball_subset (r : nat) S T : S \subset T -> set_ball r S \subset set_ball r T.
Proof.
by move=> ST; apply/subsetP => y /bigcupP [x xS yx]; apply/bigcupP; exists x => //; exact: (subsetP ST).
Qed.

Lemma set_ball_mono (r s : nat) S : r <= s -> set_ball r S \subset set_ball s S.
Proof.
move=> rs; apply/subsetP => y /bigcupP [x xS yx]; apply/bigcupP; exists x => //.
exact: (subsetP (ball_mono x rs)).
Qed.

End Balls.
