(** Downstream use of closed vertex balls and seed-set balls without corpus imports: the zero radius, centre
    membership, monotonicity, the relation-generic specialization, empty/zero/singleton/union seed sets, the empty
    graph, an edgeless host at every radius, and the separation of balls from the truncated graph distance. *)
From GTBase Require Import base balls.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Example ball_basics (G : sgraph) (x : G) (r : nat) :
  [/\ ball 0 x = [set x], x \in ball r x, ball r x \subset ball r.+3 x & ball r x = rel_ball (--) r x].
Proof.
split; [exact: ball0 | exact: ball_center | apply: ball_mono | exact: ball_rel_ballE].
by rewrite -addn3 leq_addr.
Qed.

Example set_ball_views (G : sgraph) (x : G) (S T : {set G}) (r : nat) :
  [/\ set_ball r (set0 : {set G}) = set0, set_ball 0 S = S, set_ball r [set x] = ball r x
    & set_ball r (S :|: T) = set_ball r S :|: set_ball r T].
Proof. by split; [exact: set_ball_set0 | exact: set_ball0 | exact: set_ball1 | exact: set_ballU]. Qed.

(** The empty graph: every seed-set ball is empty, at every radius. *)
Example K0_set_ball (r : nat) (S : {set 'K_0}) : set_ball r S = set0.
Proof. by apply/setP => -[]. Qed.

(** An edgeless host: every ball is its centre, at every radius. *)
Definition edgeless (n : nat) : sgraph :=
  @SGraph 'I_n (fun _ _ => false) (fun _ _ => erefl) (fun _ => erefl).

Example edgeless_ball (n r : nat) (x : edgeless n) : ball r x = [set x].
Proof.
elim: r => [//|r IH]; rewrite ballS IH big_set1.
by apply/setP => y; rewrite in_setU in_opn /= orbF.
Qed.

(** A disconnected host separates balls from the truncated distance: the two vertices of [edgeless 2] are at
    truncated distance [#|G| = 2], so [graph_dist x y <= r] for every [r >= 2], yet [y] is in no ball around [x]. *)
Example ball_vs_graph_dist :
  graph_dist (ord0 : edgeless 2) ord_max = 2 /\
  forall r : nat, (ord_max : edgeless 2) \notin ball r (ord0 : edgeless 2).
Proof.
have nb r : (ord_max : edgeless 2) \notin ball r (ord0 : edgeless 2) by rewrite edgeless_ball inE.
split=> //; rewrite /graph_dist; case: ex_minnP => m.
have -> : #|edgeless 2| = 2 by exact: card_ord.
by rewrite -ball_rel_ballE (negbTE (nb m)) /= => /eqP.
Qed.

Print Assumptions ball_basics.
Print Assumptions set_ball_views.
Print Assumptions K0_set_ball.
Print Assumptions edgeless_ball.
Print Assumptions ball_vs_graph_dist.
