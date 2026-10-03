(** Downstream use of the whole-graph clique number [ω([set: G])] (upstream [omega_mem]) and of its bigmax
    presentation [omega_setT_maxE], without corpus imports: the empty, one-vertex, complete and edgeless
    corners, as exact natural numbers. *)
From GTBase Require Import base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** The bigmax over all cliques is the clique number, with no nonempty guard. *)
Example bigmax_presentation (G : sgraph) :
  \max_(S : {set G} | cliqueb S) #|S| = ω([set: G]).
Proof. by rewrite omega_setT_maxE. Qed.

(** The clique number never exceeds the order. *)
Example omega_le_order (G : sgraph) : ω([set: G]) <= #|G|.
Proof. by rewrite omega_setT_maxE; apply/bigmax_leqP => S _; exact: max_card. Qed.

(** Complete graphs: [K_n] has clique number exactly [n]. *)
Example Kn_omega (n : nat) : ω([set: 'K_n]) = n.
Proof.
apply/eqP; rewrite eqn_leq; apply/andP; split.
  by have := omega_le_order 'K_n; rewrite card_ord.
have cl : [set: 'K_n] \in cliques [set: 'K_n].
  by rewrite !inE subsetT /=; apply/cliqueP => x y _ _.
by have := clique_bound cl; rewrite cardsT card_ord.
Qed.

Example K0_omega : ω([set: 'K_0]) = 0.
Proof. exact: Kn_omega. Qed.

Example K1_omega : ω([set: 'K_1]) = 1.
Proof. exact: Kn_omega. Qed.

(** An edgeless graph on [n.+1] vertices: every clique has at most one vertex, and a vertex is a clique. *)
Definition edgeless (n : nat) : sgraph :=
  @SGraph 'I_n (fun _ _ => false) (fun _ _ => erefl) (fun _ => erefl).

Example edgeless_omega (n : nat) : ω([set: edgeless n.+1]) = 1.
Proof.
apply/eqP; rewrite eqn_leq; apply/andP; split.
  rewrite omega_setT_maxE; apply/bigmax_leqP => S /cliqueP clS.
  rewrite leqNgt; apply/negP => /card_gt1P[x [y [xS yS xy]]].
  by have := clS x y xS yS xy.
have cl : [set (ord0 : edgeless n.+1)] \in cliques [set: edgeless n.+1].
  by rewrite !inE subsetT /=; apply/cliqueP; apply: small_clique; rewrite cards1.
by have := clique_bound cl; rewrite cards1.
Qed.

Print Assumptions bigmax_presentation.
Print Assumptions Kn_omega.
Print Assumptions edgeless_omega.
