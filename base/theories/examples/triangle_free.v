(** Downstream use of base's triangle-freeness ([triangle_free]) and its girth bridge, without corpus
    imports: small complete graphs, the 4-cycle, and the size guard of [girth_geq]. *)
From GTBase Require Import base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** The bridge holds on every simple graph. *)
Example girth4_iff (G : sgraph) : girth_geq G 4 <-> triangle_free G.
Proof. exact: girth_geq4_equiv_triangle_free. Qed.

(** Complete graphs on at most two vertices have no triangle, in both readings. *)
Example K0_triangle_free : triangle_free 'K_0 /\ girth_geq 'K_0 4.
Proof. by split; [|apply/girth_geq4_equiv_triangle_free]; case. Qed.

Example K1_triangle_free : triangle_free 'K_1 /\ girth_geq 'K_1 4.
Proof.
have tf : triangle_free 'K_1 by move=> x y z; rewrite (ord1 x) (ord1 y) sg_irrefl.
by split; [|apply/girth_geq4_equiv_triangle_free].
Qed.

Example K2_triangle_free : triangle_free 'K_2 /\ girth_geq 'K_2 4.
Proof.
have tf : triangle_free 'K_2.
  by move=> [[|[|//]] ?] [[|[|//]] ?] [[|[|//]] ?].
by split; [|apply/girth_geq4_equiv_triangle_free].
Qed.

(** The [2 < size c] guard is load-bearing: [K_2] has the size-2 [ucycle] [[:: 0; 1]], which
    [girth_geq] ignores. *)
Example K2_two_cycle : ucycle (--) [:: (ord0 : 'K_2); ord_max].
Proof. by []. Qed.

(** [K_3] is a triangle, so neither reading holds. *)
Example K3_not_triangle_free : ~ triangle_free 'K_3 /\ ~ girth_geq 'K_3 4.
Proof.
have ntf : ~ triangle_free 'K_3.
  by move/(_ ord0 (@Ordinal 3 1 isT) (@Ordinal 3 2 isT)); apply.
by split=> // /girth_geq4_equiv_triangle_free.
Qed.

(** The 4-cycle has no triangle, in both readings. *)
Example C4_triangle_free : triangle_free (cycle_graph 4) /\ girth_geq (cycle_graph 4) 4.
Proof.
have tf : triangle_free (cycle_graph 4).
  by move=> [[|[|[|[|//]]]] ?] [[|[|[|[|//]]]] ?] [[|[|[|[|//]]]] ?].
by split; [|apply/girth_geq4_equiv_triangle_free].
Qed.

Print Assumptions girth4_iff.
Print Assumptions K2_triangle_free.
Print Assumptions K3_not_triangle_free.
Print Assumptions C4_triangle_free.
