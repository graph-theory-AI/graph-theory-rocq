(** Public-only internal-radius clients.  They import only GTBase and the public
    Minor foundation.  The disconnected example is the two left vertices of the
    upstream complete bipartite graph [KB 2 2]: no centre and no radius make them
    an internal ball, while the truncated [graph_dist] of their induced subgraph
    accepts every pair at the cardinality bound.  At the model level, ['K_3] is an
    internal 1-shallow minor of [KB 2 2] but not a 0-shallow minor. *)
From GTBase Require Import base.
From Minor.foundations Require Import shallow_minors.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Standalone balls: empty-set vacuity and a separate centre *)

Example empty_ball_any_centre (G : sgraph) (c : G) (r : nat) :
  internal_ball_in (set0 : {set G}) c r /\ c \notin (set0 : {set G}).
Proof. by split; [exact: internal_ball_in_set0 | rewrite inE]. Qed.

Example nonempty_ball_contains_centre (G : sgraph) (B : {set G}) (c v : G) (r : nat) :
  v \in B -> internal_ball_in B c r -> c \in B.
Proof. exact: internal_ball_in_centre. Qed.

Example ball_can_increase (G : sgraph) (B : {set G}) (c : G) (r : nat) :
  internal_ball_in B c r -> internal_ball_in B c r.+1.
Proof. exact: internal_ball_inW (leqnSn r). Qed.

(** ** Zero radius *)

Example singleton_radius_zero (G : sgraph) (x : G) :
  internal_ball_in [set x] x 0.
Proof. exact: internal_ball_in_set1. Qed.

Example zero_radius_is_singleton (G : sgraph) (B : {set G}) (c : G) :
  internal_ball_in B c 0 -> B \subset [set c].
Proof. exact: internal_ball_in0. Qed.

Example edge_radius_one : internal_ball_in [set: 'K_2] ord0 1.
Proof.
move=> v _; have [->|nv] := eqVneq v ord0.
  by exists [::]; split=> //=; rewrite inE.
exists [:: v]; split=> //=; last by rewrite !inE.
by rewrite andbT; move: nv; rewrite eq_sym.
Qed.

Example edge_not_radius_zero (c : 'K_2) : ~ internal_ball_in [set: 'K_2] c 0.
Proof.
move=> /internal_ball_in0 /subsetP sub.
have := sub ord0 (in_setT _); have := sub ord_max (in_setT _).
by rewrite !inE => /eqP <- /eqP.
Qed.

Example zero_radius_models_are_subgraphs (G H : sgraph) :
  internal_shallow_minor G H 0 <-> has_subgraph G H.
Proof. exact: internal_shallow_minor0E. Qed.

Example edge_model_zero : internal_shallow_minor 'K_2 'K_2 0.
Proof. exact: internal_shallow_minor_refl. Qed.

(** ** Empty pattern and empty host *)

Example empty_pattern_in_empty_host : internal_shallow_minor 'K_0 'K_0 0.
Proof. exact: internal_shallow_minor_empty_pattern. Qed.

Example singleton_not_in_empty_host (r : nat) : ~ internal_shallow_minor 'K_0 'K_1 r.
Proof. exact: (@not_internal_shallow_minor_empty_host 'K_1 ord0 r). Qed.

Example model_can_increase (G H : sgraph) (r : nat) :
  internal_shallow_minor G H r -> internal_shallow_minor G H r.+1.
Proof. exact: internal_shallow_minorW (leqnSn r). Qed.

Example ordinary_minor_consequence (G H : sgraph) (r : nat) :
  internal_shallow_minor G H r -> minor G H.
Proof. exact: internal_shallow_minor_minor. Qed.

(** ** A disconnected branch, and the truncated host metric *)

Definition l0 : KB 2 2 := inl ord0.
Definition l1 : KB 2 2 := inl ord_max.
Definition r0 : KB 2 2 := inr ord0.
Definition r1 : KB 2 2 := inr ord_max.
Definition left2 : {set KB 2 2} := [set l0; l1].

Lemma left2_no_inner_edge (x y : KB 2 2) : x \in left2 -> y \in left2 -> ~~ (x -- y).
Proof. by rewrite !inE => /orP [] /eqP -> /orP [] /eqP ->. Qed.

Lemma l0_in : l0 \in left2. Proof. by rewrite !inE eqxx. Qed.
Lemma l1_in : l1 \in left2. Proof. by rewrite !inE eqxx orbT. Qed.

Example left2_disconnected : ~ connected left2.
Proof.
move=> con; have /connectP [[|y p] /= pth lst] := con l0 l1 l0_in l1_in.
  by move: lst.
move: pth => /andP [/andP [/andP [_ yB] e] _].
by move: e; rewrite (negbTE (left2_no_inner_edge l0_in yB)).
Qed.

Example disconnected_branch_fails (c : KB 2 2) (r : nat) : ~ internal_ball_in left2 c r.
Proof. exact: not_internal_ball_in_disconnected left2_disconnected. Qed.

Example truncated_metric_does_not_detect_disconnection :
  (forall x y : induced left2, graph_dist x y <= #|induced left2|) /\
  forall (c : KB 2 2) (r : nat), ~ internal_ball_in left2 c r.
Proof.
split; last exact: disconnected_branch_fails.
move=> x y; rewrite /graph_dist; case: ex_minnP => m _ minm.
by apply: minm; rewrite eqxx orbT.
Qed.

(** ** Radius one versus radius zero for models *)

Definition o1 : 'K_3 := Ordinal (isT : 1 < 3).
Definition k3_ctr (x : 'K_3) : KB 2 2 :=
  match val x with 0 => l0 | 1 => l1 | _ => r1 end.
Definition k3_branch (x : 'K_3) : {set KB 2 2} :=
  match val x with 0 => [set l0; r0] | 1 => [set l1] | _ => [set r1] end.

Lemma k3_ctr_in (x : 'K_3) : k3_ctr x \in k3_branch x.
Proof. by case: x => [[|[|m]] hx]; rewrite /k3_ctr /k3_branch /= !inE eqxx. Qed.

Lemma k3_branch_connected (x : 'K_3) : connected (k3_branch x).
Proof.
case: x => [[|[|m]] hx]; rewrite /k3_branch /=; last exact: connected1.
- exact: connected2.
- exact: connected1.
Qed.

Lemma k3_branch_disjoint (x y : 'K_3) : x != y -> [disjoint k3_branch x & k3_branch y].
Proof.
case: x y => [[|[|[|m]]] hx] [[|[|[|n]]] hy] // xy; rewrite /k3_branch /=;
  first [rewrite disjoints1 | rewrite disjoint_sym disjoints1]; by rewrite !inE.
Qed.

Lemma k3_branch_edge (x y : 'K_3) : x -- y -> neighbor (k3_branch x) (k3_branch y).
Proof.
move=> xy; apply/neighborP.
case: x y xy => [[|[|[|m]]] hx] [[|[|[|n]]] hy] // xy; rewrite /k3_branch /=.
- by exists r0, l1; rewrite !inE eqxx ?orbT.
- by exists l0, r1; rewrite !inE eqxx.
- by exists l1, r0; rewrite !inE eqxx ?orbT.
- by exists l1, r1; rewrite !inE eqxx.
- by exists r1, l0; rewrite !inE eqxx.
- by exists r1, l1; rewrite !inE eqxx.
Qed.

Lemma k3_ball (x : 'K_3) : internal_ball_in (k3_branch x) (k3_ctr x) 1.
Proof.
case: x => [[|[|m]] hx]; rewrite /k3_branch /k3_ctr /=; try exact: internal_ball_in_set1.
move=> v; rewrite !inE => /orP [] /eqP ->.
- by exists [::]; split=> //=; rewrite !inE eqxx.
- by exists [:: r0]; split=> //=; rewrite !inE eqxx ?orbT.
Qed.

Example k3_one_shallow_in_kb22 : internal_shallow_minor (KB 2 2) 'K_3 1.
Proof.
exists k3_branch, k3_ctr; split; last exact: k3_ball.
- split.
  + by move=> x; apply/set0Pn; exists (k3_ctr x); exact: k3_ctr_in.
  + exact: k3_branch_connected.
  + exact: k3_branch_disjoint.
  + exact: k3_branch_edge.
- exact: k3_ctr_in.
Qed.

Example k3_not_zero_shallow_in_kb22 : ~ internal_shallow_minor (KB 2 2) 'K_3 0.
Proof.
move=> /internal_shallow_minor0E /has_subgraphP [f [_ hom]].
move: (hom ord0 o1 isT) (hom o1 ord_max isT) (hom ord0 ord_max isT).
by case: (f ord0) => ?; case: (f o1) => ?; case: (f ord_max) => ?.
Qed.
