(** Public-only ambient-radius clients. The separation uses a connected six-vertex
    path branch and one extra host vertex adjacent to the whole branch. *)
From GTBase Require Import base.
From mathcomp Require Import zify.
From GTMisc.foundations Require Import ambient_shallow_minors.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Example empty_branch_rejected (G : sgraph) (r : nat) :
  ~ ambient_radius_at_most (set0 : {set G}) r.
Proof. exact: not_ambient_radius_set0. Qed.
Example singleton_radius_zero (G : sgraph) (x : G) :
  ambient_radius_at_most [set x] 0.
Proof. exact: ambient_radius_singleton. Qed.
Example radius_can_increase (G : sgraph) (S : {set G}) (r : nat) :
  ambient_radius_at_most S r -> ambient_radius_at_most S r.+1.
Proof. exact: ambient_radius_at_mostW (leqnSn r). Qed.
Example truncated_radius_for_any_nonempty_set (G : sgraph) (S : {set G}) :
  S != set0 -> ambient_radius_at_most S #|G|.
Proof. exact: ambient_radius_card. Qed.
Example empty_pattern_in_empty_host : ambient_shallow_minor 'K_0 'K_0 0.
Proof. exact: ambient_shallow_minor_empty_pattern. Qed.
Example singleton_not_in_empty_host (r : nat) :
  ~ ambient_shallow_minor 'K_0 'K_1 r.
Proof. exact: (@not_ambient_shallow_minor_empty_host 'K_1 ord0 r). Qed.
Example singleton_model_zero : ambient_shallow_minor 'K_1 'K_1 0.
Proof. exact: ambient_shallow_minor_refl. Qed.
Example edge_model_zero : ambient_shallow_minor 'K_2 'K_2 0.
Proof. exact: ambient_shallow_minor_refl. Qed.
Example model_can_increase (G H : sgraph) (r : nat) :
  ambient_shallow_minor G H r -> ambient_shallow_minor G H r.+1.
Proof. exact: ambient_shallow_minorW (leqnSn r). Qed.
Example ordinary_minor_consequence (G H : sgraph) (r : nat) :
  ambient_shallow_minor G H r -> minor G H.
Proof. exact: ambient_shallow_minor_minor. Qed.

Definition fan7_rel (x y : 'I_7) : bool :=
  (x != y) && (((x == ord_max) || (y == ord_max)) ||
              ((x.+1 == y) || (y.+1 == x))).
Lemma fan7_sym : symmetric fan7_rel.
Proof.
move=> x y; rewrite /fan7_rel eq_sym.
by rewrite (orbC (x == ord_max)) (orbC (x.+1 == y)).
Qed.
Lemma fan7_irrefl : irreflexive fan7_rel.
Proof. by move=> x; rewrite /fan7_rel eqxx. Qed.
Definition fan7 := SGraph fan7_sym fan7_irrefl.
Definition path_branch : {set fan7} := [set x : fan7 | val x < 6].


Definition v0 : fan7 := @Ordinal 7 0 isT.
Definition v1 : fan7 := @Ordinal 7 1 isT.
Definition v2 : fan7 := @Ordinal 7 2 isT.
Definition v3 : fan7 := @Ordinal 7 3 isT.
Definition v4 : fan7 := @Ordinal 7 4 isT.
Definition v5 : fan7 := @Ordinal 7 5 isT.
Definition v6 : fan7 := @Ordinal 7 6 isT.
Lemma edge01 : v0 -- v1. Proof. by vm_compute. Qed.
Lemma edge12 : v1 -- v2. Proof. by vm_compute. Qed.
Lemma edge23 : v2 -- v3. Proof. by vm_compute. Qed.
Lemma edge34 : v3 -- v4. Proof. by vm_compute. Qed.
Lemma edge45 : v4 -- v5. Proof. by vm_compute. Qed.
Definition branch_path : Path v0 v5 :=
  pcat (edgep edge01) (pcat (edgep edge12)
    (pcat (edgep edge23) (pcat (edgep edge34) (edgep edge45)))).

Lemma path_branchE : path_branch = [set x in branch_path].
Proof.
apply/setP=> x; rewrite /path_branch !inE /branch_path !mem_edgep.
case: x => n hn.
do 7! (case: n hn => [|n] hn; first by vm_compute).
by [].
Qed.

Example path_branch_connected : connected path_branch.
Proof. rewrite path_branchE; exact: connected_path. Qed.

Example path_branch_ambient_radius_two : ambient_radius_at_most path_branch 2.
Proof.
exists v0; split; first by rewrite /path_branch inE.
move=> x hx; apply: ambient_graph_dist_ball.
have hub01 : v0 -- v6 by vm_compute.
have hubx : v6 -- x.
  move: hx; rewrite /path_branch inE => hx.
  have nx : (x == v6) = false by exact: ltn_eqF hx.
  by rewrite /edge_rel /= /fan7_rel eq_sym nx /= /v6.
rewrite /= inE; apply/orP; right; apply/bigcupP; exists v6.
- rewrite inE; apply/orP; right; apply/bigcupP; exists v0.
  + by rewrite inE.
  + by rewrite inE.
- by rewrite inE.
Qed.

Lemma fan7_enum : enum fan7 = [:: v0; v1; v2; v3; v4; v5; v6].
Proof. apply: (inj_map val_inj); by rewrite val_enum_ord. Qed.
Lemma path_branch_card : #|path_branch| = 6.
Proof.
rewrite cardE /enum_mem -enumT fan7_enum /path_branch.
by rewrite /= !inE.
Qed.

Lemma internal_step (x y : induced path_branch) : x -- y ->
  val (val x) <= (val (val y)).+1 /\ val (val y) <= (val (val x)).+1.
Proof.
have hx := valP x; have hy := valP y.
move: hx hy; rewrite /path_branch !inE => hx hy.
have nx : (val x == ord_max) = false by exact: ltn_eqF hx.
have ny : (val y == ord_max) = false by exact: ltn_eqF hy.
change (fan7_rel (val x) (val y) -> val (val x) <= (val (val y)).+1 /\ val (val y) <= (val (val x)).+1).
rewrite /fan7_rel nx ny /= => /andP [_ /orP [/eqP e|/eqP e]]; split; lia.
Qed.

Lemma internal_ball_bound (k : nat) (c x : induced path_branch) :
  x \in rel_ball (--) k c ->
  val (val x) <= val (val c) + k /\ val (val c) <= val (val x) + k.
Proof.
elim: k => [|k IH] in x *.
- rewrite /= inE => /eqP ->; split; by rewrite addn0.
- rewrite /= inE => /orP [old|/bigcupP [z hz zx]].
  + have [bx bc] := IH _ old; split; rewrite addnS.
    * exact: leq_trans bx (leqnSn _).
    * exact: leq_trans bc (leqnSn _).
  + have [bz bc] := IH _ hz; move: zx; rewrite inE => zx.
    have [sz sx] := internal_step zx; split.
    * have bzS : (val (val z)).+1 <= (val (val c) + k).+1 by rewrite ltnS.
      rewrite addnS; exact: leq_trans sx bzS.
    * have szk : val (val z) + k <= val (val x) + k.+1 by rewrite addnS -addSn leq_add2r.
      exact: leq_trans bc szk.
Qed.

Lemma v0_in : v0 \in path_branch. Proof. by rewrite /path_branch inE. Qed.
Lemma v5_in : v5 \in path_branch. Proof. by rewrite /path_branch inE. Qed.
Definition i0 : induced path_branch := Sub v0 v0_in.
Definition i5 : induced path_branch := Sub v5 v5_in.

Example path_branch_no_internal_radius_two :
  ~ ambient_radius_at_most ([set: induced path_branch]) 2.
Proof.
have size_eq : #|induced path_branch| = #|path_branch|.
  by rewrite card_sig; apply: eq_card => x; rewrite !inE.
have size_gt2 : 2 < #|induced path_branch| by rewrite size_eq path_branch_card.
move=> [c [_hc bound]].
have ti0 : i0 \in [set: induced path_branch] by rewrite inE.
have ti5 : i5 \in [set: induced path_branch] by rewrite inE.
have b0 := bound i0 ti0; have b5 := bound i5 ti5.
rewrite (@ambient_graph_dist_smallE (induced path_branch) c i0 2 size_gt2) in b0.
rewrite (@ambient_graph_dist_smallE (induced path_branch) c i5 2 size_gt2) in b5.
have [_ c0] := @internal_ball_bound 2 c i0 b0.
have [c5 _] := @internal_ball_bound 2 c i5 b5.
move: c0 c5; rewrite /i0 /i5 /v0 /v5 /= add0n => c0 c5.
have bad := leq_trans c5 (leq_add c0 (leqnn 2)).
by move: bad.
Qed.

Example ambient_and_internal_radius_differ :
  connected path_branch /\ ambient_radius_at_most path_branch 2 /\
  ~ ambient_radius_at_most ([set: induced path_branch]) 2.
Proof.
split; first exact: path_branch_connected.
split; [exact: path_branch_ambient_radius_two | exact: path_branch_no_internal_radius_two].
Qed.
