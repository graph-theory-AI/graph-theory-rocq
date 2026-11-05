(** * Minor.conjectures.grounding_X291 -- grounding lemmas for wave X291.

    Qed-closed, axiom-free certificates for the row of [X291.v] in X271's claim shape (hyp_inhabited,
    not_trivially_true, helper_sanity).  [g291_union_edge] shows that the source's edge between two bags follows from
    their connected union; [g291_small_t] shows that the instances t = 0 and t = 1 of the row hold.  They validate
    the statement; they do not prove it (it is false for large t, arXiv:2103.10684v2 l.187-189). *)

From GraphTheory Require Import preliminaries digraph sgraph minor.
From GTBase Require Import base path_graphs.
From Minor.conjectures Require Import X291.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* The source's edge between two bags follows from the connectivity of their union. *)
Lemma g291_union_edge (G : sgraph) (A B : {set G}) :
  A != set0 -> B != set0 -> [disjoint A & B] -> connected (A :|: B) ->
  exists x y, [/\ x \in A, y \in B & x -- y].
Proof.
case/set0Pn => a aA; case/set0Pn => b bB dAB cAB.
have [/neighborP [x [y [xA yB xy]]] | noedge] := boolP (neighbor A B); first by exists x, y.
exfalso.
have cl : closed (restrict (A :|: B) sedge) A.
  move=> x y /andP [/andP [xU yU] xy]; apply/idP/idP => [xA | yA].
    apply: contraT => yA; case/negP: noedge; apply/neighborP; exists x, y; split=> //.
    by move: yU; rewrite inE (negbTE yA).
  apply: contraT => xA; case/negP: noedge; apply/neighborP; exists y, x; split=> //.
    by move: xU; rewrite inE (negbTE xA).
  by rewrite sgP.
have ab : connect (restrict (A :|: B) sedge) a b.
  by apply: cAB; rewrite inE ?aA ?bB ?orbT.
have := closed_connect cl ab; rewrite aA => /esym bA.
have := disjointFr dAB bA; by rewrite bB.
Qed.

(* Two distinct non-adjacent vertices do not form a connected set. *)
Lemma g291_pair_disconnected (G : sgraph) (x y : G) :
  x != y -> ~~ x -- y -> ~ connected [set x; y].
Proof.
move=> xy nxy c.
have cl : closed (restrict [set x; y] sedge) [set x].
  move=> u v /andP [/andP [uS vS] uv]; move: uS vS uv; rewrite !inE.
  case/orP => /eqP -> ; case/orP => /eqP -> => e;
    [by rewrite sg_irrefl in e | by rewrite (negbTE nxy) in e
    | by rewrite sgP (negbTE nxy) in e | by rewrite sg_irrefl in e].
have xS : x \in [set x; y] by rewrite !inE eqxx.
have yS : y \in [set x; y] by rewrite !inE eqxx orbT.
have := closed_connect cl (c x y xS yS).
rewrite !inE eqxx eq_sym => /esym /eqP e; by rewrite e eqxx in xy.
Qed.

Section P4.
Local Notation P4 := (ordinal_path 4).
Let v0 : P4 := @Ordinal 4 0 isT.
Let v1 : P4 := @Ordinal 4 1 isT.
Let v2 : P4 := @Ordinal 4 2 isT.
Let v3 : P4 := @Ordinal 4 3 isT.

Definition g291_p4_bags (i : 'I_2) : {set P4} :=
  if val i == 0 then [set v0; v2] else [set v1; v3].

Lemma g291_p4_bags_union : g291_p4_bags ord0 :|: g291_p4_bags ord_max = [set: P4].
Proof.
apply/setP => x; rewrite /g291_p4_bags /= !inE.
by case: x => [[|[|[|[|m]]]] Hm].
Qed.

Lemma g291_p4_quasi : x291_quasi_complete_minor P4 2.
Proof.
exists g291_p4_bags; split.
- move=> i; apply/set0Pn; rewrite /g291_p4_bags.
  by case: (val i == 0); [exists v0 | exists v1]; rewrite !inE eqxx.
- move=> [[|[|m]] Hi] [[|[|n]] Hj] //= _; rewrite /g291_p4_bags /=.
  + apply/disjointP => x; rewrite !inE.
    by case/orP => /eqP ->.
  + apply/disjointP => x; rewrite !inE.
    by case/orP => /eqP ->.
- move=> [[|[|m]] Hi] [[|[|n]] Hj] //= _.
  + have -> : Ordinal Hi = ord0 :> 'I_2 by apply: val_inj.
    have -> : Ordinal Hj = ord_max :> 'I_2 by apply: val_inj.
    by rewrite g291_p4_bags_union; exact: ordinal_path_connected.
  + have -> : Ordinal Hi = ord_max :> 'I_2 by apply: val_inj.
    have -> : Ordinal Hj = ord0 :> 'I_2 by apply: val_inj.
    by rewrite setUC g291_p4_bags_union; exact: ordinal_path_connected.
Qed.

(* Each bag is disconnected: the quasi-minor is not a minor model. *)
Lemma g291_p4_bag_disconnected (i : 'I_2) : ~ connected (g291_p4_bags i).
Proof.
rewrite /g291_p4_bags; case: (val i == 0); apply: g291_pair_disconnected => //;
  by rewrite ordinal_path4_edgeE.
Qed.
End P4.

Definition g291_lvm_hyp_claim : Prop :=
  [/\ x291_quasi_complete_minor (ordinal_path 4) 2,
      (forall i : 'I_2, ~ connected (g291_p4_bags i)) &
      (las_vergnas_meyniel_quasi_minor_statement -> minor (ordinal_path 4) 'K_2)].

Theorem g291_lvm_hyp_inhabited : g291_lvm_hyp_claim.
Proof.
split; [exact: g291_p4_quasi | exact: g291_p4_bag_disconnected |].
by move=> h; exact: h _ _ g291_p4_quasi.
Qed.

Definition g291_lvm_disjoint_bags_only : Prop :=
  forall (t : nat) (G : sgraph),
    (exists B : 'I_t -> {set G},
       (forall i, B i != set0) /\ (forall i j, i != j -> [disjoint B i & B j])) ->
    minor G 'K_t.

Definition g291_lvm_ntt_claim : Prop :=
  ~ g291_lvm_disjoint_bags_only /\
  (g291_lvm_disjoint_bags_only -> las_vergnas_meyniel_quasi_minor_statement).

Theorem g291_lvm_not_trivially_true : g291_lvm_ntt_claim.
Proof.
split.
- move=> h; apply: (@ordinal_path_K3_free 3); apply: h.
  exists (fun i : 'I_3 => [set (i : ordinal_path 3)]); split.
  + by move=> i; apply/set0Pn; exists i; rewrite inE.
  + by move=> i j ij; rewrite disjoint_sym disjoints1 inE eq_sym.
- move=> h t G [B [B0 BD _]]; apply: h; exists B; split=> //.
Qed.

(* Helper sanity: every K_t minor model is a quasi-K_t-minor; K_1 has no quasi-K_2-minor. *)
Definition g291_helper_claim : Prop :=
  [/\ (forall (G : sgraph) (t : nat), minor G 'K_t -> x291_quasi_complete_minor G t),
      ~ x291_quasi_complete_minor 'K_1 2 &
      x291_quasi_complete_minor (ordinal_path 4) 2].

Theorem g291_helper_sanity : g291_helper_claim.
Proof.
split; last exact: g291_p4_quasi.
- move=> G t /minorRE [phi [phi0 phiC phiD phiN]].
  exists phi; split=> // i j ij.
  have /neighborP [x [y [xi yj xy]]] : neighbor (phi i) (phi j) by apply: phiN; rewrite /edge_rel /= ij.
  exact: connectedU_edge xi yj xy (phiC i) (phiC j).
- case=> B [B0 BD _].
  have /set0Pn [x xB] := B0 ord0.
  have /set0Pn [y yB] := B0 ord_max.
  have e : x = y by rewrite (ord1 x) (ord1 y).
  have := disjointFr (BD ord0 ord_max isT) xB.
  by rewrite e yB.
Qed.

(* The degenerate instances t = 0 and t = 1 of the row hold. *)
Lemma g291_small_t (G : sgraph) (t : nat) :
  t <= 1 -> x291_quasi_complete_minor G t -> minor G 'K_t.
Proof.
case: t => [_ _ | [_ [B [B0 _ _]] | //]].
- apply: (@minor_of_rmap _ _ (fun _ => set0)); split; by case.
- have /set0Pn [v _] := B0 ord0.
  apply: (@minor_of_rmap _ _ (fun _ => [set v])); split.
  + by move=> i; apply/set0Pn; exists v; rewrite inE.
  + by move=> i; exact: connected1.
  + by move=> i j; rewrite (ord1 i) (ord1 j) eqxx.
  + by move=> i j; rewrite (ord1 i) (ord1 j) sg_irrefl.
Qed.
