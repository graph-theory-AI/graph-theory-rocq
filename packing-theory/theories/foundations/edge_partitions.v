(** * Packing.foundations.edge_partitions -- indexed partitions of the edge set

    Library migration, batch C family "edge_partition" (meta/LIBRARY_MIGRATION_PLAN.md
    section 15; family document meta/library_primitives/edge-partition.json;
    fidelity fragment meta/foundation_fidelity/edge-partition.json; public client
    theories/examples/edge_partitions.v; certificates theories/migration/edge_partitions.v).

    ** Canonical primitive

    [edge_partition E], for [E : 'I_m -> {set {set G}}], is the corpus notion of
    X15 (arXiv:1611.03196, Conjecture 1.14) and of its X18 consequences: an
    INDEXED family of [m] sets of vertex pairs such that
    - every edge of [G] belongs to some part and every member of a part is an
      edge, as the single equation [(e \in E(G)) = [exists i, e \in E i]]
      for every vertex pair [e];
    - parts at distinct indices are disjoint.

    Contract and degenerate cases, all proved below:
    - a part may be empty, and several parts may be empty at once: the family
      is kept as a function of the index, so repeated empty parts are
      distinguished by their indices ([edge_partition_K2_empty_part]);
    - [m = 0] is allowed and holds exactly for the edgeless graphs
      ([edge_partition0], [edge_partition_K1_0], [not_edge_partition_K2_0]);
    - every edge lies in EXACTLY one part ([edge_partition_uniqP], the
      unique-index count presentation), so two distinct indices never carry the
      same nonempty part ([edge_partition_inj_nonempty],
      [not_edge_partition_K2_duplicate]) and the part sizes add up to the
      number of edges ([card_edge_partition]);
    - a family with a member that is not an edge, such as a loop [[set x]], is
      never an edge partition ([not_edge_partition_non_edge],
      [not_edge_partition_K2_loop]).
    MathComp's set-of-blocks [partition P D] is NOT an unconditional
    substitute: it requires nonempty blocks ([set0 \notin P]) and forgets
    repeated indices, so it is not used here. *)

From GTBase Require Import base common.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition edge_partition (G : sgraph) (m : nat) (E : 'I_m -> {set {set G}}) : Prop :=
  (forall e : {set G}, (e \in E(G)) = [exists i : 'I_m, e \in E i]) /\
  forall i j : 'I_m, i != j -> [disjoint E i & E j].

(** ** Basic API *)

Section API.
Variables (G : sgraph) (m : nat) (E : 'I_m -> {set {set G}}).
Implicit Types (e : {set G}) (i j : 'I_m).

(** Cover: every edge lies in some part. *)
Lemma edge_partition_cover :
  edge_partition E -> forall e, e \in E(G) -> exists i, e \in E i.
Proof.
move=> [cov _] e eG; have := cov e; rewrite eG => /esym/existsP[i ei].
by exists i.
Qed.

(** Every member of a part is an edge. *)
Lemma edge_partition_sub : edge_partition E -> forall i, E i \subset E(G).
Proof.
move=> [cov _] i; apply/subsetP => e ei; rewrite cov; apply/existsP.
by exists i.
Qed.

Lemma edge_partition_disjoint :
  edge_partition E -> forall i j, i != j -> [disjoint E i & E j].
Proof. by case. Qed.

(** The unique-index count presentation: every member of a part is an edge
    and every edge lies in exactly one part. *)
Lemma edge_partition_uniqP :
  edge_partition E <->
  (forall i, E i \subset E(G)) /\
  forall e, e \in E(G) -> #|[set i | e \in E i]| = 1.
Proof.
split=> [part|[sub one]].
- split; first exact: edge_partition_sub.
  move=> e eG; have [i ei] := edge_partition_cover part eG.
  apply/eqP; rewrite eqn_leq; apply/andP; split.
  + apply/card_le1_eqP => i1 i2; rewrite !inE => ei1 ei2.
    have [//|i21] := altP (i2 =P i1).
    by have := edge_partition_disjoint part i21 => /disjointFr/(_ ei2); rewrite ei1.
  + by rewrite card_gt0; apply/set0Pn; exists i; rewrite inE.
- split=> [e|i j ij].
  + apply/idP/existsP => [eG|[i ei]]; last exact: (subsetP (sub i)).
    have: 0 < #|[set i | e \in E i]| by rewrite one.
    by rewrite card_gt0 => /set0Pn[i]; rewrite inE => ei; exists i.
  + rewrite -setI_eq0; apply/eqP/setP => e; rewrite !inE.
    apply/negbTE/negP => /andP[ei ej].
    have eG : e \in E(G) := subsetP (sub i) _ ei.
    have /card_le1_eqP H : #|[set k | e \in E k]| <= 1 by rewrite one.
    by have := H i j; rewrite !inE => /(_ ei ej) ji; move: ij; rewrite ji eqxx.
Qed.

(** Two distinct indices never carry the same nonempty part. *)
Lemma edge_partition_inj_nonempty :
  edge_partition E -> forall i j, E i != set0 -> E i = E j -> i = j.
Proof.
move=> part i j /set0Pn[e ei] eij; apply/eqP; apply/negPn/negP => ij.
by have := edge_partition_disjoint part ij => /disjointFr/(_ ei); rewrite -eij ei.
Qed.

(** The part sizes add up to the number of edges. *)
Lemma card_edge_partition : edge_partition E -> \sum_i #|E i| = #|E(G)|.
Proof.
move=> part.
have ->: E(G) = \bigcup_i E i.
  apply/setP => e; rewrite (proj1 part e).
  by apply/existsP/bigcupP => -[i ei]; exists i.
symmetry; rewrite -sum1_card partition_disjoint_bigcup; last exact: (proj2 part).
by apply: eq_bigr => i _; rewrite sum1_card.
Qed.

(** A member that is not an edge rules the family out. *)
Lemma not_edge_partition_non_edge e i :
  e \in E i -> e \notin E(G) -> ~ edge_partition E.
Proof.
move=> ei /negPf eG [cov _].
have: [exists j : 'I_m, e \in E j] by apply/existsP; exists i.
by rewrite -cov eG.
Qed.

End API.

(** ** Grounding *)

(** [m = 0]: the empty family partitions exactly the edgeless graphs. *)
Lemma edge_partition0 (G : sgraph) (E : 'I_0 -> {set {set G}}) :
  edge_partition E <-> E(G) = set0.
Proof.
split=> [[cov _]|G0].
- apply/setP => e; rewrite cov inE; apply/negbTE/negP => /existsP[i _].
  by have := ltn_ord i; rewrite ltn0.
- split=> [e|i]; last by have := ltn_ord i; rewrite ltn0.
  rewrite G0 inE; apply/esym/negbTE/negP => /existsP[i _].
  by have := ltn_ord i; rewrite ltn0.
Qed.

(** [K_1] is edgeless, so it is partitioned by the empty family; [K_2] is not. *)
Lemma edge_partition_K1_0 (E : 'I_0 -> {set {set 'K_1}}) : edge_partition E.
Proof. by apply/edge_partition0; rewrite sg_edge_set_K1. Qed.

Lemma not_edge_partition_K2_0 (E : 'I_0 -> {set {set 'K_2}}) : ~ edge_partition E.
Proof.
move/edge_partition0=> G0.
have : #|E('K_2)| = 0 by rewrite G0 cards0.
by rewrite card_edge_Kn.
Qed.

(** Put all edges in one designated part; every other part is empty. *)
Lemma edge_partition_single_part (G : sgraph) (m : nat) (i0 : 'I_m) :
  edge_partition (fun i : 'I_m => if i == i0 then E(G) else set0).
Proof.
split=> [e|i j ij].
- apply/idP/existsP => [eG|[i]].
  + by exists i0; rewrite eqxx.
  + by case: ifP => // _; rewrite inE.
- case ei: (i == i0); case ej: (j == i0);
    rewrite -setI_eq0 ?setI0 ?set0I ?eqxx //.
  by move: ij; rewrite (eqP ei) (eqP ej) eqxx.
Qed.

(** A nonempty edge set with TWO repeated empty parts is valid. *)
Definition K2_with_empty_parts (i : 'I_3) : {set {set 'K_2}} :=
  if i == ord0 then E('K_2) else set0.

Lemma edge_partition_K2_empty_part : edge_partition K2_with_empty_parts.
Proof. exact: edge_partition_single_part. Qed.

Lemma K2_repeated_empty_parts :
  K2_with_empty_parts (@Ordinal 3 1 isT) = set0 /\
  K2_with_empty_parts (@Ordinal 3 2 isT) = set0.
Proof. by []. Qed.

(** Two distinct indices cannot both contain the edge of [K_2]. *)
Lemma not_edge_partition_K2_duplicate :
  ~ edge_partition (fun _ : 'I_2 => E('K_2)).
Proof.
move=> part.
have eG : [set: 'K_2] \in E('K_2).
  apply: (perfect_matching_edge perfect_matching_K2).
  by rewrite inE.
have d := edge_partition_disjoint part
  (isT : (ord0 : 'I_2) != @Ordinal 2 1 isT).
by have := disjointFr d eG; rewrite eG.
Qed.

(** A non-edge member is rejected even when the graph has edges. *)
Lemma not_edge_partition_K2_loop :
  ~ edge_partition (fun _ : 'I_1 => [set [set (ord0 : 'K_2)]]).
Proof.
apply: (@not_edge_partition_non_edge 'K_2 1 _ [set ord0] ord0).
- by rewrite inE.
- have -> : [set (ord0 : 'K_2)] = [set ord0; ord0] by rewrite setUid.
  by rewrite in_edges sg_irrefl.
Qed.

Print Assumptions edge_partition_uniqP.
Print Assumptions card_edge_partition.
Print Assumptions edge_partition0.
Print Assumptions edge_partition_K2_empty_part.
Print Assumptions not_edge_partition_K2_duplicate.
Print Assumptions not_edge_partition_K2_loop.
