(** * Extremal.examples.edge_cycles — public-only client of Extremal.foundations.edge_cycles (B29)

    Compiles against public modules alone (no conjecture or migration module).  The empty family, the graphs
    [K_0], [K_1], [K_2] and every length at most two have no cycle; [K_3] has exactly one, its three edges; a
    triangle of [K_4] is a cycle although the fourth vertex is uncovered and three host chords lie outside the family;
    two disjoint triangles of [K_6] are host edges but not one cycle (their support is disconnected); a singleton
    member keeps its raw reflexive relation and is rejected by the host-edge conjunct. *)

From mathcomp Require Import all_boot.
From GraphTheory Require Import preliminaries digraph sgraph.
From GTBase Require Import base.
From Extremal Require Import foundations.edge_cycles.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Notation k3 i := (@Ordinal 3 i isT) (only parsing).
Local Notation k4 i := (@Ordinal 4 i isT) (only parsing).
Local Notation k6 i := (@Ordinal 6 i isT) (only parsing).

(** No cycle in the empty family, in graphs with at most two vertices, or of length at most two. *)
Lemma example_small :
  ~~ edge_family_cycle (set0 : {set {set 'K_3}}) /\
  [/\ edge_family_cycle_count 'K_0 = 0, edge_family_cycle_count 'K_1 = 0 & edge_family_cycle_count 'K_2 = 0] /\
  (forall (G : sgraph) (l : nat), l <= 2 -> ~ has_edge_family_cycle_length G l).
Proof.
split; first exact: edge_family_cycle_set0.
split; first by split; apply: edge_family_cycle_count_small; rewrite card_ord.
by move=> G l l2 /has_edge_family_cycle_length_gt2; rewrite ltnNge l2.
Qed.

(** [K_3] has exactly one edge-family cycle: its three edges. *)
Lemma example_K3_count : edge_family_cycle_count 'K_3 = 1.
Proof.
set F3 : {set {set 'K_3}} := [set [set k3 0; k3 1]; [set k3 1; k3 2]; [set k3 0; k3 2]].
have [cyc _] := @edge_family_cycle_triangle 'K_3 (k3 0) (k3 1) (k3 2) isT isT isT.
have E3 : E('K_3) = F3.
  apply/esym/eqP; rewrite eqEcard (edge_family_cycle_subset cyc) card_sg_edge_set_K3.
  by have /edge_family_cycleP[_ big -> _ _] := cyc.
rewrite /edge_family_cycle_count (_ : [set F | edge_family_cycle F] = [set F3]) ?cards1 //.
apply/setP => F; rewrite !inE; apply/idP/eqP => [cF | ->] //.
apply/eqP; rewrite eqEcard -E3 (edge_family_cycle_subset cF) card_sg_edge_set_K3 /=.
by have /edge_family_cycleP[_ big -> _ _] := cF.
Qed.

(** A triangle of [K_4] beside the uncovered fourth vertex, with host chords outside the family. *)
Lemma example_K4_triangle :
  let F : {set {set 'K_4}} := [set [set k4 0; k4 1]; [set k4 1; k4 2]; [set k4 0; k4 2]] in
  [/\ edge_family_cycle F, k4 3 \notin edge_family_support F & [set (k4 0 : 'K_4); k4 3] \in E('K_4) :\: F].
Proof.
have [cyc supp] := @edge_family_cycle_triangle 'K_4 (k4 0) (k4 1) (k4 2) isT isT isT.
split=> //; first by rewrite supp !inE.
rewrite in_setD in_edges andbT; rewrite !inE -orbA.
by apply/negP => /or3P[] /eqP /setP /(_ (k4 3)); rewrite !inE /=.
Qed.

(** Two disjoint triangles of [K_6]: host edges, but the support is disconnected. *)
Lemma example_K6_two_triangles :
  let F : {set {set 'K_6}} := [set [set k6 0; k6 1]; [set k6 1; k6 2]; [set k6 0; k6 2]] :|:
           [set [set k6 3; k6 4]; [set k6 4; k6 5]; [set k6 3; k6 5]] in
  F \subset E('K_6) /\ ~~ edge_family_cycle F.
Proof.
have [cA _] := @edge_family_cycle_triangle 'K_6 (k6 0) (k6 1) (k6 2) isT isT isT.
have [cB _] := @edge_family_cycle_triangle 'K_6 (k6 3) (k6 4) (k6 5) isT isT isT.
move=> F; split; first by rewrite subUset (edge_family_cycle_subset cA) (edge_family_cycle_subset cB).
set A : {set 'K_6} := [set k6 0; k6 1; k6 2].
have sep e : e \in F -> (e \subset A) || [disjoint e & A].
  rewrite in_setU => /orP[eA | eB]; apply/orP; [left | right].
  - move: eA; rewrite !inE -orbA => /or3P[] /eqP->; apply/subsetP => z;
      rewrite !inE => /orP[] /eqP->; rewrite ?eqxx ?orbT //.
  - move: eB; rewrite !inE -orbA => /or3P[] /eqP->; apply/disjointP => z;
      rewrite !inE => /orP[] /eqP->; by [].
have x0 : (k6 0 : 'K_6) \in A by rewrite !inE.
have x3 : (k6 3 : 'K_6) \notin A by rewrite !inE.
have nc := @edge_family_rel_closed 'K_6 F A (k6 0) (k6 3) sep x0 x3.
apply/negP => /edge_family_cycleP[_ _ _ _ con]; move/negP: nc; apply; apply: con.
- by rewrite in_edge_family_support; apply/existsP; exists [set k6 0; k6 1]; rewrite !inE !eqxx ?orbT.
- by rewrite in_edge_family_support; apply/existsP; exists [set k6 3; k6 4]; rewrite !inE !eqxx ?orbT.
Qed.

(** A singleton member: the raw relation is reflexive there and the support is that vertex, but the member is not a
    host edge, so the family is rejected by the first conjunct. *)
Lemma example_singleton_member :
  let F := [set [set k3 0]] : {set {set 'K_3}} in
  [/\ edge_family_rel F (k3 0) (k3 0), edge_family_support F = [set k3 0], ~~ (F \subset E('K_3))
    & ~~ edge_family_cycle F].
Proof.
move=> F; have notE : [set (k3 0 : 'K_3)] \notin E('K_3).
  rewrite in_sg_edge_set; apply/existsP => -[x /existsP[y /andP[xy /eqP E]]].
  have : x \in [set k3 0] by rewrite E !inE eqxx.
  have : y \in [set k3 0] by rewrite E !inE eqxx orbT.
  by rewrite !inE => /eqP yx /eqP xx; move: xy; rewrite yx xx sgP.
have sub : ~~ (F \subset E('K_3)) by rewrite sub1set.
split=> //.
- by apply: edge_family_rel_singleton; rewrite inE.
- apply/setP => v; rewrite in_edge_family_support !inE; apply/existsP/idP => [[e] | ve].
    by rewrite !inE => /andP[/eqP-> ]; rewrite !inE.
  by exists [set k3 0]; rewrite !inE eqxx.
- by apply/negP => /edge_family_cycle_subset; apply/negP.
Qed.

Print Assumptions example_small.
Print Assumptions example_K3_count.
Print Assumptions example_K4_triangle.
Print Assumptions example_K6_two_triangles.
Print Assumptions example_singleton_member.
