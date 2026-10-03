(** Downstream use of the incidence degree of a vertex in a supplied finite family
    ([incidence_degree]), without corpus imports.  The family is arbitrary: empty, with an empty
    or a singleton member, or not a set of graph edges at all. *)
From GTBase Require Import base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Families.
Variable T : finType.
Implicit Types (F M : {set {set T}}) (e W : {set T}) (v w : T).

Example empty_family_counts_nothing v : incidence_degree (set0 : {set {set T}}) v = 0.
Proof. exact: incidence_degree_set0. Qed.

(** An empty member contains no vertex. *)
Example empty_member_counts_nothing v : incidence_degree [set (set0 : {set T})] v = 0.
Proof. by rewrite incidence_degree_set1 inE. Qed.

(** A singleton member (not a graph edge) counts once at its vertex and nowhere else. *)
Example singleton_member_counts_once v : incidence_degree [set [set v]] v = 1.
Proof. by rewrite incidence_degree_set1 set11. Qed.

Example singleton_member_elsewhere v w : w != v -> incidence_degree [set [set v]] w = 0.
Proof. by move=> wv; rewrite incidence_degree_set1 inE (negbTE wv). Qed.

Example at_most_the_family F v : incidence_degree F v <= #|F|.
Proof. exact: incidence_degree_le. Qed.

Example positive_iff_some_member_contains F v :
  (0 < incidence_degree F v) = [exists e in F, v \in e].
Proof. exact: incidence_degree_gt0. Qed.

Example monotone_in_the_family F M v :
  M \subset F -> incidence_degree M v <= incidence_degree F v.
Proof. exact: incidence_degree_subset. Qed.

(** Restricting to the members inside [W]: nothing outside [W], everything for [W = setT]. *)
Example restricted_outside F W v :
  v \notin W -> incidence_degree [set e in F | e \subset W] v = 0.
Proof. exact: incidence_degree_inside_out. Qed.

Example restricted_whole_carrier F v :
  incidence_degree [set e in F | e \subset [set: T]] v = incidence_degree F v.
Proof. exact: incidence_degree_insideT. Qed.

End Families.

(** At the edge set of a graph, the graph degree. *)
Example edge_set_degree (G : sgraph) (v : G) : incidence_degree E(G) v = #|N(v)|.
Proof. exact: incidence_degree_edges. Qed.

(** A non-graph family on ['I_3]: the whole carrier (three vertices) and a singleton.  Vertex [0]
    lies in both members, vertex [2] only in the first. *)
Definition triple_and_singleton : {set {set 'I_3}} := [set [set: 'I_3]; [set ord0]].

Lemma triple_neq_singleton : [set: 'I_3] != [set ord0].
Proof. by apply/eqP => /setP/(_ ord_max); rewrite !inE. Qed.

Example nongraph_family_two : incidence_degree triple_and_singleton ord0 = 2.
Proof.
rewrite /incidence_degree (_ : [set e in _ | _] = triple_and_singleton).
  by rewrite cards2 triple_neq_singleton.
by apply/setP => e; rewrite !inE; apply/andb_idr => /orP[] /eqP ->; rewrite !inE.
Qed.

Example nongraph_family_one : incidence_degree triple_and_singleton ord_max = 1.
Proof.
rewrite /incidence_degree (_ : [set e in _ | _] = [set [set: 'I_3]]) ?cards1 //.
apply/setP => e; rewrite !inE; case: (e =P [set: 'I_3]) => [->|_]; first by rewrite inE.
by case: (e =P [set ord0]) => [->|] //; rewrite inE.
Qed.

(** Restricted to [W = [set ord0]], only the singleton is inside [W]: vertex [0] keeps one
    incidence and vertex [2], outside [W], none. *)
Example nongraph_family_restricted :
  incidence_degree [set e in triple_and_singleton | e \subset [set ord0]] ord0 = 1 /\
  incidence_degree [set e in triple_and_singleton | e \subset [set ord0]] ord_max = 0.
Proof.
split; last by apply: incidence_degree_inside_out; rewrite inE.
have notin : ([set: 'I_3] \subset [set ord0]) = false.
  by apply/negbTE/subsetPn; exists ord_max; rewrite !inE.
rewrite /incidence_degree (_ : [set e in _ | _] = [set [set ord0]]) ?cards1 //.
apply/setP => e; rewrite /triple_and_singleton !inE.
case: (e =P [set ord0]) => [->|_]; first by rewrite subxx !inE !eqxx orbT.
by case: (e =P [set: 'I_3]) => [->|_]; rewrite ?notin ?andbF.
Qed.

Print Assumptions nongraph_family_two.
Print Assumptions nongraph_family_restricted.
Print Assumptions edge_set_degree.
