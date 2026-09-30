(** * Hamilton.conjectures.grounding_X211 — grounding lemmas for wave X211

    Qed-closed, axiom-free sanity results for the statements of [X211.v]
    (Bondy–Murty Appendix A rows bm-079, 080, 085, 088, 089, 090, 091).  For
    every authored statement we record

    - a NON-VACUITY witness: the hypotheses are satisfiable by a concrete finite
      graph (and, where the source records a settled case, the conclusion holds
      there — e.g. ['K_4] is a planar cubic graph with a triangle);
    - a GUARD-HAS-TEETH lemma: the obvious degenerate candidate is rejected, or
      the guard of the statement is load-bearing (dropping it refutes the
      statement).

    These validate the STATEMENTS; none of the (open) conjectures is proved. *)

From GTBase Require Import base.
From GraphTheory Require Import minor bij.
From mathcomp Require Import fingroup perm.
From Hamilton.conjectures Require Import X211.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Shared helpers on complete graphs, components and small graphs *)

(** Adjacency in ['K_n] is "being different". *)
Lemma edge_complete n (x y : 'K_n) : (x -- y) = (x != y).
Proof. by []. Qed.

(** Every vertex set of a complete graph is connected. *)
Lemma connected_complete n (A : {set 'K_n}) : connected A.
Proof.
move=> x y xA yA; have [->|xy] := eqVneq x y; first exact: connect0.
by apply: connect1; rewrite /= xA yA edge_complete xy.
Qed.

(** ['K_n] is k-connected for every k < n (Whitney form). *)
Lemma k_connected_complete n k : k < n -> k_connected 'K_n k.
Proof.
by move=> kn; split; [rewrite card_ord|move=> S _; exact: connected_complete].
Qed.

(** The open neighbourhood of a vertex of ['K_n] is everything else. *)
Lemma open_neigh_complete n (x : 'K_n) : N(x) = [set: 'K_n] :\ x.
Proof. by apply/setP => y; rewrite !inE andbT edge_complete eq_sym. Qed.

(** Removing one vertex from the full set. *)
Lemma card_setT_D1 (T : finType) (x : T) : #|[set: T] :\ x| = #|T| - 1.
Proof. by rewrite -cardsT [in RHS](cardsD1 x) in_setT add1n subn1. Qed.

(** Complete graphs are (n-1)-regular. *)
Lemma deg_complete n (x : 'K_n) : #|N(x)| = n.-1.
Proof. by rewrite open_neigh_complete card_setT_D1 card_ord subn1. Qed.

(** A connected vertex set has at most one component. *)
Lemma card_components_connected (G : sgraph) (A : {set G}) :
  connected A -> #|components A| <= 1.
Proof.
move=> cA; rewrite leqNgt; apply/negP => /card_gt1P[C [D [CP DP CD]]].
have [x xC] := components_nonempty CP.
have [y yD] := components_nonempty DP.
have xA : x \in A by move/components_subset/subsetP: CP; apply.
have yA : y \in A by move/components_subset/subsetP: DP; apply.
have yCx : y \in pblock (components A) x.
  by rewrite (pblock_equivalence_partition (@sedge_equiv_in G A)) //; apply: cA.
rewrite (def_pblock (trivIset_components A) CP xC) in yCx.
have /trivIsetP/(_ C D CP DP CD) := trivIset_components A.
by rewrite -setI_eq0 => /eqP/setP/(_ y); rewrite !inE yCx yD.
Qed.

(** A one-vertex graph is traceable (the single vertex is a Hamilton path). *)
Lemma traceable_card1 (G : sgraph) : #|G| = 1 -> traceable G.
Proof.
move=> c1; have /card_gt0P[x _] : 0 < #|G| by rewrite c1.
by exists [:: x]; rewrite /hamiltonian_path /= c1.
Qed.

(** The number of vertices of an induced subgraph. *)
Lemma card_induced (G : sgraph) (S : {set G}) : #|induced S| = #|S|.
Proof. by rewrite card_sig; apply: eq_card => x; rewrite inE. Qed.

(** ['K_5] has a Hamilton cycle. *)
Lemma hamiltonian_K5 : hamiltonian 'K_5.
Proof.
exists [:: (@Ordinal 5 0 isT : 'K_5); (@Ordinal 5 1 isT : 'K_5);
           (@Ordinal 5 2 isT : 'K_5); (@Ordinal 5 3 isT : 'K_5);
           (@Ordinal 5 4 isT : 'K_5)].
by rewrite /hamiltonian_cycle /ucycleb /= card_ord.
Qed.

(** ['K_4] has a Hamilton cycle. *)
Lemma hamiltonian_K4 : hamiltonian 'K_4.
Proof.
exists [:: (@Ordinal 4 0 isT : 'K_4); (@Ordinal 4 1 isT : 'K_4);
           (@Ordinal 4 2 isT : 'K_4); (@Ordinal 4 3 isT : 'K_4)].
by rewrite /hamiltonian_cycle /ucycleb /= card_ord.
Qed.

(** ** bm-079 — Matthews–Sumner ([matthews_sumner_four_connected_claw_free_statement])

    Non-vacuity: ['K_5] is 4-connected, claw-free and Hamiltonian, so the
    hypotheses are satisfiable and the conclusion holds there.
    Guard has teeth: the claw itself is NOT claw-free, and ['K_4] is not
    4-connected. *)

(** Complete graphs are claw-free: a claw has two non-adjacent vertices. *)
Lemma claw_free_complete n : x211_claw_free 'K_n.
Proof.
move=> S h.
have := edge_diso' h (inr ord0 : 'K_1,3) (inr (@Ordinal 3 1 isT) : 'K_1,3).
rewrite [in RHS]/edge_rel /= /kb_rel /=.
move/negbT; rewrite /edge_rel /= /induced_rel /= edge_complete negbK.
move/eqP/val_inj/(@bij_injective' _ _ (diso_v h)) => e.
by move: (f_equal (fun z : 'K_1,3 => if z is inr k then val k else 0) e).
Qed.

Lemma matthews_sumner_nonvacuous :
  k_connected 'K_5 4 /\ x211_claw_free 'K_5 /\ hamiltonian 'K_5.
Proof.
by split; [exact: k_connected_complete|split;
  [exact: claw_free_complete|exact: hamiltonian_K5]].
Qed.

(** The claw is not claw-free (the hypothesis rejects something). *)
Lemma not_claw_free_claw : ~ x211_claw_free 'K_1,3.
Proof.
move=> cf; apply: (cf [set: 'K_1,3]).
have inj_val : injective (val : induced [set: 'K_1,3] -> 'K_1,3) by exact: val_inj.
have sur : forall x : 'K_1,3, x \in [set: 'K_1,3] by move=> x; rewrite inE.
pose f (x : induced [set: 'K_1,3]) : 'K_1,3 := val x.
pose g (x : 'K_1,3) : induced [set: 'K_1,3] := Sub x (sur x).
have fg : cancel f g by move=> x; apply: val_inj.
have gf : cancel g f by [].
by apply: (@Diso _ _ (Bij fg gf)) => x y.
Qed.

(** 4-connectivity has teeth: ['K_4] is not 4-connected (too few vertices). *)
Lemma not_k_connected_K4_4 : ~ k_connected 'K_4 4.
Proof. by case; rewrite card_ord. Qed.

(** ** bm-080 — Barnette, BLOCKED placeholder
    ([barnette_simple_four_polytope_hamiltonian_statement])

    The placeholder hypothesis is satisfiable ([K_5] is 4-regular and
    4-connected) and it is strictly weaker than "graph of a simple 4-polytope":
    it holds for graphs that are not polytope graphs at all.  Recorded only to
    document the proxy; the row's statement leg is blocked. *)
Lemma four_polytope_placeholder_K5 : x211_four_polytope_graph_placeholder 'K_5.
Proof.
split; last exact: k_connected_complete.
by move=> v; rewrite deg_complete.
Qed.

Lemma not_four_polytope_placeholder_K4 :
  ~ x211_four_polytope_graph_placeholder 'K_4.
Proof. by case=> _; apply: not_k_connected_K4_4. Qed.

(** ** bm-085 — Cantoni ([cantoni_planar_cubic_three_hamilton_cycles_statement])

    Non-vacuity + settled case: ['K_4] is planar, cubic and DOES contain a
    triangle (the conjecture holds for it).
    Guard has teeth: ['K_5] is not planar, and ['K_4] is not 4-regular. *)

Lemma wagner_planar_K4 : wagner_planar 'K_4.
Proof.
split=> m; have := minor_card m; rewrite card_ord.
- by rewrite card_ord.
- by rewrite card_sum !card_ord.
Qed.

Lemma regular_K4_3 : regular 'K_4 3.
Proof. by move=> v; rewrite deg_complete. Qed.

Lemma has_triangle_K4 : x211_has_triangle 'K_4.
Proof.
exists (@Ordinal 4 0 isT : 'K_4), (@Ordinal 4 1 isT : 'K_4),
       (@Ordinal 4 2 isT : 'K_4).
by split; rewrite edge_complete.
Qed.

Lemma cantoni_nonvacuous :
  wagner_planar 'K_4 /\ regular 'K_4 3 /\ x211_has_triangle 'K_4.
Proof.
by split; [exact: wagner_planar_K4|split; [exact: regular_K4_3|exact: has_triangle_K4]].
Qed.

(** Planarity has teeth: ['K_5] is not (Wagner-)planar. *)
Lemma not_wagner_planar_K5 : ~ wagner_planar 'K_5.
Proof. by case=> nK5 _; apply: nK5; apply: sub_minor; exists id. Qed.

(** Cubicity has teeth: ['K_5] is 4-regular, not 3-regular. *)
Lemma not_regular_K5_3 : ~ regular 'K_5 3.
Proof. by move/(_ (@Ordinal 5 0 isT : 'K_5)); rewrite deg_complete. Qed.

(** The Hamilton-cycle counter is not vacuous: ['K_4] carries a Hamilton cycle,
    so its collection of Hamilton-cycle edge sets is nonempty.  (['K_4] in fact
    has EXACTLY three Hamilton cycles, the settled instance of Cantoni's
    conjecture recorded by the source, and it does contain a triangle; the exact
    count is NOT machine-checked here because deciding
    [#|x211_hamilton_cycle_edge_sets 'K_4| = 3] by computation sweeps the 2^16
    collections of edge sets of ['K_4] and is far too slow for the build.) *)
Lemma ham_cycle_sets_K4_nonempty : 0 < #|x211_hamilton_cycle_edge_sets 'K_4|.
Proof.
pose s : seq 'K_4 := [:: @Ordinal 4 0 isT; @Ordinal 4 1 isT;
                        @Ordinal 4 2 isT; @Ordinal 4 3 isT].
have sz : size s == #|'K_4| by rewrite /= card_ord.
apply/card_gt0P; exists (x211_cycle_edges 'K_4 s); rewrite inE.
apply/existsP; exists (@Tuple #|'K_4| 'K_4 s sz).
by rewrite eqxx andbT /hamiltonian_cycle /ucycleb /= card_ord.
Qed.

(** The Hamilton-cycle counter has teeth: ['K_1] carries no Hamilton cycle. *)
Lemma hamilton_cycle_edge_sets_K1 : #|x211_hamilton_cycle_edge_sets 'K_1| = 0.
Proof.
apply/eqP; rewrite cards_eq0; apply/eqP/setP => A; rewrite !inE.
apply/negbTE/negP => /existsP[c /andP[uc _]].
have sz := size_tuple c.
case E : (tval c) => [|x [|y s]]; rewrite E in sz uc.
- by move: sz; rewrite card_ord.
- move: uc; rewrite /hamiltonian_cycle /ucycleb /=.
  by rewrite sg_irrefl.
- by move: sz; rewrite card_ord.
Qed.

(** ** bm-088 — Thomassen, vertex-transitive graphs
    ([thomassen_vertex_transitive_all_but_finitely_many_statement])

    Non-vacuity: ['K_n] is connected, vertex-transitive and (for n >= 3)
    Hamiltonian.
    Guard has teeth: the claw ['K_1,3] is connected but NOT vertex-transitive
    (its centre and its leaves have different degrees). *)

Lemma vertex_transitive_complete n : x211_vertex_transitive 'K_n.
Proof.
move=> x y; exists (tperm x y); split; last exact: tpermL.
split; first by exists (tperm x y); apply: tpermK.
by move=> u v; rewrite !edge_complete (inj_eq perm_inj).
Qed.

Lemma thomassen_nonvacuous :
  connected [set: 'K_5] /\ x211_vertex_transitive 'K_5 /\ hamiltonian 'K_5.
Proof.
by split; [exact: connected_complete|split;
  [exact: vertex_transitive_complete|exact: hamiltonian_K5]].
Qed.

(** An automorphism preserves degrees. *)
Lemma automorphism_deg (G : sgraph) (f : G -> G) :
  x211_graph_automorphism f -> forall x : G, #|N(f x)| = #|N(x)|.
Proof.
case=> [[g fg gf] hf] x.
have -> : N(f x) = f @: N(x).
  apply/setP => y; rewrite !inE; apply/idP/imsetP.
  - by move=> fxy; exists (g y); [rewrite inE -hf gf|rewrite gf].
  - by case=> u; rewrite inE => ux ->; rewrite hf.
by rewrite card_imset //; apply: (can_inj fg).
Qed.

(** The claw is connected but not vertex-transitive. *)
Lemma not_vertex_transitive_claw : ~ x211_vertex_transitive 'K_1,3.
Proof.
move=> vt; have [f [af fx]] := vt (inl ord0) (inr ord0).
have := automorphism_deg af (inl ord0).
by rewrite fx deg_Knm_r deg_Knm_l.
Qed.

(** ** bm-089 — Chvátal's toughness conjecture
    ([chvatal_toughness_hamiltonian_statement])

    Non-vacuity: ['K_3] has more than two vertices, is k-tough for every k, and
    is Hamiltonian.
    Guard has teeth: ['K_1] is k-tough for every k and is NOT Hamiltonian, so
    the guard [2 < #|G|] is load-bearing — without it the statement would be
    refutable for a trivial reason. *)

Lemma tough_complete n k : x211_tough 'K_n k.
Proof.
move=> S; rewrite ltnNge => /negP; case.
by apply: card_components_connected; exact: connected_complete.
Qed.

Lemma chvatal_nonvacuous :
  2 < #|'K_3| /\ x211_tough 'K_3 1 /\ hamiltonian 'K_3.
Proof.
by split; [rewrite card_ord|split; [exact: tough_complete|exact: hamiltonian_K3]].
Qed.

Lemma chvatal_guard_has_teeth :
  (forall k : nat, x211_tough 'K_1 k) /\ ~ hamiltonian 'K_1 /\ ~~ (2 < #|'K_1|).
Proof.
split; first by move=> k; exact: tough_complete.
by split; [exact: not_hamiltonian_K1|rewrite card_ord].
Qed.

(** ** bm-090 — hypohamiltonian graphs of minimum degree >= 4
    ([hypohamiltonian_minimum_degree_four_statement])

    Non-vacuity of the degree hypothesis: ['K_5] has minimum degree 4.
    Guard has teeth: ['K_5] is NOT hypohamiltonian (it is Hamiltonian), so the
    existential statement is not satisfied by the obvious degree witness; and
    ['K_4] does not even have minimum degree 4. *)

Lemma min_degree_K5_4 : x211_min_degree_geq 'K_5 4.
Proof. by move=> v; rewrite deg_complete. Qed.

Lemma not_min_degree_K4_4 : ~ x211_min_degree_geq 'K_4 4.
Proof. by move/(_ (@Ordinal 4 0 isT : 'K_4)); rewrite deg_complete. Qed.

Lemma not_hypohamiltonian_K5 : ~ x211_hypohamiltonian 'K_5.
Proof. by case=> nh _; apply: nh; exact: hamiltonian_K5. Qed.

(** ** bm-091 — Grötschel, bipartite hypotraceable graphs
    ([grotschel_no_bipartite_hypotraceable_statement])

    Guard has teeth (and the guard is load-bearing): the edgeless graph on two
    vertices is bipartite and literally hypotraceable — it has no Hamilton path,
    while each of its one-vertex subgraphs has one — so without the [2 < #|G|]
    guard the statement would be refuted by this degenerate graph.
    The hypotraceability side has teeth too: ['K_3] is traceable, hence NOT
    hypotraceable, so the conclusion [~ x211_hypotraceable G] is not vacuous. *)

Section Edgeless.
Variable n : nat.
Definition x211g_norel : rel 'I_n := [rel _ _ | false].
Lemma x211g_norel_sym : symmetric x211g_norel. Proof. by []. Qed.
Lemma x211g_norel_irrefl : irreflexive x211g_norel. Proof. by []. Qed.
Definition x211g_edgeless : sgraph := SGraph x211g_norel_sym x211g_norel_irrefl.
End Edgeless.

Lemma card_edgeless n : #|x211g_edgeless n| = n.
Proof. exact: card_ord. Qed.

Lemma bipartite_edgeless n : bipartite (x211g_edgeless n).
Proof. by exists (fun _ => true) => x y. Qed.

Lemma not_traceable_edgeless2 : ~ traceable (x211g_edgeless 2).
Proof.
case=> s /and3P[srt _]; rewrite card_edgeless.
by case: s srt => [|x [|y [|z s]]] //=; rewrite andbT.
Qed.

Lemma traceable_edgeless2_del (v : x211g_edgeless 2) :
  traceable (induced ([set: x211g_edgeless 2] :\ v)).
Proof.
apply: traceable_card1; rewrite card_induced.
by rewrite card_setT_D1 card_edgeless.
Qed.

Lemma hypotraceable_edgeless2 : x211_hypotraceable (x211g_edgeless 2).
Proof.
by split; [exact: not_traceable_edgeless2|exact: traceable_edgeless2_del].
Qed.

Lemma grotschel_guard_has_teeth :
  bipartite (x211g_edgeless 2) /\ x211_hypotraceable (x211g_edgeless 2)
  /\ ~~ (2 < #|x211g_edgeless 2|).
Proof.
split; first exact: bipartite_edgeless.
by split; [exact: hypotraceable_edgeless2|rewrite card_edgeless].
Qed.

(** ['K_3] is traceable, hence not hypotraceable (the conclusion has teeth). *)
Lemma traceable_K3 : traceable 'K_3.
Proof.
exists [:: (@Ordinal 3 0 isT : 'K_3); (@Ordinal 3 1 isT : 'K_3);
           (@Ordinal 3 2 isT : 'K_3)].
by rewrite /hamiltonian_path /= card_ord.
Qed.

Lemma not_hypotraceable_K3 : ~ x211_hypotraceable 'K_3.
Proof. by case=> nt _; apply: nt; exact: traceable_K3. Qed.

(** ** Axiom audit *********************************************************

    Every lemma above is [Qed]-closed and was checked with [Print Assumptions]:
    "Closed under the global context". *)

Print Assumptions claw_free_complete.
Print Assumptions matthews_sumner_nonvacuous.
Print Assumptions not_claw_free_claw.
Print Assumptions not_k_connected_K4_4.
Print Assumptions four_polytope_placeholder_K5.
Print Assumptions not_four_polytope_placeholder_K4.
Print Assumptions cantoni_nonvacuous.
Print Assumptions not_wagner_planar_K5.
Print Assumptions not_regular_K5_3.
Print Assumptions ham_cycle_sets_K4_nonempty.
Print Assumptions hamilton_cycle_edge_sets_K1.
Print Assumptions thomassen_nonvacuous.
Print Assumptions not_vertex_transitive_claw.
Print Assumptions chvatal_nonvacuous.
Print Assumptions chvatal_guard_has_teeth.
Print Assumptions min_degree_K5_4.
Print Assumptions not_min_degree_K4_4.
Print Assumptions not_hypohamiltonian_K5.
Print Assumptions grotschel_guard_has_teeth.
Print Assumptions not_hypotraceable_K3.
