(** * Extremal.conjectures.grounding_X215 -- grounding lemmas for wave X215.

    For every statement of [X215.v] this file records
    (i)  a NON-VACUITY witness: the hypotheses are jointly satisfiable by a
         concrete finite graph, so the statement is not true by an empty guard;
    (ii) a GUARD-HAS-TEETH lemma: the obvious degenerate instance is rejected,
         so the guard does restricting work and the conclusion is not automatic;
    plus, for the Burr-Erdos row, the SETTLED case k = 1 (r(K_2,K_2) = 2) proved
    from the statement's own definitions.

    Everything is closed by [Qed]; see the [Print Assumptions] audit at the end. *)

From GTBase Require Import base.
From Extremal.foundations Require Import edge_colourings.
From Extremal.conjectures Require Import X215.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** The smallest non-trivial tree: ['K_2] *)

Lemma is_forest_K2 : is_forest [set: 'K_2].
Proof.
have key : forall (x y : 'K_2) (p q : Path x y), irred p -> irred q -> p = q.
  move=> x y; case: (eqVneq x y) => [<-|xy] p q ip iq.
    by rewrite (irredxx ip) (irredxx iq).
  have E2 : [set x; y] = [set: 'K_2].
    by apply/eqP; rewrite eqEcard subsetT /= cards2 xy cardsT card_ord.
  have sub : forall (r : Path x y), {subset r <= [set x; y]}.
    by move=> r z _; rewrite E2 inE.
  have [e1 ->] := irred_is_edge p ip xy (sub p).
  have [e2 ->] := irred_is_edge q iq xy (sub q).
  by rewrite (bool_irrelevance e2 e1).
apply: forestI => -[x [y [p1 [p2 [[i1 i2 ne] _]]]]].
by rewrite (key _ _ p1 p2 i1 i2) eqxx in ne.
Qed.

Lemma connected_K2 : connected [set: 'K_2].
Proof.
move=> x y _ _; case: (eqVneq x y) => [->|xy]; first exact: connect0.
have xy' : x -- y := xy.
by apply: connect1; rewrite /= !inE.
Qed.

Lemma is_tree_K2 : is_tree [set: 'K_2].
Proof. by split; [exact: is_forest_K2 | exact: connected_K2]. Qed.

Lemma card_edge_K2 : #|E('K_2)| = 1.
Proof. by rewrite card_edge_Kn binn. Qed.

Lemma card_edge_K3 : #|E('K_3)| = 3.
Proof. by rewrite card_edge_Kn. Qed.

(** ** Row bm-033 (Erdos-Sos) *)

(** NON-VACUITY: the triangle and the single edge satisfy every hypothesis
    ([T] = 'K_2 is a tree with k = 1 edge and 2 vertices, and
    #|'K_3| * 1 = 3 < 2 * 3 + 3), so the guard is inhabited. *)
Lemma erdos_sos_hypotheses_satisfiable :
  is_tree [set: 'K_2] /\ #|E('K_2)| = 1 /\ #|'K_2| = 2 /\
  #|'K_3| * 1 < 2 * #|E('K_3)| + #|'K_3|.
Proof.
split; first exact: is_tree_K2.
split; first exact: card_edge_K2.
by rewrite !card_ord card_edge_K3.
Qed.

(** GUARD HAS TEETH, part 1: the edge-count guard FAILS for G = 'K_2 and k = 2
    (4 < 4 is false), so it is not satisfied by every graph. *)
Lemma erdos_sos_guard_rejects_K2 :
  ~~ (#|'K_2| * 2 < 2 * #|E('K_2)| + #|'K_2|).
Proof. by rewrite card_ord card_edge_K2. Qed.

(** GUARD HAS TEETH, part 2: and the conclusion genuinely fails there -- no tree
    on 3 vertices (i.e. with k = 2 edges) embeds into 'K_2 at all.  So the guard
    rejected exactly an instance where the conclusion is false. *)
Lemma erdos_sos_no_3_vertex_subgraph (T : sgraph) :
  #|T| = 3 -> ~ has_subgraph 'K_2 T.
Proof.
move=> cT [h inj _].
by have := leq_card h inj; rewrite cT card_ord.
Qed.

(** ** Row bm-034 (even-cycle Turan number) *)

(** NON-VACUITY: C_4-free graphs on few vertices exist -- 'K_3 has no C_4
    subgraph -- so for k = 2 the inner existential is over a non-empty class. *)
Lemma turan_C4_free_K3 : ~ has_subgraph 'K_3 (cycle_graph (2 * 2)).
Proof.
move=> [h inj _].
by have := leq_card h inj; rewrite !card_ord.
Qed.

(** GUARD HAS TEETH: the C_2k-free requirement genuinely excludes graphs --
    C_4 itself contains C_4. *)
Lemma turan_C4_not_free_C4 : has_subgraph (cycle_graph (2 * 2)) (cycle_graph (2 * 2)).
Proof. exact: has_subgraph_refl. Qed.

(** ** Rows bm-037 / bm-038 (BLOCKED placeholders): the Ramsey arrow vocabulary *)

(** NON-VACUITY: [x215_arrows 1 1] holds (K_1 arrows K_1 vacuously, it has no
    edge to colour), so the arrow relation of both blocked placeholders is
    inhabited and not an empty predicate. *)
Lemma x215_arrows_1_1 : x215_arrows 1 1.
Proof.
move=> col; exists true, id; split => // x y xy; move: xy;
  by rewrite [x]ord1 [y]ord1 sg_irrefl.
Qed.

(** GUARD HAS TEETH: the arrow relation is NOT automatic -- K_0 does not arrow
    K_1, so [~ x215_arrows N k] (the shape used by both blocked placeholders) is
    genuinely satisfiable. *)
Lemma not_x215_arrows_0_1 : ~ x215_arrows 0 1.
Proof.
move=> /(_ (fun _ => true)) [c [emb [_ _ _]]].
by case: (emb ord0) => m mh; rewrite ltn0 in mh.
Qed.

(** ** Row bm-039 (Burr-Erdos tree Ramsey) *)

(** NON-VACUITY: T = 'K_2, k = 1, N = 2 satisfies every hypothesis. *)
Lemma burr_erdos_hypotheses_satisfiable :
  is_tree [set: 'K_2] /\ #|E('K_2)| = 1 /\ #|'K_2| = 2 /\ 0 < 1 /\ 2 = 2 * 1.
Proof.
split; first exact: is_tree_K2.
by split; [exact: card_edge_K2 | rewrite card_ord].
Qed.

(** SETTLED CASE k = 1: r(K_2,K_2) <= 2, proved from the statement's own
    definitions -- in K_2 the unique edge is monochromatic. *)
Lemma burr_erdos_settled_k1 (col : {set 'K_2} -> bool) :
  exists c : bool, mono_copy 'K_2 col c.
Proof.
exists (col [set: 'K_2]), id; split => // x y xy.
have -> : [set x; y] = [set: 'K_2].
  have xy' : x != y := xy.
  by apply/eqP; rewrite eqEcard subsetT /= cards2 xy' cardsT card_ord.
by [].
Qed.

(** GUARD HAS TEETH: a monochromatic copy is NOT automatic -- no copy of 'K_2
    fits inside the empty host K_0, so the conclusion carries content. *)
Lemma no_mono_copy_K2_in_K0 (col : {set 'K_0} -> bool) (c : bool) :
  ~ mono_copy 'K_2 col c.
Proof. by case=> emb [_ _ _]; case: (emb ord0) => m mh; rewrite ltn0 in mh. Qed.

(** ** Print Assumptions audit *)

Print Assumptions is_tree_K2.
Print Assumptions erdos_sos_hypotheses_satisfiable.
Print Assumptions erdos_sos_guard_rejects_K2.
Print Assumptions erdos_sos_no_3_vertex_subgraph.
Print Assumptions turan_C4_free_K3.
Print Assumptions turan_C4_not_free_C4.
Print Assumptions x215_arrows_1_1.
Print Assumptions not_x215_arrows_0_1.
Print Assumptions burr_erdos_hypotheses_satisfiable.
Print Assumptions burr_erdos_settled_k1.
Print Assumptions no_mono_copy_K2_in_K0.
