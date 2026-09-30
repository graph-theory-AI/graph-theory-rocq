(** * Minor.conjectures.grounding_X228 — grounding lemmas for wave X228.

    Qed-closed, axiom-free sanity results for the two X228 statements and for the
    new primitive [x228_unavoidable], plus for the layered-treewidth / queue-number
    vocabulary of Minor.foundations.width_params.

    Per statement: a NON-VACUITY witness and a GUARD-HAS-TEETH lemma.  The blocked
    row arxiv:2002.00496#02 is grounded on its PLACEHOLDER body (see X228.v's
    Notes): the empty graph is unavoidable and does satisfy the placeholder's
    conclusion, while ['K_5] shows the conclusion is not automatic. *)

From GTBase Require Import base.
From GraphTheory Require Import minor.
From Minor.foundations Require Import containment width_params.
From Minor.conjectures Require Import X228.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Row 1 — arxiv:1810.08314#00 (layered treewidth vs queue number) *****)

Lemma K2_edge' : (ord0 : 'K_2) -- (@Ordinal 2 1 isT).
Proof. by rewrite /edge_rel. Qed.

(** ['K_2] has queue number at most 1: order the two vertices by their index and
    put the unique edge in queue 0; nesting needs four strictly increasing
    positions, which two vertices cannot provide. *)
Lemma X228_K2_queue : queue_number_le 'K_2 1.
Proof.
exists (fun v : 'K_2 => val v), (fun _ => 0); split.
- by move=> u v /val_inj.
- by [].
- move=> a b c d _ _ _ ac cd db.
  have c0 : 0 < val c by exact: leq_ltn_trans (leq0n (val a)) ac.
  have d1 : 1 < val d by exact: leq_ltn_trans c0 cd.
  have b2 : 2 < val b by exact: leq_ltn_trans d1 db.
  by move: (leq_ltn_trans b2 (ltn_ord b)).
Qed.

(** NON-VACUITY: ['K_2] has layered treewidth at most 2 and queue number at most
    1, so both sides of the statement are satisfiable by a graph WITH an edge. *)
Lemma X228_queue_nonvacuous :
  layered_tw_le 'K_2 2 /\ queue_number_le 'K_2 1.
Proof.
split; last exact: X228_K2_queue.
by have := layered_tw_le_card 'K_2; rewrite card_ord.
Qed.

(** GUARD HAS TEETH (1): queue number 0 forces an edgeless graph, so the
    conclusion [queue_number_le G (f k)] is not automatic. *)
Lemma X228_queue_guard_teeth : ~ queue_number_le 'K_2 0.
Proof.
by move=> q; move: (queue_number_le0_edgeless (ord0 : 'K_2) (@Ordinal 2 1 isT) q); rewrite K2_edge'.
Qed.

(** GUARD HAS TEETH (2): layered treewidth 0 forces a graph with no vertex, so
    the hypothesis [layered_tw_le G k] really restricts. *)
Lemma X228_layered_guard_teeth : ~ layered_tw_le 'K_1 0.
Proof. by move/layered_tw_le0_empty; rewrite card_ord. Qed.

(** ** Row 2 — arxiv:2002.00496#02 (BLOCKED placeholder) *******************)

(** Every graph has the empty graph as a minor (all clauses are vacuous). *)
Lemma X228_K0_void (x : 'K_0) : False.
Proof. by case: x => m; rewrite ltn0. Qed.

Lemma minor_K0 (G : sgraph) : minor G 'K_0.
Proof.
exists (fun _ : G => None); split.
- by move=> y; case: (X228_K0_void y).
- by move=> y; case: (X228_K0_void y).
- by move=> x y; case: (X228_K0_void x).
Qed.

(** NON-VACUITY: the empty graph is unavoidable, and it satisfies the
    placeholder's conclusion (it is Wagner-planar and has treewidth 0). *)
Lemma X228_unavoidable_K0 : x228_unavoidable 'K_0.
Proof. by exists 0 => P _; exact: minor_K0. Qed.

Lemma X228_kelly_nonvacuous :
  x228_unavoidable 'K_0 /\ wagner_planar 'K_0 /\ tw_le 'K_0 3.
Proof.
split; first exact: X228_unavoidable_K0.
split; last by apply: tw_le_card; rewrite card_ord.
split=> m; first by move: (minor_card m); rewrite !card_ord.
by move: (minor_card m); rewrite card_ord card_sum !card_ord.
Qed.

(** GUARD HAS TEETH: the placeholder's conclusion is not automatic — ['K_5] is
    NOT Wagner-planar, so it could not be unavoidable if the placeholder held. *)
Lemma X228_kelly_guard_teeth : ~ wagner_planar 'K_5.
Proof.
case=> no5 _; apply: no5; apply: sub_minor.
by apply: (@sub_Kn 5 'K_5); rewrite card_ord.
Qed.

(** The [x228_unavoidable] guard has teeth on the dimension side: a threshold is
    genuinely needed, since the definition only constrains posets whose dimension
    EXCEEDS it (the unit poset has dimension at most 1 and is thus never tested). *)
Lemma X228_unit_poset_dim : poset_dimension_at_most unit_poset 1.
Proof.
exists [:: unit_poset_le]; split; first by [].
split=> [i|x y].
- rewrite ltnS leqn0 => /eqP->; split; last by [].
  by split; [ | case; case | | ].
- by split=> [_ i|_ //]; rewrite ltnS leqn0 => /eqP->.
Qed.

Print Assumptions bounded_layered_treewidth_bounded_queue_number_statement.
Print Assumptions unavoidable_minor_kelly_construction_statement.
Print Assumptions X228_queue_nonvacuous.
Print Assumptions X228_queue_guard_teeth.
Print Assumptions X228_layered_guard_teeth.
Print Assumptions X228_unavoidable_K0.
Print Assumptions X228_kelly_nonvacuous.
Print Assumptions X228_kelly_guard_teeth.
Print Assumptions X228_unit_poset_dim.
