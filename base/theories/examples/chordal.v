(** * GTBase.examples.chordal — public-only client of GTBase.chordal (B25)

    Compiles against public modules alone (no conjecture module).  Cycle presentation: [K_0], [K_1]
    and [K_3] satisfy it, the triangle of [K_3] being an accepted chordless cycle of length three,
    while [cycle_graph 4] fails it through its actual hole.  Clique-tree presentation: [K_0] with
    the empty index, [K_1] and [K_3] with one full clique bag, a nonempty host forcing an inhabited
    index, a disconnected edgeless host with singleton bags on the tree [K_2], and a cyclic index
    rejecting one supplied witness while the host still admits another. *)

From mathcomp Require Import all_boot.
From GraphTheory Require Import preliminaries digraph sgraph.
From GraphTheory Require minor.
From GTBase Require Import base induced_cycles bag_decompositions trees chordal.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Cycle presentation *)

Lemma example_cycles_K0 : chordal_by_cycles 'K_0.
Proof. by apply: chordal_by_cycles_small; rewrite card_ord. Qed.

Lemma example_cycles_K1 : chordal_by_cycles 'K_1.
Proof. by apply: chordal_by_cycles_small; rewrite card_ord. Qed.

Lemma example_cycles_K3 : chordal_by_cycles 'K_3.
Proof. by apply: chordal_by_cycles_small; rewrite card_ord. Qed.

Local Notation k3_0 := (@Ordinal 3 0 isT).
Local Notation k3_1 := (@Ordinal 3 1 isT).
Local Notation k3_2 := (@Ordinal 3 2 isT).

(** The triangle is a chordless genuine cycle, accepted because it has three vertices. *)
Lemma example_triangle_accepted :
  chordless_cycle (G := 'K_3) [:: k3_0; k3_1; k3_2] /\ size [:: k3_0; k3_1; k3_2] <= 3.
Proof. by split=> //; apply/chordless_cycleP; vm_compute. Qed.

Definition c4 : seq (cycle_graph 4) :=
  [:: @Ordinal 4 0 isT; @Ordinal 4 1 isT; @Ordinal 4 2 isT; @Ordinal 4 3 isT].

(** The four-cycle has a hole, so it fails the cycle presentation. *)
Lemma example_C4_not_chordal : ~ chordal_by_cycles (cycle_graph 4).
Proof. by move/chordal_by_cyclesP/(_ c4); apply; apply/holeP; vm_compute. Qed.

(** ** Clique-tree presentation *)

(** The empty host uses the empty index graph (a tree). *)
Lemma example_clique_tree_K0 : admits_clique_tree 'K_0.
Proof.
exists ('K_0), (fun _ => set0); split; first exact: tree_bag_decomposition_K0.
by case=> m; rewrite ltn0.
Qed.

Lemma example_clique_tree_K1 : admits_clique_tree 'K_1.
Proof.
apply: admits_clique_tree_complete => x y _ _.
by rewrite (fintype.ord1 x) (fintype.ord1 y) eqxx.
Qed.

Lemma example_clique_tree_K3 : admits_clique_tree 'K_3.
Proof. exact: admits_clique_tree_complete (@minor.Kn_clique 3). Qed.

(** A nonempty host forces an inhabited index. *)
Lemma example_nonempty_index (T : sgraph) (bag : T -> {set 'K_1}) :
  clique_tree_decomposition bag -> 0 < #|T|.
Proof. by move/clique_tree_decomposition_nonempty_index; apply; rewrite card_ord. Qed.

(** A disconnected edgeless host: two isolated vertices, singleton bags on the tree [K_2]. *)
Lemma example_two_isolated_no_edge : ~~ ((ord0 : two_isolated) -- ord_max).
Proof. by []. Qed.

Lemma example_clique_tree_two_isolated : admits_clique_tree two_isolated.
Proof.
exists ('K_2), (fun t : 'K_2 => [set (t : two_isolated)]); split.
- split; first exact: is_tree_K2.
  split=> [v|]; first by apply/existsP; exists (v : 'K_2); rewrite inE.
  split=> [x y //|v].
  have -> : [set t : 'K_2 | v \in [set (t : two_isolated)]] = [set (v : 'K_2)].
    by apply/setP => t; rewrite !inE eq_sym.
  exact: connected1.
- by move=> t; apply/cliqueP => a b; rewrite !inE => /eqP-> /eqP->; rewrite eqxx.
Qed.

(** A cyclic index rejects that supplied witness; the host still admits another one. *)
Lemma example_cyclic_index_rejected :
  ~ clique_tree_decomposition (fun _ : 'K_3 => [set: 'K_1]) /\ admits_clique_tree 'K_1.
Proof.
split; last exact: example_clique_tree_K1.
by case=> dec _; exact: not_tree_bag_decomposition_K3_index dec.
Qed.

Print Assumptions example_cycles_K3.
Print Assumptions example_triangle_accepted.
Print Assumptions example_C4_not_chordal.
Print Assumptions example_clique_tree_K0.
Print Assumptions example_clique_tree_K3.
Print Assumptions example_clique_tree_two_isolated.
Print Assumptions example_cyclic_index_rejected.
