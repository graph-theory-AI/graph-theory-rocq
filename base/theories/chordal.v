(** * GTBase.chordal — chordality through chordless cycles and through clique trees

    Library migration B25, family [chordal] (meta/library_primitives/chordal.json).  The corpus
    states chordality in two presentations.  They are kept here as two distinct public contracts.
    No theorem relating them is assumed or proved: the pinned GraphTheory and MathComp sources
    contain no chordal, clique-tree, perfect-elimination or simplicial-vertex characterization, and
    none is claimed.
    - [chordal_by_cycles G]: every chordless genuine cycle of [G] ([chordless_cycle],
      GTBase.induced_cycles: a duplicate-free closed adjacency walk on at least three vertices with
      no chord) has at most three vertices (Packing XE1).  [chordal_by_cyclesP]: equivalently, [G]
      has no [hole].  The empty list and the two-vertex cycle of an edge are not genuine cycles, so
      they are never constrained.
    - [admits_clique_tree G]: some supplied index graph [T] and bag map [bag : T -> {set G}] form a
      [clique_tree_decomposition]: a tree-indexed bag decomposition ([tree_bag_decomposition],
      GTBase.bag_decompositions: [is_tree [set: T]], vertex coverage, edge coverage, connected
      fibres) all of whose bags are cliques ([cliqueb]) (GTMisc X169).  [admits_clique_treeP]
      spells the existential out clause by clause.  The index may be empty when [G] is ([is_tree]
      holds of the empty index), bags may be empty, unused or repeated, the host need not be
      connected, the bags need not be maximal cliques, and nothing bounds the index degree.  A
      nonempty host forces an inhabited index through vertex coverage alone.  Transport to upstream
      [sdecomp] keeps the same supplied forest and the explicit tree condition
      ([clique_tree_decomposition_sdecompP]); upstream [decomp_clique] keeps its nonempty-clique
      premise ([clique_tree_decomposition_clique]).
    Not re-exported by GTBase.base; no conjecture module is imported. *)

From mathcomp Require Import all_boot.
From GraphTheory Require Import preliminaries digraph sgraph treewidth.
From GTBase Require Import base induced_cycles bag_decompositions trees.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Chordal.
Variable G : sgraph.

(** ** The cycle presentation *)

Definition chordal_by_cycles : Prop :=
  forall c : seq G, chordless_cycle c -> size c <= 3.

(** No hole: a chordless genuine cycle has at most three vertices exactly when no chordless
    cycle has four or more. *)
Lemma chordal_by_cyclesP : chordal_by_cycles <-> forall c : seq G, ~ hole c.
Proof.
split=> h c.
- by move=> hc; have := h c (hole_chordless_cycle hc); rewrite leqNgt (hole_size hc).
- move=> cc; rewrite leqNgt; apply/negP => sz; apply: (h c).
  by case: cc => uc [_ ch]; split=> //; split.
Qed.

(** A chordless cycle is duplicate-free, so it has at most [#|G|] vertices. *)
Lemma chordless_cycle_size_card (c : seq G) : chordless_cycle c -> size c <= #|G|.
Proof. by case=> /andP[_ uc] _; rewrite -(card_uniqP uc) max_card. Qed.

(** Graphs on at most three vertices satisfy the cycle presentation (triangles are allowed). *)
Lemma chordal_by_cycles_small : #|G| <= 3 -> chordal_by_cycles.
Proof. by move=> small c cc; exact: leq_trans (chordless_cycle_size_card cc) small. Qed.

(** ** The clique-tree presentation *)

Definition clique_tree_decomposition (T : sgraph) (bag : T -> {set G}) : Prop :=
  tree_bag_decomposition bag /\ forall t : T, cliqueb (bag t).

Definition admits_clique_tree : Prop :=
  exists (T : sgraph) (bag : T -> {set G}), clique_tree_decomposition bag.

(** The supplied tree and bags, clause by clause. *)
Lemma admits_clique_treeP :
  admits_clique_tree <->
  exists (T : sgraph) (bag : T -> {set G}),
    [/\ is_tree [set: T],
        forall v : G, exists t : T, v \in bag t,
        forall x y : G, x -- y -> exists t : T, x \in bag t /\ y \in bag t,
        forall v : G, connected [set t : T | v \in bag t] &
        forall t : T, cliqueb (bag t)].
Proof.
split=> -[T [bag]].
- move=> [dec cl]; have [tr [cov [edg fib]]] := (tree_bag_decompositionP bag).1 dec.
  by exists T, bag.
- move=> [tr cov edg fib cl]; exists T, bag; split=> //.
  by apply/tree_bag_decompositionP.
Qed.

(** A complete host has a single-bag clique tree on [K_1]. *)
Lemma admits_clique_tree_complete : clique [set: G] -> admits_clique_tree.
Proof.
move=> cl; exists ('K_1), (fun _ => [set: G]); split; last by move=> _; apply/cliqueP.
split; first exact: is_tree_K1.
split=> [v|]; first by apply/existsP; exists ord0; rewrite inE.
split=> [x y _|v]; first by apply/existsP; exists ord0; rewrite !inE.
have -> : [set t : 'K_1 | v \in [set: G]] = [set: 'K_1] by apply/setP => t; rewrite !inE.
by case: is_tree_K1.
Qed.

(** A nonempty host forces an inhabited index (through vertex coverage alone). *)
Lemma clique_tree_decomposition_nonempty_index (T : sgraph) (bag : T -> {set G}) :
  clique_tree_decomposition bag -> 0 < #|G| -> 0 < #|T|.
Proof. by case=> -[_ dec] _; exact: bag_decomposition_nonempty_index dec. Qed.

(** Upstream transport on the same supplied forest, with the explicit tree condition kept. *)
Lemma clique_tree_decomposition_sdecompP (T : forest) (bag : T -> {set G}) :
  clique_tree_decomposition bag <->
  [/\ is_tree [set: T], sdecomp T G bag & forall t : T, cliqueb (bag t)].
Proof.
split=> [[[tr dec] cl] | [tr dec cl]].
- by split=> //; apply/bag_decomposition_sdecompP.
- by split=> //; split=> //; apply/bag_decomposition_sdecompP.
Qed.

(** Every nonempty clique of the host lies inside one bag (upstream [decomp_clique], whose
    nonempty premise is kept). *)
Lemma clique_tree_decomposition_clique (T : sgraph) (bag : T -> {set G}) (S : {set G}) :
  clique_tree_decomposition bag -> 0 < #|S| -> clique S -> exists t : T, S \subset bag t.
Proof.
case=> -[[tf _] dec] _ S0 cS.
have sd := (bag_decomposition_forest_sdecompP tf bag).1 dec.
exact: (@decomp_clique G (Forest tf) bag sd S S0 cS).
Qed.

End Chordal.

Arguments chordal_by_cycles G : assert.
Arguments admits_clique_tree G : assert.
Arguments clique_tree_decomposition {G T} bag.
