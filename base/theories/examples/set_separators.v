(** * GTBase.examples.set_separators — public-only client of GTBase.set_separators (B26)

    Compiles against public modules alone (no conjecture module).  Corner cases of upstream
    [separator]: empty endpoint sets and the empty graph, the whole separator, overlapping singleton
    endpoint sets (the empty separator fails, the common vertex succeeds), a separator containing an
    endpoint, two nonempty endpoint sets in a graph without edges separated by the empty set, the edge
    of [K_2] with and without an endpoint in the separator, monotonicity, symmetry, and the difference
    from upstream [separates], which forbids endpoints in the separator. *)

From mathcomp Require Import all_boot.
From GraphTheory Require Import preliminaries digraph sgraph connectivity.
From GTBase Require Import base walks_paths bag_decompositions set_separators.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Notation k2_0 := (@Ordinal 2 0 isT).
Local Notation k2_1 := (@Ordinal 2 1 isT).
Local Notation k3_0 := (@Ordinal 3 0 isT).

(** Empty endpoint sets, and every triple of sets in the empty graph. *)
Lemma example_set0 (A : {set 'K_3}) : separator 'K_3 set0 [set k3_0] A /\ separator 'K_3 [set k3_0] set0 A.
Proof. by split; [exact: separator_set0l | exact: separator_set0r]. Qed.

Lemma example_empty_graph (X Y A : {set 'K_0}) : separator 'K_0 X Y A.
Proof. by move=> a; have := ltn_ord a; rewrite ltn0. Qed.

(** The whole carrier separates anything. *)
Lemma example_whole (X Y : {set 'K_3}) : separator 'K_3 X Y [set: 'K_3].
Proof. exact: separator_setT. Qed.

(** Overlapping singleton endpoint sets: the one-vertex path must be hit. *)
Lemma example_overlap :
  ~ separator 'K_3 [set k3_0] [set k3_0] set0 /\ separator 'K_3 [set k3_0] [set k3_0] [set k3_0].
Proof. by split; [move/separator_seq1; rewrite inE | apply/separator_seq1; exact: set11]. Qed.

(** An endpoint in the separator is allowed, and the edge of [K_2] is cut by it. *)
Lemma example_K2_endpoint : separator 'K_2 [set k2_0] [set k2_1] [set k2_0].
Proof. exact: separator_endpointL. Qed.

Lemma example_K2_other_endpoint : separator 'K_2 [set k2_0] [set k2_1] [set k2_1].
Proof. exact: separator_endpointR. Qed.

(** Without an endpoint, the edge of [K_2] is a path avoiding the empty separator. *)
Lemma example_K2_empty_fails : ~ separator 'K_2 [set k2_0] [set k2_1] set0.
Proof.
have e : (k2_0 : 'K_2) -- k2_1 by [].
by move=> sep; have [s] := sep k2_0 k2_1 (edgep e) (set11 _) (set11 _); rewrite inE.
Qed.

(** A graph without edges: two nonempty endpoint sets are separated by the empty set. *)
Lemma example_no_edges : separator two_isolated [set (ord0 : two_isolated)] [set ord_max] set0.
Proof.
apply/seq_separatorP => -[|x [|z q]] //.
- by move=> /seq_set_path_seq1; rewrite !inE => /andP[/eqP-> /eqP/(congr1 val)].
- by move=> [_ [_ [_ /andP[]]]].
Qed.

(** Monotonicity and symmetry. *)
Lemma example_mono : separator 'K_2 [set k2_0] [set k2_1] [set: 'K_2].
Proof. exact: separator_mono (subsetT _) example_K2_endpoint. Qed.

Lemma example_sym : separator 'K_2 [set k2_1] [set k2_0] [set k2_0].
Proof. exact: separator_sym example_K2_endpoint. Qed.

(** [separator] is not upstream [separates]: the latter rejects an endpoint in the separator. *)
Lemma example_not_separates :
  separator 'K_2 [set k2_0] [set k2_1] [set k2_0] /\ ~ separates (k2_0 : 'K_2) k2_1 [set k2_0].
Proof. exact: separator_not_separates. Qed.

Print Assumptions example_empty_graph.
Print Assumptions example_overlap.
Print Assumptions example_K2_empty_fails.
Print Assumptions example_no_edges.
Print Assumptions example_sym.
Print Assumptions example_not_separates.
