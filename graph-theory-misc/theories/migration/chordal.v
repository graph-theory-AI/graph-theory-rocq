(** * GTMisc.migration.chordal — B25 certificates: X169's clique-tree chordality and its row

    Frozen verbatim at the fixed B24 baseline 63be197: X169's [x169_chordal] (some supplied index
    graph and bag map form a clique tree: a tree-indexed bag decomposition with clique bags), its one
    forward chain [x169_polytime_decides_TS_connectivity] (a program with polynomially bounded cost
    decides token-sliding connectivity on the class of graphs that are chordal AND have a clique tree
    of degree at most [D]; the two existential witnesses stay separate) and the complete current row
    [token_sliding_chordal_clique_tree_degree_polytime_statement] ([forall k D]).  The row is
    disproved and its statement leg blocked: the decided predicate does not require the
    intermediate token-sliding states to be stable; that documented defect and the status are kept,
    not repaired.  Since B25 the live [x169_chordal] is a transparent alias of
    [GTBase.chordal.admits_clique_tree], the same body by conversion, so the certificates below are
    kernel-checked conversions.  The copies keep the live local supports [x169_clique_tree],
    [x169_clique_tree_degree_at_most] and [x169_token_sliding_connected] (not migrated).  The
    complete earlier row is C13's [GTMisc.migration.bag_decompositions.Legacy.
    token_sliding_chordal_clique_tree_degree_polytime_statement] (over C13's raw tree decomposition,
    clique tree, chordality, degree-bounded clique tree and polytime chain), reused with C13's
    certificate; a later A20 composition (stable sets and token sliding) is the coordinator's. *)

From GTBase Require Import base bag_decompositions chordal.
From GTMisc.conjectures Require Import X169.
From GTMisc.migration Require bag_decompositions.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module C13 := GTMisc.migration.bag_decompositions.

Module Legacy.

Definition x169_chordal (G : sgraph) : Prop :=
  exists (T : sgraph) (bag : T -> {set G}), x169_clique_tree bag.

End Legacy.

Module X169Legacy.

Definition x169_polytime_decides_TS_connectivity (k D : nat) : Prop :=
  polytime_decides_graph_on
    (fun G : sgraph => Legacy.x169_chordal G /\ x169_clique_tree_degree_at_most G D)
    (fun G : sgraph => x169_token_sliding_connected G k).

Definition token_sliding_chordal_clique_tree_degree_polytime_statement : Prop :=
  forall k D : nat, X169Legacy.x169_polytime_decides_TS_connectivity k D.

End X169Legacy.

Lemma x169_chordal_compat (G : sgraph) : Legacy.x169_chordal G <-> x169_chordal G.
Proof. exact: iff_refl. Qed.

Lemma x169_polytime_decides_TS_connectivity_compat (k D : nat) :
  X169Legacy.x169_polytime_decides_TS_connectivity k D <-> x169_polytime_decides_TS_connectivity k D.
Proof. exact: iff_refl. Qed.

Lemma token_sliding_chordal_clique_tree_degree_polytime_statement_compat :
  X169Legacy.token_sliding_chordal_clique_tree_degree_polytime_statement <->
  token_sliding_chordal_clique_tree_degree_polytime_statement.
Proof. exact: iff_refl. Qed.

(** The complete earlier row, reused from C13 with C13's own certificate. *)
Lemma token_sliding_chordal_clique_tree_degree_polytime_statement_original_compat :
  GTMisc.migration.bag_decompositions.Legacy.token_sliding_chordal_clique_tree_degree_polytime_statement <->
  token_sliding_chordal_clique_tree_degree_polytime_statement.
Proof. exact: C13.token_sliding_chordal_clique_tree_degree_polytime_statement_compat. Qed.

Print Assumptions x169_chordal_compat.
Print Assumptions x169_polytime_decides_TS_connectivity_compat.
Print Assumptions token_sliding_chordal_clique_tree_degree_polytime_statement_compat.
Print Assumptions token_sliding_chordal_clique_tree_degree_polytime_statement_original_compat.
