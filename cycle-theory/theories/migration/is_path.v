(** * Cycle.migration.is_path — frozen path-subgraph chain (library migration B7)

    Batch B, family [is-path] (meta/library_primitives/is-path.json), multigraph
    class.  [Legacy] freezes U6's helper [is_path] verbatim as it stood at
    632e0b1, before the migration: a nonempty, connected, acyclic edge set of
    arc-end degree at most two (U6's [acyclic], which is not migrated, stays the
    live one).  The live helper now unfolds to
    [Cycle.foundations.path_subgraphs.path_subgraph P], whose body is the same
    conjunction over an acyclicity predicate with U6's [acyclic] body, so the
    certificates below are kernel-checked conversions.  [U6Legacy] freezes
    [path_decomposition] (renamed [u6_path_decomposition], since U6's names carry
    no wave prefix) and the path-decomposition row, with its positivity,
    simplicity, connectivity, edge-partition and [(n + 1) %/ 2] guards.  Source
    hashes, the exact substitutions and the per-row theorem names are recorded in
    meta/migration_reports/is_path.md. *)

From GraphTheory Require Import mgraph.
From GTBase Require Import base.
From Cycle.conjectures Require Import U6.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Legacy.

Definition is_path (G : mgraph) (P : {set edge G}) : Prop :=
  [/\ P != set0, subgraph_connected P, acyclic P & forall v : G, (subdeg P v <= 2)%N].

End Legacy.

Module U6Legacy.

Definition u6_path_decomposition (G : mgraph) (D : seq {set edge G}) : Prop :=
  (forall P, P \in D -> Legacy.is_path P) /\ edge_partitionT D.

Definition decomposing_a_connected_graph_into_paths_statement : Prop :=
  forall G : mgraph,
    (0 < #|G|)%N -> (0 < #|edge G|)%N -> simple_mgraph G -> mconnected G ->
    exists D : seq {set edge G},
      u6_path_decomposition D /\ (size D <= (#|G| + 1) %/ 2)%N.

End U6Legacy.

(** ** Certificates *)

Lemma u6_is_path_compat (G : mgraph) (P : {set edge G}) : Legacy.is_path P <-> is_path P.
Proof. exact: iff_refl. Qed.

Lemma u6_path_decomposition_compat (G : mgraph) (D : seq {set edge G}) :
  U6Legacy.u6_path_decomposition D <-> path_decomposition D.
Proof. exact: iff_refl. Qed.

Lemma decomposing_a_connected_graph_into_paths_statement_compat :
  U6Legacy.decomposing_a_connected_graph_into_paths_statement <->
  decomposing_a_connected_graph_into_paths_statement.
Proof. exact: iff_refl. Qed.
