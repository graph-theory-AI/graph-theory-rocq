(** A7 edge counts: the frozen public count [GTBase.finite_graph.fg_edge_count], an enrolled
    repository source pinned at ae0e605 (meta/library_primitives/edge-count.json). Baseline,
    hashes and exact substitutions are recorded in meta/migration_reports/edge_count.spec.json.
    [fg_edges] itself is unchanged; [fg_edgesE] relates it to [E(G)]. *)
From GTBase Require Import base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Legacy.

Definition fg_edge_count (G : sgraph) : nat := #|fg_edges G|.

End Legacy.

Lemma fg_edge_count_compat (G : sgraph) : Legacy.fg_edge_count G = fg_edge_count G.
Proof. exact: card_fg_edges. Qed.
