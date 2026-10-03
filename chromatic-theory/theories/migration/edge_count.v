(** A7 edge counts: the frozen chromatic XE1 helper. Baseline, hashes and exact substitutions are
    recorded in meta/migration_reports/edge_count.spec.json. [Legacy.xe1_edge_count] is the post-M1
    body (it counts M1's alias [xe1_edge_set]); no corpus row reaches it. *)
From GTBase Require Import base.
From Chromatic.conjectures Require Import XE1.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Legacy.

Definition xe1_edge_count (G : sgraph) : nat := #|xe1_edge_set G|.

End Legacy.

Lemma xe1_edge_count_compat (G : sgraph) : Legacy.xe1_edge_count G = xe1_edge_count G.
Proof. by []. Qed.
