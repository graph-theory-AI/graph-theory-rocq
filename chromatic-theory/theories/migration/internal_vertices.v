(** * Chromatic.migration.internal_vertices — frozen internal-vertex chain (library migration B2)

    Batch B, family [internal-vertices] (meta/library_primitives/internal-vertices.json).  [Legacy]
    freezes the conjecture-local helper [x157_path_internal] verbatim as it stood
    at 9e03072, before the migration; the live helper now unfolds to
    [GTBase.walks_paths.seq_interior x y p].  [X157Legacy] freezes the affected
    chain of row [local_connectivity_k_colouring_polytime_statement], the
    statement included: the copies drop the wave prefix of their names and refer
    to the frozen helper as [Legacy.x157_path_internal], so no frozen body
    resolves through a live helper of this family.  Definitions that do not reach
    the helper (simple x-y paths, the output decoding) are the live, unchanged
    ones.

    [seq_interior x y p] is [seq_vertices p :\: [set x; y]] and [seq_vertices p]
    is [[set:: p]], which unfolds to the frozen comprehension [[set z : G | z \in p]];
    so every live definition is convertible to its frozen copy and the
    certificates below are kernel-checked conversions.  Source hashes, the exact
    substitutions and the per-row theorem names are recorded in
    meta/migration_reports/internal_vertices.md. *)

From Chromatic.conjectures Require Import X157.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Legacy.

Definition x157_path_internal (G : sgraph) (x y : G) (p : seq G) : {set G} :=
  [set z : G | z \in p] :\: [set x; y].

End Legacy.

Module X157Legacy.

Definition internally_disjoint_xy_paths
    (G : sgraph) (x y : G) (m : nat) : Prop :=
  exists route : 'I_m -> seq G,
    (forall i : 'I_m, x157_simple_xy_path x y (route i)) /\
    forall i j : 'I_m,
      i != j ->
      [disjoint Legacy.x157_path_internal x y (route i)
       & Legacy.x157_path_internal x y (route j)].

Definition max_local_connectivity_at_most (G : sgraph) (k : nat) : Prop :=
  forall (x y : G) (m : nat),
    x != y -> internally_disjoint_xy_paths x y m -> m <= k.

Definition polytime_colouring_or_none (k : nat) : Prop :=
  polytime_outputs_graph_on
    (fun G : sgraph => k_connected G k /\ max_local_connectivity_at_most G k)
    (x157_output_k_colouring_or_none k).

Definition statement : Prop :=
  forall k : nat, 4 <= k -> polytime_colouring_or_none k.

End X157Legacy.

(** ** Certificates *)

Lemma x157_path_internal_compat (G : sgraph) (x y : G) (p : seq G) :
  Legacy.x157_path_internal x y p = x157_path_internal x y p.
Proof. by rewrite /x157_path_internal /seq_interior seq_verticesE. Qed.

Lemma x157_internally_disjoint_xy_paths_compat (G : sgraph) (x y : G) (m : nat) :
  X157Legacy.internally_disjoint_xy_paths x y m <-> x157_internally_disjoint_xy_paths x y m.
Proof. exact: iff_refl. Qed.

Lemma x157_max_local_connectivity_at_most_compat (G : sgraph) (k : nat) :
  X157Legacy.max_local_connectivity_at_most G k <-> x157_max_local_connectivity_at_most G k.
Proof. exact: iff_refl. Qed.

Lemma x157_polytime_colouring_or_none_compat (k : nat) :
  X157Legacy.polytime_colouring_or_none k <-> x157_polytime_colouring_or_none k.
Proof. exact: iff_refl. Qed.

Lemma local_connectivity_k_colouring_polytime_statement_compat :
  X157Legacy.statement <-> local_connectivity_k_colouring_polytime_statement.
Proof. exact: iff_refl. Qed.
