(** * Extremal.migration.internal_vertices — frozen internal-vertex chain (library migration B2)

    Batch B, family [internal-vertices] (meta/library_primitives/internal-vertices.json).  [Legacy]
    freezes the conjecture-local helper [xe2_internal_path_vertices] verbatim as it
    stood at 9e03072, before the migration: the vertices of [p] other than [x] and
    [y].  The live helper now unfolds to [GTBase.walks_paths.seq_interior x y p].
    [XE2Legacy] freezes the affected chain of row [erdos_915_statement], the
    statement included, with the wave prefix dropped from the copied names and
    the frozen helper referred to as [Legacy.xe2_internal_path_vertices].
    Definitions that do not reach the helper (edge counts, path edge sets, edge
    disjointness) are the live, unchanged ones.

    The frozen helper is a boolean comprehension and [seq_interior] a set
    difference: they are extensionally equal, not convertible.
    [xe2_internal_path_vertices_compat] proves the equality by membership
    ([in_seq_interior]); the chain certificates transport it under the binders.
    Source hashes, the exact substitutions and the per-row theorem names are
    recorded in meta/migration_reports/internal_vertices.md. *)

From GTBase Require Import base.
From Extremal.conjectures Require Import X4 XE2.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Legacy.

Definition xe2_internal_path_vertices (G : sgraph) (x y : G) (p : seq G) : {set G} :=
  [set v : G | [&& v \in p, v != x & v != y]].

End Legacy.

Module XE2Legacy.

Definition paths_internally_disjoint
    (G : sgraph) (m : nat) (x y : G) (P : 'I_m -> seq G) : Prop :=
  forall i j : 'I_m, i != j ->
    [disjoint Legacy.xe2_internal_path_vertices x y (P i)
            & Legacy.xe2_internal_path_vertices x y (P j)].

Definition statement : Prop :=
  forall (n m : nat) (G : sgraph),
    #|G| = 1 + n * (m - 1) ->
    x4_edge_count G = 1 + n * 'C(m, 2) ->
    exists x y : G, exists P : 'I_m -> seq G,
      x != y /\
      (forall i : 'I_m,
        if P i is z :: p then z = x /\ last z p = y /\ path (--) z p else False) /\
      paths_internally_disjoint x y P /\
      xe2_paths_edge_disjoint P.

End XE2Legacy.

(** ** Certificates *)

Lemma xe2_internal_path_vertices_compat (G : sgraph) (x y : G) (p : seq G) :
  Legacy.xe2_internal_path_vertices x y p = xe2_internal_path_vertices x y p.
Proof. by apply/setP => z; rewrite /xe2_internal_path_vertices in_seq_interior inE. Qed.

Lemma xe2_paths_internally_disjoint_compat
    (G : sgraph) (m : nat) (x y : G) (P : 'I_m -> seq G) :
  XE2Legacy.paths_internally_disjoint x y P <-> xe2_paths_internally_disjoint x y P.
Proof.
rewrite /XE2Legacy.paths_internally_disjoint /xe2_paths_internally_disjoint.
by split=> h i j ij; move: (h i j ij); rewrite !xe2_internal_path_vertices_compat.
Qed.

Lemma erdos_915_statement_compat : XE2Legacy.statement <-> erdos_915_statement.
Proof.
rewrite /XE2Legacy.statement /erdos_915_statement.
split=> h n m G cardG edges; have [x [y [P [xy [ends [dis edis]]]]]] := h n m G cardG edges;
  exists x, y, P; do !split=> //; exact/xe2_paths_internally_disjoint_compat.
Qed.
