(** * Digraph.migration.cycle_vertices — frozen vertex support of X19 (library migration B12)

    Batch B, family [cycle-vertices] (meta/library_primitives/cycle-vertices.json).  The family reuses
    B1's canonical [GTBase.walks_paths.seq_vertices] (registry path-vertices) and adds no primitive,
    fidelity owner or validity guard.  [Legacy] freezes, verbatim as it stood at the B12 baseline
    13c00aa, X19's [x19_cycle_vertices] ([[set v | v \in c]] over a [diGraphType] carrier).  The live
    helper now unfolds to [seq_vertices c] (X19.v imports only the small [GTBase.walks_paths], as B1's
    X2 does, not the broad base module), the same comprehension, so the certificates are kernel-checked
    conversions; the helper certificate goes through [seq_verticesE].  [X19Legacy] freezes the
    vertex-disjoint dicycle chain and Lichiardopol's row with this family's helper only.  The
    disjointness clause still quantifies over distinct list members ([c != d]); it is not strengthened
    to distinct indices.  Hashes and substitutions: meta/migration_reports/cycle_vertices.md. *)

From HB Require Import structures.
From mathcomp Require Import all_boot.
From Digraph Require Import prelude digraph oriented dipath.
From Digraph.conjectures Require Import classic_core.
From GTBase Require Import walks_paths.
From Digraph.conjectures Require Import X19.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Legacy.

Definition x19_cycle_vertices (D : diGraphType) (c : seq D) : {set D} :=
  [set v | v \in c].

End Legacy.

Module X19Legacy.

Definition vertex_disjoint_dicycles
    (D : diGraphType) (cs : seq (seq D)) : Prop :=
  all (@dicycle D) cs /\
  forall c d : seq D, c \in cs -> d \in cs -> c != d ->
    [disjoint Legacy.x19_cycle_vertices c & Legacy.x19_cycle_vertices d].

Definition lichiardopol_distinct_length_dicycle_packing_statement : Prop :=
  forall k : nat, exists g : nat,
    forall D : diGraphType,
      0 < #|D| ->
      x19_loopless D ->
      (forall v : D, g <= outdeg v) ->
      exists cs : seq (seq D),
        size cs = k /\
        vertex_disjoint_dicycles cs /\
        x19_distinct_cycle_lengths cs.

End X19Legacy.

(** ** Certificates *)

Lemma x19_cycle_vertices_compat (D : diGraphType) (c : seq D) :
  Legacy.x19_cycle_vertices c = x19_cycle_vertices c.
Proof. by rewrite /x19_cycle_vertices seq_verticesE. Qed.

Lemma x19_vertex_disjoint_dicycles_compat (D : diGraphType) (cs : seq (seq D)) :
  X19Legacy.vertex_disjoint_dicycles cs <-> x19_vertex_disjoint_dicycles cs.
Proof. exact: iff_refl. Qed.

Lemma lichiardopol_distinct_length_dicycle_packing_statement_compat :
  X19Legacy.lichiardopol_distinct_length_dicycle_packing_statement <->
  lichiardopol_distinct_length_dicycle_packing_statement.
Proof. exact: iff_refl. Qed.

Print Assumptions x19_cycle_vertices_compat.
Print Assumptions lichiardopol_distinct_length_dicycle_packing_statement_compat.
