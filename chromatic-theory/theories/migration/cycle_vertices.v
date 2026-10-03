(** * Chromatic.migration.cycle_vertices — frozen vertex supports of X153 and XE1 (library migration B12)

    Batch B, family [cycle-vertices] (meta/library_primitives/cycle-vertices.json).  The family reuses
    B1's canonical [GTBase.walks_paths.seq_vertices] (registry path-vertices) and adds no primitive,
    fidelity owner or validity guard.  [Legacy] freezes, verbatim as they stood at the B12 baseline
    13c00aa, X153's [x153_cycle_vertices] ([[set v | v \in c]]) and XE1's [xe1_vertices_of_seq]
    ([[set v : G | v \in c]]).  The live helpers now unfold to [seq_vertices c], MathComp's [[set:: c]],
    which is the same comprehension, so the certificates are kernel-checked conversions; the helper
    certificates go through [seq_verticesE], as in B1.  [X153Legacy] freezes the precoloured-lists chain
    and the list-critical row with this family's helper only.  XE1's helper is used by no row: it has
    its helper certificate and no row of its own.  The A7, B4 and B10 histories of XE1 are untouched.
    Hashes and substitutions: meta/migration_reports/cycle_vertices.md. *)

From GTBase Require Import base.
From Chromatic.conjectures Require Import X153 XE1.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Legacy.

Definition x153_cycle_vertices (G : sgraph) (c : seq G) : {set G} :=
  [set v | v \in c].

Definition xe1_vertices_of_seq (G : sgraph) (c : seq G) : {set G} :=
  [set v : G | v \in c].

End Legacy.

Module X153Legacy.

Definition cycle_precoloured_lists
    (G : sgraph) (C : finType) (L : G -> {set C}) (c1 c2 : seq G) : Prop :=
  forall v : G,
    if v \in Legacy.x153_cycle_vertices c1 :|: Legacy.x153_cycle_vertices c2
    then #|L v| = 1
    else 3 <= #|L v|.

Definition planar_girth5_two_cycles_list_critical_subgraph_statement : Prop :=
  forall k : nat,
    5 <= k ->
    exists K : nat,
      forall (G : sgraph) (C : finType) (L : G -> {set C}) (c1 c2 : seq G),
        wagner_planar G ->
        girth_geq G 5 ->
        x153_short_cycle k c1 ->
        x153_short_cycle k c2 ->
        cycle_precoloured_lists L c1 c2 ->
        ~ @list_colourable G C L ->
        exists S : {set G},
          [/\ #|S| <= K,
              Legacy.x153_cycle_vertices c1 \subset S,
              Legacy.x153_cycle_vertices c2 \subset S &
              ~ x153_list_colourable_induced L S].

End X153Legacy.

(** ** Certificates *)

Lemma x153_cycle_vertices_compat (G : sgraph) (c : seq G) :
  Legacy.x153_cycle_vertices c = x153_cycle_vertices c.
Proof. by rewrite /x153_cycle_vertices seq_verticesE. Qed.

Lemma xe1_vertices_of_seq_compat (G : sgraph) (c : seq G) :
  Legacy.xe1_vertices_of_seq c = xe1_vertices_of_seq c.
Proof. by rewrite /xe1_vertices_of_seq seq_verticesE. Qed.

Lemma x153_cycle_precoloured_lists_compat
    (G : sgraph) (C : finType) (L : G -> {set C}) (c1 c2 : seq G) :
  X153Legacy.cycle_precoloured_lists L c1 c2 <-> x153_cycle_precoloured_lists L c1 c2.
Proof. exact: iff_refl. Qed.

Lemma planar_girth5_two_cycles_list_critical_subgraph_statement_compat :
  X153Legacy.planar_girth5_two_cycles_list_critical_subgraph_statement <->
  planar_girth5_two_cycles_list_critical_subgraph_statement.
Proof. exact: iff_refl. Qed.

Print Assumptions x153_cycle_vertices_compat.
Print Assumptions xe1_vertices_of_seq_compat.
Print Assumptions planar_girth5_two_cycles_list_critical_subgraph_statement_compat.
