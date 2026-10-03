(** * Extremal.migration.path_edges — frozen path-edge set of XE2 #915 (library migration B8)

    Batch B, family [path-edges] (meta/library_primitives/path-edges.json),
    finite-support class.  [Legacy] freezes XE2's [xe2_path_edge_set] verbatim as it
    stood at the B8 baseline 048c768: the existential image of the consecutive pairs
    [zip p (behead p)] under [(x, y) |-> [set x; y]].  The live helper now unfolds to
    [GTBase.walks_paths.seq_edge_set p], the support of the same pairs; the two are
    equal for EVERY sequence but not convertible, so [xe2_path_edge_set_compat] is a
    proved equality ([seq_edge_set_image]) and the chain and row certificates
    rewrite with it.  [XE2Legacy] freezes [xe2_paths_edge_disjoint] and #915 with
    B2's live internal-disjointness clause; [XE2Original] composes B2's frozen
    [XE2Legacy.paths_internally_disjoint] (Extremal.migration.internal_vertices)
    with this family's frozen edge-disjointness, the complete pre-B2, pre-B8 row.
    The paths stay nonempty endpoint walks, with no uniqueness added, and all n/m
    arithmetic is unchanged.  Hashes and substitutions:
    meta/migration_reports/path_edges.md. *)

From GTBase Require Import base.
From Extremal.conjectures Require Import X4 XE2.
From Extremal.migration Require internal_vertices.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Legacy.

Definition xe2_path_edge_set (G : sgraph) (p : seq G) : {set {set G}} :=
  [set e : {set G} |
      [exists xy : G * G, (xy \in zip p (behead p)) && (e == [set xy.1; xy.2])]].

End Legacy.

Module XE2Legacy.

Definition paths_edge_disjoint
    (G : sgraph) (m : nat) (P : 'I_m -> seq G) : Prop :=
  forall i j : 'I_m, i != j ->
    [disjoint Legacy.xe2_path_edge_set (P i) & Legacy.xe2_path_edge_set (P j)].

Definition erdos_915_statement : Prop :=
  forall (n m : nat) (G : sgraph),
    #|G| = 1 + n * (m - 1) ->
    x4_edge_count G = 1 + n * 'C(m, 2) ->
    exists x y : G, exists P : 'I_m -> seq G,
      x != y /\
      (forall i : 'I_m,
        if P i is z :: p then z = x /\ last z p = y /\ path (--) z p else False) /\
      xe2_paths_internally_disjoint x y P /\
      paths_edge_disjoint P.

End XE2Legacy.

Module XE2Original.

Definition erdos_915_statement : Prop :=
  forall (n m : nat) (G : sgraph),
    #|G| = 1 + n * (m - 1) ->
    x4_edge_count G = 1 + n * 'C(m, 2) ->
    exists x y : G, exists P : 'I_m -> seq G,
      x != y /\
      (forall i : 'I_m,
        if P i is z :: p then z = x /\ last z p = y /\ path (--) z p else False) /\
      Extremal.migration.internal_vertices.XE2Legacy.paths_internally_disjoint x y P /\
      XE2Legacy.paths_edge_disjoint P.

End XE2Original.

(** ** Certificates *)

(** Not a conversion: the existential image of the consecutive pairs is their support. *)
Lemma xe2_path_edge_set_compat (G : sgraph) (p : seq G) :
  Legacy.xe2_path_edge_set p = xe2_path_edge_set p.
Proof. by rewrite /xe2_path_edge_set seq_edge_set_image. Qed.

Lemma xe2_paths_edge_disjoint_compat (G : sgraph) (m : nat) (P : 'I_m -> seq G) :
  XE2Legacy.paths_edge_disjoint P <-> xe2_paths_edge_disjoint P.
Proof.
rewrite /XE2Legacy.paths_edge_disjoint /xe2_paths_edge_disjoint.
by split=> h i j ij; move: (h i j ij); rewrite !xe2_path_edge_set_compat.
Qed.

Lemma erdos_915_statement_compat : XE2Legacy.erdos_915_statement <-> erdos_915_statement.
Proof.
rewrite /XE2Legacy.erdos_915_statement /erdos_915_statement.
split=> h n m G cardG edges; have [x [y [P [xy [ends [dis edis]]]]]] := h n m G cardG edges;
  exists x, y, P; do !split=> //; exact/xe2_paths_edge_disjoint_compat.
Qed.

(** Before B2 and B8: B2's frozen internal disjointness and this family's frozen edge
    disjointness. *)
Lemma erdos_915_statement_original_compat :
  XE2Original.erdos_915_statement <-> erdos_915_statement.
Proof.
rewrite /XE2Original.erdos_915_statement /erdos_915_statement.
split=> h n m G cardG edges; have [x [y [P [xy [ends [dis edis]]]]]] := h n m G cardG edges;
  exists x, y, P; do !split=> //;
  first [exact/Extremal.migration.internal_vertices.xe2_paths_internally_disjoint_compat
        | exact/xe2_paths_edge_disjoint_compat].
Qed.

Print Assumptions xe2_path_edge_set_compat.
Print Assumptions xe2_paths_edge_disjoint_compat.
Print Assumptions erdos_915_statement_compat.
Print Assumptions erdos_915_statement_original_compat.
