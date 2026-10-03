(** * GTMisc.migration.spanning_trees — frozen labelled spanning-tree helpers, Records, wrappers
    and rows of X167 / X168 (library migration B18)

    Family [spanning-tree] (meta/library_primitives/spanning-tree.json).  [Legacy] freezes, verbatim
    as they stood at the B18 baseline 7848021, the two helpers [x167_spanning_tree] and
    [x168_spanning_tree] ([T \subset fg_edges G /\ is_tree [set: fg_labelled_sgraph T]]: a set of
    edges of [G] whose labelled graph on the WHOLE carrier of [G] is an upstream tree).  The live
    helpers now unfold to the public [GTBase.spanning_trees.fg_spanning_tree], the same body, so both
    certificates are conversions.  [X167Legacy] and [X168Legacy] freeze the complete chains over the
    frozen helpers: the five-field Records [x167_extension_system] / [x168_extension_system]
    (auxiliary dimension, inequality index, its cardinality bound by [facets], and the two linking
    fields concluding [True], which are the documented defects of both rows and stay literal), the
    existence wrappers [x167_spanning_tree_polytope_xc] / [x168_spanning_tree_polytope_xc] and the two
    rows with every guard in order (whole-graph connectivity and the fixed-surface embedding; the
    proper-minor-closed class, membership and connectivity).  Frozen and live Records are nominally
    distinct types: the certificates transport witnesses field by field in both directions.

    [X168Original] composes the complete pre-C11, pre-B18 row: C11 (family proper-minor-closed-class,
    certificate [GTMisc.migration.minor_classes], bound here as [Module C11]) froze the old
    minor-class body but its per-row snapshot still calls the live wrapper; the Original uses
    C11's frozen class together with this family's frozen wrapper, and is certified end to end.  No
    guard, status or documented defect changes; both rows stay BLOCKED (KNOWN UNFAITHFUL).  Hashes and
    substitutions: meta/migration_reports/spanning_trees.md. *)

From GraphTheory Require Import minor.
From GTBase Require Import base minor_classes spanning_trees.
From GTMisc.migration Require minor_classes.
From GTMisc.conjectures Require Import X167 X168.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** C11's certificate, bound explicitly: its frozen minor-class body is reused by the Original. *)
Module C11 := GTMisc.migration.minor_classes.

Module Legacy.

Definition x167_spanning_tree (G : sgraph) (T : {set {set G}}) : Prop :=
  T \subset fg_edges G /\
  is_tree [set: fg_labelled_sgraph T].

Definition x168_spanning_tree (G : sgraph) (T : {set {set G}}) : Prop :=
  T \subset fg_edges G /\
  is_tree [set: fg_labelled_sgraph T].

End Legacy.

Module X167Legacy.

Record x167_extension_system (G : sgraph) (facets : nat) := {
  x167_aux_dim : nat;
  x167_ineq_index : finType;
  x167_ineq_count : #|{: x167_ineq_index}| <= facets;
  x167_accepts_tree : forall T : {set {set G}}, Legacy.x167_spanning_tree T -> True;
  x167_rejects_non_tree : forall T : {set {set G}}, ~ Legacy.x167_spanning_tree T -> True
}.

Definition x167_spanning_tree_polytope_xc (G : sgraph) (facets : nat) : Prop :=
  exists _ : X167Legacy.x167_extension_system G facets, True.

Definition fixed_surface_spanning_tree_polytope_linear_xc_statement : Prop :=
  forall surface : nat,
    exists C : nat,
      forall G : sgraph,
        connected [set: G] ->
        x167_embedded_in_fixed_surface surface G ->
        X167Legacy.x167_spanning_tree_polytope_xc G (C * #|G|.+1).

End X167Legacy.

Module X168Legacy.

Record x168_extension_system (G : sgraph) (facets : nat) := {
  x168_aux_dim : nat;
  x168_ineq_index : finType;
  x168_ineq_count : #|{: x168_ineq_index}| <= facets;
  x168_accepts_tree : forall T : {set {set G}}, Legacy.x168_spanning_tree T -> True;
  x168_rejects_non_tree : forall T : {set {set G}}, ~ Legacy.x168_spanning_tree T -> True
}.

Definition x168_spanning_tree_polytope_xc (G : sgraph) (facets : nat) : Prop :=
  exists _ : X168Legacy.x168_extension_system G facets, True.

Definition minor_closed_spanning_tree_polytope_linear_xc_statement : Prop :=
  forall C : sgraph -> Prop,
    x168_proper_minor_closed_class C ->
    exists K : nat,
      forall G : sgraph,
        C G ->
        connected [set: G] ->
        X168Legacy.x168_spanning_tree_polytope_xc G (K * #|G|.+1).

End X168Legacy.

Module X168Original.

Definition minor_closed_spanning_tree_polytope_linear_xc_statement : Prop :=
  forall C : sgraph -> Prop,
    C11.Legacy.x168_proper_minor_closed_class C ->
    exists K : nat,
      forall G : sgraph,
        C G ->
        connected [set: G] ->
        X168Legacy.x168_spanning_tree_polytope_xc G (K * #|G|.+1).

End X168Original.

(** ** Certificates *)

(** The helpers: the body of the public [fg_spanning_tree], by conversion. *)
Lemma x167_spanning_tree_compat (G : sgraph) (T : {set {set G}}) :
  Legacy.x167_spanning_tree T <-> x167_spanning_tree T.
Proof. exact: iff_refl. Qed.

Lemma x168_spanning_tree_compat (G : sgraph) (T : {set {set G}}) :
  Legacy.x168_spanning_tree T <-> x168_spanning_tree T.
Proof. exact: iff_refl. Qed.

(** The Records: nominally distinct types whose five fields convert one by one; the explicit
    witness transports keep every field (dimension, index, cardinality bound and the two linking
    fields concluding [True]). *)
Definition x167_extension_system_to_live (G : sgraph) (facets : nat)
    (r : X167Legacy.x167_extension_system G facets) : x167_extension_system G facets :=
  @Build_x167_extension_system G facets (X167Legacy.x167_aux_dim r) (X167Legacy.x167_ineq_index r)
    (X167Legacy.x167_ineq_count r) (X167Legacy.x167_accepts_tree r) (X167Legacy.x167_rejects_non_tree r).

Definition x167_extension_system_of_live (G : sgraph) (facets : nat)
    (r : x167_extension_system G facets) : X167Legacy.x167_extension_system G facets :=
  @X167Legacy.Build_x167_extension_system G facets (x167_aux_dim r) (x167_ineq_index r)
    (x167_ineq_count r) (x167_accepts_tree r) (x167_rejects_non_tree r).

Lemma x167_extension_system_compat (G : sgraph) (facets : nat) :
  inhabited (X167Legacy.x167_extension_system G facets) <-> inhabited (x167_extension_system G facets).
Proof.
by split=> -[r]; constructor; [exact: x167_extension_system_to_live r | exact: x167_extension_system_of_live r].
Qed.

Definition x168_extension_system_to_live (G : sgraph) (facets : nat)
    (r : X168Legacy.x168_extension_system G facets) : x168_extension_system G facets :=
  @Build_x168_extension_system G facets (X168Legacy.x168_aux_dim r) (X168Legacy.x168_ineq_index r)
    (X168Legacy.x168_ineq_count r) (X168Legacy.x168_accepts_tree r) (X168Legacy.x168_rejects_non_tree r).

Definition x168_extension_system_of_live (G : sgraph) (facets : nat)
    (r : x168_extension_system G facets) : X168Legacy.x168_extension_system G facets :=
  @X168Legacy.Build_x168_extension_system G facets (x168_aux_dim r) (x168_ineq_index r)
    (x168_ineq_count r) (x168_accepts_tree r) (x168_rejects_non_tree r).

Lemma x168_extension_system_compat (G : sgraph) (facets : nat) :
  inhabited (X168Legacy.x168_extension_system G facets) <-> inhabited (x168_extension_system G facets).
Proof.
by split=> -[r]; constructor; [exact: x168_extension_system_to_live r | exact: x168_extension_system_of_live r].
Qed.

(** The existence wrappers, by witness transport. *)
Lemma x167_spanning_tree_polytope_xc_compat (G : sgraph) (facets : nat) :
  X167Legacy.x167_spanning_tree_polytope_xc G facets <-> x167_spanning_tree_polytope_xc G facets.
Proof.
by split=> -[r _]; [exists (x167_extension_system_to_live r) | exists (x167_extension_system_of_live r)].
Qed.

Lemma x168_spanning_tree_polytope_xc_compat (G : sgraph) (facets : nat) :
  X168Legacy.x168_spanning_tree_polytope_xc G facets <-> x168_spanning_tree_polytope_xc G facets.
Proof.
by split=> -[r _]; [exists (x168_extension_system_to_live r) | exists (x168_extension_system_of_live r)].
Qed.

(** arxiv:1604.07976#00 (unchanged; the row stays BLOCKED). *)
Lemma fixed_surface_spanning_tree_polytope_linear_xc_statement_compat :
  X167Legacy.fixed_surface_spanning_tree_polytope_linear_xc_statement <->
  fixed_surface_spanning_tree_polytope_linear_xc_statement.
Proof.
split=> h s; have [C hC] := h s; exists C => G cG eG.
- by apply/x167_spanning_tree_polytope_xc_compat; exact: hC.
- by apply/x167_spanning_tree_polytope_xc_compat; exact: hC.
Qed.

(** arxiv:1604.07976#01 (unchanged; the row stays BLOCKED): the per-row copy over this family's
    frozen chain and the live minor-class alias. *)
Lemma minor_closed_spanning_tree_polytope_linear_xc_statement_compat :
  X168Legacy.minor_closed_spanning_tree_polytope_linear_xc_statement <->
  minor_closed_spanning_tree_polytope_linear_xc_statement.
Proof.
split=> h C pC; have [K hK] := h C pC; exists K => G cG conn.
- by apply/x168_spanning_tree_polytope_xc_compat; exact: hK.
- by apply/x168_spanning_tree_polytope_xc_compat; exact: hK.
Qed.

(** The complete pre-C11, pre-B18 row, end to end: C11's frozen class through its own certificate
    [C11.x168_proper_minor_closed_class_compat], the wrapper through witness transport. *)
Lemma minor_closed_spanning_tree_polytope_linear_xc_statement_original_compat :
  X168Original.minor_closed_spanning_tree_polytope_linear_xc_statement <->
  minor_closed_spanning_tree_polytope_linear_xc_statement.
Proof.
split=> h C /C11.x168_proper_minor_closed_class_compat pC; have [K hK] := h C pC.
- by exists K => G cG conn; apply/x168_spanning_tree_polytope_xc_compat; exact: hK.
- by exists K => G cG conn; apply/x168_spanning_tree_polytope_xc_compat; exact: hK.
Qed.

Print Assumptions x167_spanning_tree_compat.
Print Assumptions x168_spanning_tree_compat.
Print Assumptions x167_extension_system_to_live.
Print Assumptions x167_extension_system_of_live.
Print Assumptions x167_extension_system_compat.
Print Assumptions x168_extension_system_to_live.
Print Assumptions x168_extension_system_of_live.
Print Assumptions x168_extension_system_compat.
Print Assumptions x167_spanning_tree_polytope_xc_compat.
Print Assumptions x168_spanning_tree_polytope_xc_compat.
Print Assumptions fixed_surface_spanning_tree_polytope_linear_xc_statement_compat.
Print Assumptions minor_closed_spanning_tree_polytope_linear_xc_statement_compat.
Print Assumptions minor_closed_spanning_tree_polytope_linear_xc_statement_original_compat.
