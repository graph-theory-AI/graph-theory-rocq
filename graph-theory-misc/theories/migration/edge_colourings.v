(** * GTMisc.migration.edge_colourings -- frozen proper edge colourings (C6, 2026-10-03)

    Family: "proper_edge_colouring" (meta/library_primitives/proper-edge-colouring.json);
    misc rows of X14 (Andersen) and X62.  Canonical primitive:
    [GTBase.edge_colourings.proper_edge_colouring] (set maps over an [eqType]
    palette); public client base/theories/examples/edge_colourings.v;
    generated report meta/migration_reports/proper_edge_colouring.md (from
    proper_edge_colouring.spec.json); record meta/LIBRARY_MIGRATION_C6.md.

    ** Frozen source

    [Legacy] freezes the migrated helper [x14_proper_edge_colouring] verbatim
    as it stood at 3011c28 (the "distinct edges that are not disjoint get
    different colours" form over [{set G}] maps into a finite palette),
    together with the pre-M1 comprehension body of [x14_edge_set] (X14.v at
    061154c; M1 froze the same text as [GTMisc.migration.simple_edges.Legacy.exists_edge_set]
    and C1 as [GTMisc.migration.matching.Legacy.x14_edge_set]; the live name has
    been the transparent alias [sg_edge_set G] since M1), so that the frozen
    helper resolves through no alias of any migration.  [X14Legacy] and
    [X62Legacy] freeze the two rows with the reference to the helper replaced
    by its frozen copy; [x14_rainbow_path], [x14_genuine_path],
    [x14_path_edges] and [x62_edges_covered_by_paths] reach no helper of this
    family and are used live (the raw-path vocabulary is family B6's).

    ** Certificates

    [x14_edge_set_compat] is the chain certificate of the edge set;
    [x14_proper_edge_colouring_compat] the helper certificate (through
    [proper_edge_colouring_meetP]); [andersen_rainbow_path_statement_compat]
    and [rainbow_paths_linear_edge_cover_statement_compat] the row certificates.
    Andersen's [n.-1] VERTICES and [2 <= n] guard, and X62's uniform outer
    constant, are unchanged.

    Axiom-free: no Axiom/Parameter/Admitted; Print Assumptions at the end. *)

From GTBase Require Import base common edge_colourings.
From GTMisc.conjectures Require Import X14 X62.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Legacy.

(** [x14_edge_set] before M1: X14.v lines 11-13 at 061154c, verbatim. *)
Definition x14_edge_set (G : sgraph) : {set {set G}} :=
  [set e : {set G} |
      [exists x : G, [exists y : G, (x -- y) && (e == [set x; y])]]].

(** X14.v lines 37-44 at 3011c28, verbatim; [x14_edge_set] is the frozen
    comprehension above. *)
Definition x14_proper_edge_colouring
    (G : sgraph) (C : finType) (col : {set G} -> C) : Prop :=
  forall e f : {set G},
    e \in x14_edge_set G ->
    f \in x14_edge_set G ->
    e != f ->
    ~~ [disjoint e & f] ->
    col e != col f.

End Legacy.

(** ** Helper certificates *)

Lemma x14_edge_set_compat (G : sgraph) :
  Legacy.x14_edge_set G = x14_edge_set G.
Proof. by rewrite /x14_edge_set sg_edge_setE. Qed.

(** The migrated helper: the frozen "not disjoint" form is the canonical
    endpoint form. *)
Lemma x14_proper_edge_colouring_compat
    (G : sgraph) (C : finType) (col : {set G} -> C) :
  Legacy.x14_proper_edge_colouring col <-> x14_proper_edge_colouring col.
Proof.
rewrite /Legacy.x14_proper_edge_colouring x14_edge_set_compat
  /x14_proper_edge_colouring.
exact: iff_sym (proper_edge_colouring_meetP col).
Qed.

(** ** The two rows *)

Module X14Legacy.

(** X14.v lines 93-98 at 3011c28 with [x14_proper_edge_colouring] ->
    [Legacy.x14_proper_edge_colouring]. *)
Definition andersen_rainbow_path_statement : Prop :=
  forall (n : nat) (C : finType) (col : {set complete n} -> C),
    2 <= n ->
    @Legacy.x14_proper_edge_colouring (complete n) C col ->
    exists p : seq (complete n),
      @x14_rainbow_path (complete n) C col p /\ size p = n.-1.

End X14Legacy.

Module X62Legacy.

(** X62.v lines 37-44 at 3011c28 with [x14_proper_edge_colouring] ->
    [Legacy.x14_proper_edge_colouring]. *)
Definition rainbow_paths_linear_edge_cover_statement : Prop :=
  exists c : nat,
    forall (G : sgraph) (C : finType) (col : {set G} -> C),
      Legacy.x14_proper_edge_colouring col ->
      exists paths : seq (seq G),
        size paths <= c * #|G| /\
        (forall p : seq G, p \in paths -> x14_rainbow_path col p) /\
        x62_edges_covered_by_paths paths.

End X62Legacy.

(** studies:std_andersen_s_conjecture (open, unchanged). *)
Lemma andersen_rainbow_path_statement_compat :
  X14Legacy.andersen_rainbow_path_statement <-> andersen_rainbow_path_statement.
Proof.
by split=> H n C col n2 prop; apply: (H n C col n2); apply/x14_proper_edge_colouring_compat.
Qed.

(** arxiv:2301.08707#01 (open, unchanged). *)
Lemma rainbow_paths_linear_edge_cover_statement_compat :
  X62Legacy.rainbow_paths_linear_edge_cover_statement <->
  rainbow_paths_linear_edge_cover_statement.
Proof.
by split=> -[c H]; exists c => G C col prop; apply: (H G C col);
  apply/x14_proper_edge_colouring_compat.
Qed.

Print Assumptions x14_edge_set_compat.
Print Assumptions x14_proper_edge_colouring_compat.
Print Assumptions andersen_rainbow_path_statement_compat.
Print Assumptions rainbow_paths_linear_edge_cover_statement_compat.
