(** * Chromatic.migration.edge_colourings -- frozen proper edge colourings (C6, 2026-10-03)

    Family: "proper_edge_colouring" (meta/library_primitives/proper-edge-colouring.json);
    chromatic rows of X142 and X213.  Canonical primitives:
    [GTBase.edge_colourings.proper_edge_colouring] (set maps) and
    [GTBase.edge_colourings.proper_pair_edge_colouring] (pair maps symmetric
    on all ordered pairs), both over an [eqType] palette; public client
    base/theories/examples/edge_colourings.v; generated report
    meta/migration_reports/proper_edge_colouring.md (from
    proper_edge_colouring.spec.json); record meta/LIBRARY_MIGRATION_C6.md.

    ** X142: M1's complete frozen chain is reused

    M1 (Chromatic.migration.simple_edges) froze the whole X142 chain over the
    pre-M1 edge comprehension [Legacy.exists_edge_set]: [X142Legacy.proper_edge_colouring]
    (the intersection form over [{set G}] maps into ['I_k]), [edges_incident],
    [incident_sum], [neighbour_sum_distinguishing], [neighbour_sum_edge_colourable]
    and the row [X142Legacy.statement].  Those bodies and theorem types are
    byte-identical; only M1's helper certificate proof now goes through
    [proper_edge_colouring_edgesP].  This module is the per-family entry point
    for X142: it restates this family's helper, chain and row certificates
    over M1's frozen bodies and proves them from the adapted M1 theorems.

    ** X213: fresh frozen chain

    [Legacy] freezes [x213_proper_edge_colouring] verbatim as it stood at
    3011c28: a map on ORDERED PAIRS, symmetric on every pair (adjacent or not)
    and giving different colours to two distinct neighbours of a vertex;
    the live name is now the alias of [proper_pair_edge_colouring], so the
    certificate is a kernel-checked conversion.  [X213Legacy] freezes the
    chain [edge_colourable] (prefix dropped) and the two rows with every
    reference to a frozen name replaced by its frozen copy; [x213_kempe_reach]
    and [x213_used_colours] reach no helper of this family and are used live,
    so the whole-function Kempe states and the used-colour count are
    preserved exactly.  The prose of X213.v ("only the values on adjacent
    pairs are constrained") and its body (symmetry on all pairs) disagree;
    C6 records that discrepancy and changes neither.

    Axiom-free: no Axiom/Parameter/Admitted; Print Assumptions at the end. *)

From GTBase Require Import base edge_colourings.
From Chromatic.conjectures Require Import X142 X213.
From Chromatic.migration Require simple_edges.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** X142, over M1's frozen bodies *)

(** Helper certificate: the frozen intersection form over the pre-M1 edge
    comprehension is the canonical endpoint form. *)
Lemma x142_proper_edge_colouring_compat
    (G : sgraph) (k : nat) (col : {set G} -> 'I_k) :
  Chromatic.migration.simple_edges.X142Legacy.proper_edge_colouring col <->
  x142_proper_edge_colouring col.
Proof. exact: Chromatic.migration.simple_edges.x142_proper_edge_colouring_compat. Qed.

(** Chain certificate. *)
Lemma x142_neighbour_sum_edge_colourable_compat (G : sgraph) (k : nat) :
  Chromatic.migration.simple_edges.X142Legacy.neighbour_sum_edge_colourable G k <->
  x142_neighbour_sum_edge_colourable G k.
Proof. exact: Chromatic.migration.simple_edges.x142_neighbour_sum_edge_colourable_compat. Qed.

(** studies:std_flandrin_et_al_conjecture_neighbour_sum_distingu (open, unchanged). *)
Lemma flandrin_neighbour_sum_distinguishing_edge_colouring_statement_compat :
  Chromatic.migration.simple_edges.X142Legacy.statement <->
  flandrin_neighbour_sum_distinguishing_edge_colouring_statement.
Proof. exact: Chromatic.migration.simple_edges.x142_statement_compat. Qed.

(** ** X213 *)

Module Legacy.

(** X213.v lines 24-27 at 3011c28, verbatim. *)
Definition x213_proper_edge_colouring
    (G : sgraph) (k : nat) (col : G -> G -> 'I_k) : Prop :=
  (forall u v : G, col u v = col v u) /\
  (forall u v w : G, u -- v -> u -- w -> v != w -> col u v != col u w).

End Legacy.

(** The migrated helper: the frozen pair-map body is the canonical pair-map
    predicate (a conversion). *)
Lemma x213_proper_edge_colouring_compat
    (G : sgraph) (k : nat) (col : G -> G -> 'I_k) :
  Legacy.x213_proper_edge_colouring col <-> x213_proper_edge_colouring col.
Proof. exact: iff_refl. Qed.

Module X213Legacy.

(** X213.v lines 30-31 at 3011c28 with [x213_edge_colourable] ->
    [edge_colourable] and [x213_proper_edge_colouring] ->
    [Legacy.x213_proper_edge_colouring]. *)
Definition edge_colourable (G : sgraph) (k : nat) : Prop :=
  exists col : G -> G -> 'I_k, Legacy.x213_proper_edge_colouring col.

(** X213.v lines 155-161 and 183-192 at 3011c28 with [x213_edge_colourable]
    -> [edge_colourable] and [x213_proper_edge_colouring] ->
    [Legacy.x213_proper_edge_colouring]. *)
Definition one_factorization_conjecture_statement : Prop :=
  forall (G : sgraph) (d : nat),
    0 < #|G| ->
    ~~ odd #|G| ->
    regular G d ->
    #|G| <= 2 * d ->
    edge_colourable G d.

Definition vizing_kempe_interchange_statement : Prop :=
  forall (G : sgraph) (k m : nat) (col : G -> G -> 'I_k),
    Legacy.x213_proper_edge_colouring col ->
    m <= k ->
    edge_colourable G m ->
    exists (n : nat) (col' : G -> G -> 'I_k),
      [/\ x213_kempe_reach n col col',
          Legacy.x213_proper_edge_colouring col' &
          #|x213_used_colours col'| <= m].

End X213Legacy.

Lemma x213_edge_colourable_compat (G : sgraph) (k : nat) :
  X213Legacy.edge_colourable G k <-> x213_edge_colourable G k.
Proof. exact: iff_refl. Qed.

(** bm:bm-057 (partial, unchanged). *)
Lemma one_factorization_conjecture_statement_compat :
  X213Legacy.one_factorization_conjecture_statement <->
  one_factorization_conjecture_statement.
Proof. exact: iff_refl. Qed.

(** bm:bm-060 (solved, unchanged). *)
Lemma vizing_kempe_interchange_statement_compat :
  X213Legacy.vizing_kempe_interchange_statement <->
  vizing_kempe_interchange_statement.
Proof. exact: iff_refl. Qed.

Print Assumptions x142_proper_edge_colouring_compat.
Print Assumptions x142_neighbour_sum_edge_colourable_compat.
Print Assumptions flandrin_neighbour_sum_distinguishing_edge_colouring_statement_compat.
Print Assumptions x213_proper_edge_colouring_compat.
Print Assumptions x213_edge_colourable_compat.
Print Assumptions one_factorization_conjecture_statement_compat.
Print Assumptions vizing_kempe_interchange_statement_compat.
