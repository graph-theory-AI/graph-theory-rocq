(** * Packing.migration.perfect_matching -- C2 certificates for the packing rows (X18, X25)

    Family: "perfect-matching" (meta/library_primitives/perfect-matching.json);
    packing rows of X18 and X25.  Canonical primitive:
    [GTBase.common.perfect_matching] (a [connectivity.matching] covering every
    vertex), API and grounding in base/theories/common.v; public downstream
    client base/theories/examples/perfect_matching.v; generated report
    meta/migration_reports/perfect_matching.md (from perfect_matching.spec.json);
    record meta/LIBRARY_MIGRATION_C2.md.

    ** Frozen source

    The two packing helpers of this family were frozen by earlier families,
    together with the whole affected chains of their rows, and those
    snapshots are preserved verbatim rather than duplicated:
    - [x18_perfect_matching] as [Packing.migration.matching.X18Legacy.perfect_matching]
      (C1; over the frozen [Legacy.x15_matching] and the pre-M1 edge set), with the
      X18 row [X18Legacy.knn_fair_perfect_matching_statement];
    - [x25_perfect_matching] as [Packing.migration.simple_edges.X25Legacy.perfect_matching]
      (M1; over the pre-M1 [Legacy.edge_set]), with the chain
      [X25Legacy.perfect_one_factorization] and the X25 row [X25Legacy.statement].
    Since C2 the live helpers are transparent aliases of [perfect_matching]; the
    helper certificates of those modules were re-proved through
    [perfect_matching_exactly_oneP], their statements unchanged.

    ** Certificates

    This module is the per-family entry point: it states this family's helper
    certificates and the two row certificates over the existing frozen bodies
    and proves them from the adapted certificates of the old modules.  The
    X24 row has its own module, Cycle.migration.perfect_matching.

    Axiom-free: no Axiom/Parameter/Admitted; Print Assumptions at the end. *)

From GTBase Require Import base common.
From Packing.conjectures Require Import X18 X25.
From Packing.migration Require matching simple_edges.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Helper certificates (frozen body <-> live alias = canonical [perfect_matching]) *)

Lemma x18_perfect_matching_compat (G : sgraph) (M : {set {set G}}) :
  Packing.migration.matching.X18Legacy.perfect_matching M <-> x18_perfect_matching M.
Proof. exact: Packing.migration.matching.x18_perfect_matching_compat. Qed.

Lemma x25_perfect_matching_compat (G : sgraph) (M : {set {set G}}) :
  Packing.migration.simple_edges.X25Legacy.perfect_matching M <-> x25_perfect_matching M.
Proof. exact: Packing.migration.simple_edges.x25_perfect_matching_compat. Qed.

(** ** Row certificates *)

(** arxiv:1611.03196#01 (partial row, unchanged). *)
Lemma knn_fair_perfect_matching_statement_compat :
  Packing.migration.matching.X18Legacy.knn_fair_perfect_matching_statement <->
  knn_fair_perfect_matching_statement.
Proof. exact: Packing.migration.matching.knn_fair_perfect_matching_statement_compat. Qed.

(** studies:std_kotzig_s_perfect_1_factorization_conjecture (unchanged). *)
Lemma kotzig_perfect_one_factorization_statement_compat :
  Packing.migration.simple_edges.X25Legacy.statement <->
  kotzig_perfect_one_factorization_statement.
Proof. exact: Packing.migration.simple_edges.x25_statement_compat. Qed.

Print Assumptions x18_perfect_matching_compat.
Print Assumptions x25_perfect_matching_compat.
Print Assumptions knn_fair_perfect_matching_statement_compat.
Print Assumptions kotzig_perfect_one_factorization_statement_compat.
