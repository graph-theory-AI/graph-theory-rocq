(** * C4: indexed edge families over the unchanged M1/C1/C2/C3 history

    C1 already froze the pre-M1 edge comprehension, original matching, edge
    family and all four full underrepresentation statements. These entry
    points reuse those bodies verbatim. Only the C1 edge-family helper proof
    needs the new public alias unfolded; all statement theorem types stay
    unchanged. Corpus status, quantifiers, guards, arithmetic and the three
    separate LLM constant bounds are preserved.

    Inputs: meta/migration_reports/edge_family.spec.json and
    meta/library_primitives/edge-family.json. Public API/client:
    theories/foundations/edge_families.v and theories/examples/edge_families.v. *)

From GTBase Require Import base.
From Packing.conjectures Require Import X15.
From Packing.migration Require matching.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma x15_edge_family_compat
    (G : sgraph) (m : nat) (E : 'I_m -> {set {set G}}) :
  Packing.migration.matching.X15Legacy.edge_family E <-> x15_edge_family E.
Proof. exact: Packing.migration.matching.x15_edge_family_compat. Qed.

Lemma bipartite_matching_underrepresentation_statement_compat :
  Packing.migration.matching.X15Legacy.bipartite_matching_underrepresentation_statement <->
  bipartite_matching_underrepresentation_statement.
Proof. exact: Packing.migration.matching.bipartite_matching_underrepresentation_statement_compat. Qed.

Lemma bipartite_matching_underrepresentation_llm_statement_compat :
  Packing.migration.matching.X15Legacy.bipartite_matching_underrepresentation_llm_statement <->
  bipartite_matching_underrepresentation_llm_statement.
Proof. exact: Packing.migration.matching.bipartite_matching_underrepresentation_llm_statement_compat. Qed.

Lemma bipartite_matching_underrepresentation_llm2_statement_compat :
  Packing.migration.matching.X15Legacy.bipartite_matching_underrepresentation_llm2_statement <->
  bipartite_matching_underrepresentation_llm2_statement.
Proof. exact: Packing.migration.matching.bipartite_matching_underrepresentation_llm2_statement_compat. Qed.

Lemma bipartite_matching_underrepresentation_llm3_statement_compat :
  Packing.migration.matching.X15Legacy.bipartite_matching_underrepresentation_llm3_statement <->
  bipartite_matching_underrepresentation_llm3_statement.
Proof. exact: Packing.migration.matching.bipartite_matching_underrepresentation_llm3_statement_compat. Qed.

Print Assumptions x15_edge_family_compat.
Print Assumptions bipartite_matching_underrepresentation_statement_compat.
Print Assumptions bipartite_matching_underrepresentation_llm_statement_compat.
Print Assumptions bipartite_matching_underrepresentation_llm2_statement_compat.
Print Assumptions bipartite_matching_underrepresentation_llm3_statement_compat.
