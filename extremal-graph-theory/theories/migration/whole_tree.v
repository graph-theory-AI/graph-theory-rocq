(** * Extremal.migration.whole_tree — frozen whole-graph tree wrapper and rows of XE1 / XE2
    (library migration B20)

    Family [whole-tree] (meta/library_primitives/whole-tree.json).  [Legacy] freezes, verbatim as it
    stood at the B20 baseline 6de6ce3, XE1's [xe1_tree] ([is_forest [set: T] /\ connected [set: T]]),
    which is definitionally the upstream [GraphTheory.core.sgraph.is_tree [set: T]]; the live wrapper
    now unfolds to that canonical, so the certificate is a conversion.  No second tree predicate and no
    nonempty guard: ['K_0] stays a tree.

    [XE1Legacy] and [XE2Legacy] freeze the six Extremal rows complete over the frozen tree and the LIVE
    aliases of the other families (A5 subgraph_of, A6 complement/Ramsey, A7 edge_count, C7 bipartition,
    A11 isolated vertices): #548 (k.+1 <= n, exact orders, the doubled edge bound with natural
    subtraction, the subgraph conclusion), #550 (positive part sizes and the two smallest, N before
    n/RTB/RTG/T/G, the complete multipartite host and BOTH least-Ramsey witnesses), #557 (1 <= k, an
    additive C, the k-colour least-Ramsey relation), #568 (both existential bounds, the uniform C, no
    isolated vertices, the exact edge count), #547 (2 <= n, the least diagonal Ramsey number, R <= 2n-2)
    and #549 (no k > 0 guard, bipartition sizes k and 2k, R = 4k-1).  #548's prose claims k >= 1 follows
    from its guards; it does not (k = 0 is admitted), recorded without repair.

    [XE1Original] and [XE2Original] compose the five complete pre-A5/A6/A7/C7/A11, pre-B20 rows from the
    earlier families' Original templates (bound as [Module A5]/[A6]/[A7]/[C7]/[A11]) with the new frozen
    tree: #548 over A7's frozen x4_edge_count and A5's frozen subgraph relation, #550 and #547 over A6's
    Original Ramsey numbers, #568 over A6's Original Ramsey number, A7's frozen edge count and A11's
    frozen no-isolated-vertices, #549 over C7's frozen bipartition sizes and A6's Original diagonal
    Ramsey number; each is certified end to end through the earlier family's own Original certificate.
    The earlier snapshots that still call the live tree stay byte-exact (reciprocal known-stale notes).
    Hashes and substitutions: meta/migration_reports/whole_tree.md. *)

From Corelib Require Import Setoid Morphisms.
From GTBase Require Import base.
From Extremal.conjectures Require Import X4 XE1 XE2.
From Extremal.migration Require subgraph_of complement edge_count bipartition min_degree_at_least.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** The earlier certificates, bound explicitly: their frozen bodies are reused by the Originals. *)
Module A5 := Extremal.migration.subgraph_of.
Module A6 := Extremal.migration.complement.
Module A7 := Extremal.migration.edge_count.
Module C7 := Extremal.migration.bipartition.
Module A11 := Extremal.migration.min_degree_at_least.

Module Legacy.

Definition xe1_tree (T : sgraph) : Prop :=
  is_forest [set: T] /\ connected [set: T].

End Legacy.

Module XE1Legacy.

Definition erdos_548_statement : Prop :=
  forall (n k : nat) (G T : sgraph),
    k.+1 <= n ->
    #|G| = n -> #|T| = k.+1 -> Legacy.xe1_tree T ->
    2 * x4_edge_count G >= (k - 1) * n + 2 ->
    xe1_subgraph_of T G.

Definition erdos_550_statement : Prop :=
  forall (k : nat) (sizes : 'I_k -> nat) (m1 m2 : nat),
    2 <= k ->
    (forall i : 'I_k, 0 < sizes i) ->
    xe1_two_smallest_part_sizes sizes m1 m2 ->
    exists N : nat,
    forall (n RTB RTG : nat) (T G : sgraph),
      N <= n -> Legacy.xe1_tree T -> #|T| = n ->
      xe1_complete_multipartite_with_sizes G sizes ->
      xe1_graph_ramsey_number T (KB m1 m2) RTB ->
      xe1_graph_ramsey_number T G RTG ->
      RTG <= (χ([set: G]) - 1) * (RTB - 1) + m1.

Definition erdos_557_statement : Prop :=
  forall k : nat, 1 <= k -> exists C : nat,
    forall (n R : nat) (T : sgraph),
      Legacy.xe1_tree T -> #|T| = n ->
      xe1_multicolour_graph_ramsey_number k T R ->
      R <= k * n + C.

Definition erdos_568_statement : Prop :=
  forall G : sgraph,
    (exists C1 : nat, forall (n R : nat) (T : sgraph),
      Legacy.xe1_tree T -> #|T| = n -> xe1_graph_ramsey_number G T R -> R <= C1 * n) ->
    (exists C2 : nat, forall (n R : nat),
      xe1_graph_ramsey_number G 'K_n R -> R <= C2 * n ^ 2) ->
    exists C : nat, forall (H : sgraph) (m R : nat),
      x4_edge_count H = m -> xe1_no_isolated_vertices H ->
      xe1_graph_ramsey_number G H R ->
      R <= C * m.

End XE1Legacy.

Module XE2Legacy.

Definition erdos_547_statement : Prop :=
  forall (n R : nat) (T : sgraph),
    2 <= n ->
    Legacy.xe1_tree T -> #|T| = n ->
    xe1_diagonal_ramsey_number T R ->
    R <= 2 * n - 2.

Definition erdos_549_statement : Prop :=
  forall (k R : nat) (T : sgraph),
    Legacy.xe1_tree T -> xe2_bipartition_sizes T k (2 * k) ->
    xe1_diagonal_ramsey_number T R ->
    R = 4 * k - 1.

End XE2Legacy.

Module XE1Original.

Definition erdos_548_statement : Prop :=
  forall (n k : nat) (G T : sgraph),
    k.+1 <= n ->
    #|G| = n -> #|T| = k.+1 -> Legacy.xe1_tree T ->
    2 * A7.Legacy.x4_edge_count G >= (k - 1) * n + 2 ->
    A5.Legacy.xe1_subgraph_of T G.

Definition erdos_550_statement : Prop :=
  forall (k : nat) (sizes : 'I_k -> nat) (m1 m2 : nat),
    2 <= k ->
    (forall i : 'I_k, 0 < sizes i) ->
    xe1_two_smallest_part_sizes sizes m1 m2 ->
    exists N : nat,
    forall (n RTB RTG : nat) (T G : sgraph),
      N <= n -> Legacy.xe1_tree T -> #|T| = n ->
      xe1_complete_multipartite_with_sizes G sizes ->
      A6.XE1Original.graph_ramsey_number T (KB m1 m2) RTB ->
      A6.XE1Original.graph_ramsey_number T G RTG ->
      RTG <= (χ([set: G]) - 1) * (RTB - 1) + m1.

Definition erdos_568_statement : Prop :=
  forall G : sgraph,
    (exists C1 : nat, forall (n R : nat) (T : sgraph),
      Legacy.xe1_tree T -> #|T| = n -> A6.XE1Original.graph_ramsey_number G T R -> R <= C1 * n) ->
    (exists C2 : nat, forall (n R : nat),
      A6.XE1Original.graph_ramsey_number G 'K_n R -> R <= C2 * n ^ 2) ->
    exists C : nat, forall (H : sgraph) (m R : nat),
      A7.Legacy.x4_edge_count H = m -> A11.Legacy.xe1_no_isolated_vertices H ->
      A6.XE1Original.graph_ramsey_number G H R ->
      R <= C * m.

End XE1Original.

Module XE2Original.

Definition erdos_547_statement : Prop :=
  forall (n R : nat) (T : sgraph),
    2 <= n ->
    Legacy.xe1_tree T -> #|T| = n ->
    A6.XE1Original.diagonal_ramsey_number T R ->
    R <= 2 * n - 2.

Definition erdos_549_statement : Prop :=
  forall (k R : nat) (T : sgraph),
    Legacy.xe1_tree T -> C7.XE2Legacy.xe2_bipartition_sizes T k (2 * k) ->
    A6.XE1Original.diagonal_ramsey_number T R ->
    R = 4 * k - 1.

End XE2Original.

(** ** Certificates *)

(** The helper: the upstream [is_tree] at the whole carrier, by conversion. *)
Lemma xe1_tree_compat (T : sgraph) : Legacy.xe1_tree T <-> xe1_tree T.
Proof. exact: iff_refl. Qed.

(** The six Extremal rows (erdos:548, 550, 557, 568, 547, 549; unchanged): per-row copies over the
    frozen tree and the live aliases of the other families, by conversion. *)
Lemma erdos_548_statement_compat : XE1Legacy.erdos_548_statement <-> erdos_548_statement.
Proof. exact: iff_refl. Qed.

Lemma erdos_550_statement_compat : XE1Legacy.erdos_550_statement <-> erdos_550_statement.
Proof. exact: iff_refl. Qed.

Lemma erdos_557_statement_compat : XE1Legacy.erdos_557_statement <-> erdos_557_statement.
Proof. exact: iff_refl. Qed.

Lemma erdos_568_statement_compat : XE1Legacy.erdos_568_statement <-> erdos_568_statement.
Proof. exact: iff_refl. Qed.

Lemma erdos_547_statement_compat : XE2Legacy.erdos_547_statement <-> erdos_547_statement.
Proof. exact: iff_refl. Qed.

Lemma erdos_549_statement_compat : XE2Legacy.erdos_549_statement <-> erdos_549_statement.
Proof. exact: iff_refl. Qed.

(** The five complete Originals, end to end: each is the earlier family's composed Original with the
    frozen tree substituted (a conversion), so the earlier family's own Original certificate closes it. *)
Lemma erdos_548_statement_original_compat : XE1Original.erdos_548_statement <-> erdos_548_statement.
Proof. exact: A7.erdos_548_statement_original_compat. Qed.

Lemma erdos_550_statement_original_compat : XE1Original.erdos_550_statement <-> erdos_550_statement.
Proof. exact: A6.erdos_550_statement_original_compat. Qed.

Lemma erdos_568_statement_original_compat : XE1Original.erdos_568_statement <-> erdos_568_statement.
Proof. exact: A11.erdos_568_statement_original_compat. Qed.

Lemma erdos_547_statement_original_compat : XE2Original.erdos_547_statement <-> erdos_547_statement.
Proof. exact: A6.erdos_547_statement_original_compat. Qed.

Lemma erdos_549_statement_original_compat : XE2Original.erdos_549_statement <-> erdos_549_statement.
Proof. exact: C7.erdos_549_statement_complement_original_compat. Qed.

Print Assumptions xe1_tree_compat.
Print Assumptions erdos_548_statement_compat.
Print Assumptions erdos_550_statement_compat.
Print Assumptions erdos_557_statement_compat.
Print Assumptions erdos_568_statement_compat.
Print Assumptions erdos_547_statement_compat.
Print Assumptions erdos_549_statement_compat.
Print Assumptions erdos_548_statement_original_compat.
Print Assumptions erdos_550_statement_original_compat.
Print Assumptions erdos_568_statement_original_compat.
Print Assumptions erdos_547_statement_original_compat.
Print Assumptions erdos_549_statement_original_compat.
