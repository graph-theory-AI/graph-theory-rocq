(** * Cycle.migration.eulerian — frozen Eulerian multigraph helper and rows of U6 (library migration B17)

    Second contract of family [degree-balance] (meta/library_primitives/degree-balance.json, semantic class
    multigraph-eulerian; root decision 2026-10-03, option A: the inventory binds every helper of the
    corpus name "eulerian" to one family).  No equivalence with the directed degree balance of
    [Digraph.foundations.degree_balance] nor with U6's supplied directed [is_eulerian_tour] is stated or
    implied; the two contracts share only the name.  [Legacy] freezes, verbatim as it
    stood at the B17 baseline cc78377, U6's [eulerian] ([mconnected G /\ forall v : G, ~~ odd (mdeg v)]:
    connected over all vertices through base's undirected [uwalk], every arc-end degree even, so a loop
    counts two; the empty multigraph and an isolated vertex qualify).  The live helper now unfolds to the
    public [Cycle.foundations.eulerian.eulerian], the same body, so the certificate is a conversion.
    [U6Legacy] freezes the three complete OPG rows over the frozen helper, with every guard in its order:
    positive vertex and edge counts, [simple_mgraph] and the floor bound (row 4); positive vertex count,
    minimum arc-end degree 4 and the supplied DIRECTED [is_eulerian_tour] (row 5, the documented
    orientation limitation preserved); positive counts, [edge_connected G 6] and the supplied
    [transition2_system] (row 6).  [even_subgraph] and [is_eulerian_tour] are distinct, untouched
    contracts; no tour equivalence is used.  Hashes and substitutions: meta/migration_reports/degree_balance.md. *)

From GraphTheory Require Import mgraph.
From GTBase Require Import base.
From Cycle.foundations Require Import connectivity eulerian.
From Cycle.conjectures Require Import U6.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module Legacy.

Definition eulerian (G : mgraph) : Prop :=
  mconnected G /\ forall v : G, ~~ odd (mdeg v).

End Legacy.

Module U6Legacy.

Definition decomposing_an_eulerian_graph_into_cycles_statement : Prop :=
  forall G : mgraph,
    (0 < #|G|)%N -> (0 < #|edge G|)%N -> simple_mgraph G -> Legacy.eulerian G ->
    exists D : seq {set edge G},
      cycle_decomposition D /\ (size D <= (#|G| - 1) %/ 2)%N.

Definition decomposing_an_eulerian_graph_into_cycles_with_no_tw_statement : Prop :=
  forall (G : mgraph) (w : seq (edge G)),
    (0 < #|G|)%N -> Legacy.eulerian G -> (forall v : G, (4 <= mdeg v)%N) ->
    is_eulerian_tour w ->
    exists D : seq {set edge G},
      cycle_decomposition D /\ (forall C, C \in D -> ~~ two_consecutive w C).

Definition decomposing_eulerian_graphs_statement : Prop :=
  forall (G : mgraph) (P : G -> {set {set edge G}}),
    (0 < #|G|)%N -> (0 < #|edge G|)%N -> edge_connected G 6 -> Legacy.eulerian G ->
    transition2_system P ->
    exists D : seq {set edge G}, compatible_decomposition P D.

End U6Legacy.

(** ** Certificates *)

(** The helper: the body of the public [eulerian], by conversion. *)
Lemma eulerian_compat (G : mgraph) : Legacy.eulerian G <-> Cycle.conjectures.U6.eulerian G.
Proof. exact: iff_refl. Qed.

(** opg:decomposing_an_eulerian_graph_into_cycles (unchanged). *)
Lemma decomposing_an_eulerian_graph_into_cycles_statement_compat :
  U6Legacy.decomposing_an_eulerian_graph_into_cycles_statement <->
  Cycle.conjectures.U6.decomposing_an_eulerian_graph_into_cycles_statement.
Proof. exact: iff_refl. Qed.

(** opg:decomposing_an_eulerian_graph_into_cycles_with_no_two_consecutives_edges_on_a_prescirbed_eulerian_tour
    (unchanged). *)
Lemma decomposing_an_eulerian_graph_into_cycles_with_no_tw_statement_compat :
  U6Legacy.decomposing_an_eulerian_graph_into_cycles_with_no_tw_statement <->
  Cycle.conjectures.U6.decomposing_an_eulerian_graph_into_cycles_with_no_tw_statement.
Proof. exact: iff_refl. Qed.

(** opg:decomposing_eulerian_graphs (unchanged). *)
Lemma decomposing_eulerian_graphs_statement_compat :
  U6Legacy.decomposing_eulerian_graphs_statement <->
  Cycle.conjectures.U6.decomposing_eulerian_graphs_statement.
Proof. exact: iff_refl. Qed.

Print Assumptions eulerian_compat.
Print Assumptions decomposing_an_eulerian_graph_into_cycles_statement_compat.
Print Assumptions decomposing_an_eulerian_graph_into_cycles_with_no_tw_statement_compat.
Print Assumptions decomposing_eulerian_graphs_statement_compat.
