(** * Hamilton.migration.cycle_edges — frozen successor-image edge sets of U2 and X211 (library
    migration B11)

    Batch B, family [cycle-edges] (meta/library_primitives/cycle-edges.json).  [Legacy] freezes,
    verbatim as they stood at the B11 baseline 0a0203e, U2's [cycle_edges] and X211's
    [x211_cycle_edges] ([[set [set x; next c x] | x in [set z | z \in c]]], MathComp's [next]
    reading the first occurrence), with their explicit [Arguments].  Both now unfold to
    [GTBase.walks_paths.seq_next_edge_set c], the same term, so the certificates are
    kernel-checked conversions.  [U2Legacy] freezes the uniquely-Hamiltonian and Hamilton
    decomposition chains and the three U2 rows; [X211Legacy] the Hamilton-cycle edge-set
    collection and Cantoni's row; all with this family's helpers only.  The digon convention of
    the Hamilton cycle predicates (a two-entry Hamilton cycle of ['K_2]) and their empty-carrier
    behaviour are untouched: no length guard is added.

    Name resolution: U2 defines its own [hamiltonian_cycle] and [edge_set], while X211 reads
    GTBase.common's [hamiltonian_cycle].  U2 is imported before its rows are frozen, and X211
    (which re-exports GTBase.base) only after them, so each frozen row resolves these names
    exactly as its source does; the kernel evidence of the family checks it. *)

From GTBase Require Import base.
From Hamilton.conjectures Require U2 X211.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Legacy.

Definition cycle_edges (G : sgraph) (c : seq G) : {set {set G}} :=
  [set [set x; next c x] | x in [set z | z \in c]].
Arguments cycle_edges : clear implicits.

Definition x211_cycle_edges (G : sgraph) (c : seq G) : {set {set G}} :=
  [set [set x; next c x] | x in [set z | z \in c]].
Arguments x211_cycle_edges : clear implicits.

End Legacy.

(** ** U2, with U2's own [hamiltonian_cycle] and [edge_set] *)

Import U2.

Module U2Legacy.

Definition four_connected_graphs_are_not_uniquely_hamiltonian_statement : Prop :=
  forall G : sgraph, k_connected G 4 ->
    forall c : seq G, hamiltonian_cycle G c ->
      exists c' : seq G,
        hamiltonian_cycle G c' /\ Legacy.cycle_edges G c' != Legacy.cycle_edges G c.

Definition uniquely_hamiltonian (G : sgraph) : Prop :=
  exists c : seq G,
    hamiltonian_cycle G c /\
    forall c' : seq G, hamiltonian_cycle G c' -> Legacy.cycle_edges G c' = Legacy.cycle_edges G c.

Definition uniquely_hamiltonian_graphs_statement : Prop :=
  forall (r : nat) (G : sgraph),
    2 < r -> regular G r -> ~ U2Legacy.uniquely_hamiltonian G.

Definition hamilton_decomposition_into_two (G : sgraph) : Prop :=
  exists c1 c2 : seq G,
    [/\ hamiltonian_cycle G c1, hamiltonian_cycle G c2,
        [disjoint Legacy.cycle_edges G c1 & Legacy.cycle_edges G c2]
      & Legacy.cycle_edges G c1 :|: Legacy.cycle_edges G c2 = edge_set G].

Definition decomposing_the_prism_of_a_3_connected_cubic_planar_statement : Prop :=
  forall (G : sgraph),
    wagner_planar G -> k_connected G 3 -> regular G 3 ->
    U2Legacy.hamilton_decomposition_into_two (cartesian_product G 'K_2).

End U2Legacy.

(** ** X211, with GTBase.common's [hamiltonian_cycle] *)

Import X211.

Module X211Legacy.

Definition hamilton_cycle_edge_sets (G : sgraph) : {set {set {set G}}} :=
  [set A : {set {set G}} |
    [exists c : (#|G|).-tuple G,
       hamiltonian_cycle G c && (A == Legacy.x211_cycle_edges G c)]].

Definition cantoni_planar_cubic_three_hamilton_cycles_statement : Prop :=
  forall G : sgraph,
    wagner_planar G ->
    regular G 3 ->
    #|hamilton_cycle_edge_sets G| = 3 ->
    x211_has_triangle G.

End X211Legacy.

(** ** Certificates *)

Lemma cycle_edges_compat (G : sgraph) (c : seq G) : Legacy.cycle_edges G c = cycle_edges G c.
Proof. by []. Qed.

Lemma x211_cycle_edges_compat (G : sgraph) (c : seq G) :
  Legacy.x211_cycle_edges G c = x211_cycle_edges G c.
Proof. by []. Qed.

Lemma four_connected_graphs_are_not_uniquely_hamiltonian_statement_compat :
  U2Legacy.four_connected_graphs_are_not_uniquely_hamiltonian_statement <->
  four_connected_graphs_are_not_uniquely_hamiltonian_statement.
Proof. exact: iff_refl. Qed.

Lemma uniquely_hamiltonian_compat (G : sgraph) :
  U2Legacy.uniquely_hamiltonian G <-> uniquely_hamiltonian G.
Proof. exact: iff_refl. Qed.

Lemma uniquely_hamiltonian_graphs_statement_compat :
  U2Legacy.uniquely_hamiltonian_graphs_statement <-> uniquely_hamiltonian_graphs_statement.
Proof. exact: iff_refl. Qed.

Lemma hamilton_decomposition_into_two_compat (G : sgraph) :
  U2Legacy.hamilton_decomposition_into_two G <-> hamilton_decomposition_into_two G.
Proof. exact: iff_refl. Qed.

Lemma decomposing_the_prism_of_a_3_connected_cubic_planar_statement_compat :
  U2Legacy.decomposing_the_prism_of_a_3_connected_cubic_planar_statement <->
  decomposing_the_prism_of_a_3_connected_cubic_planar_statement.
Proof. exact: iff_refl. Qed.

Lemma x211_hamilton_cycle_edge_sets_compat (G : sgraph) :
  X211Legacy.hamilton_cycle_edge_sets G = x211_hamilton_cycle_edge_sets G.
Proof. by []. Qed.

Lemma cantoni_planar_cubic_three_hamilton_cycles_statement_compat :
  X211Legacy.cantoni_planar_cubic_three_hamilton_cycles_statement <->
  cantoni_planar_cubic_three_hamilton_cycles_statement.
Proof. exact: iff_refl. Qed.

Print Assumptions cycle_edges_compat.
Print Assumptions x211_cycle_edges_compat.
Print Assumptions four_connected_graphs_are_not_uniquely_hamiltonian_statement_compat.
Print Assumptions uniquely_hamiltonian_graphs_statement_compat.
Print Assumptions decomposing_the_prism_of_a_3_connected_cubic_planar_statement_compat.
Print Assumptions cantoni_planar_cubic_three_hamilton_cycles_statement_compat.
