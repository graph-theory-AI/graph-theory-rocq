(** * Packing.migration.path_edges — frozen first-index edge set of X178 (library migration B8)

    Batch B, family [path-edges] (meta/library_primitives/path-edges.json),
    first-index class.  [Legacy] freezes X178's [x178_path_edge_set] verbatim as it
    stood at the B8 baseline 048c768: the ACTUAL edges [x -- y] of the graph with both
    ends in [p] whose FIRST occurrences in [p] are adjacent positions ([U9.consec]).
    The live helper now unfolds to [GTBase.walks_paths.seq_index_edge_set p], whose
    body is that comprehension with [U9.consec]'s body as
    [seq_index_consecutive], so the certificates are kernel-checked conversions.  It
    is NOT the raw support of the consecutive pairs: the two agree on duplicate-free
    walks ([seq_index_edge_set_walk]); [U9.consec] itself is unchanged.
    [X178Legacy] freezes the decomposition predicate and the row with B6's live
    [x178_path_seq]; [X178Original] composes B6's frozen [x178_path_seq]
    (Packing.migration.simple_path.Legacy) with this family's frozen edge set, the
    complete pre-B6, pre-B8 row.  The indexed family, a possibly empty family, edge
    disjointness, the exact cover of [edge_setG] and the odd-semiclique guard are
    unchanged.  Hashes and substitutions: meta/migration_reports/path_edges.md. *)

From GTBase Require Import base.
From Packing.conjectures Require Import U9 X178.
From Packing.migration Require simple_path.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Legacy.

Definition x178_path_edge_set (G : sgraph) (p : seq G) : {set {set G}} :=
  [set e : {set G} |
    [exists x : G, [exists y : G,
      [&& x -- y, e == [set x; y], x \in p, y \in p & @consec G p x y]]]].

End Legacy.

Module X178Legacy.

Definition path_decomposition_at_most (G : sgraph) (m : nat) : Prop :=
  exists (r : nat) (P : 'I_r -> seq G),
    [/\ r <= m,
        (forall i : 'I_r, x178_path_seq (P i)),
        (forall i j : 'I_r,
            i != j ->
            [disjoint Legacy.x178_path_edge_set (P i) & Legacy.x178_path_edge_set (P j)])
      & \bigcup_(i : 'I_r) Legacy.x178_path_edge_set (P i) = edge_setG G].

Definition gallai_odd_semiclique_path_decomposition_statement : Prop :=
  forall G : sgraph,
    connected [set: G] ->
    ~ x178_odd_semi_clique G ->
    path_decomposition_at_most G (#|G| %/ 2).

End X178Legacy.

Module X178Original.

Definition path_decomposition_at_most (G : sgraph) (m : nat) : Prop :=
  exists (r : nat) (P : 'I_r -> seq G),
    [/\ r <= m,
        (forall i : 'I_r, Packing.migration.simple_path.Legacy.x178_path_seq (P i)),
        (forall i j : 'I_r,
            i != j ->
            [disjoint Legacy.x178_path_edge_set (P i) & Legacy.x178_path_edge_set (P j)])
      & \bigcup_(i : 'I_r) Legacy.x178_path_edge_set (P i) = edge_setG G].

Definition gallai_odd_semiclique_path_decomposition_statement : Prop :=
  forall G : sgraph,
    connected [set: G] ->
    ~ x178_odd_semi_clique G ->
    path_decomposition_at_most G (#|G| %/ 2).

End X178Original.

(** ** Certificates *)

Lemma x178_path_edge_set_compat (G : sgraph) (p : seq G) :
  Legacy.x178_path_edge_set p = x178_path_edge_set p.
Proof. by []. Qed.

Lemma x178_path_decomposition_at_most_compat (G : sgraph) (m : nat) :
  X178Legacy.path_decomposition_at_most G m <-> x178_path_decomposition_at_most G m.
Proof. exact: iff_refl. Qed.

Lemma gallai_odd_semiclique_path_decomposition_statement_compat :
  X178Legacy.gallai_odd_semiclique_path_decomposition_statement <->
  gallai_odd_semiclique_path_decomposition_statement.
Proof. exact: iff_refl. Qed.

(** Before B6 and B8: B6's frozen path predicate and this family's frozen edge set. *)
Lemma x178_path_decomposition_at_most_original_compat (G : sgraph) (m : nat) :
  X178Original.path_decomposition_at_most G m <-> x178_path_decomposition_at_most G m.
Proof.
split=> -[r [P [rm paths disj cover]]]; exists r, P; split=> //.
- by move=> i; apply/Packing.migration.simple_path.x178_path_seq_compat; exact: paths.
- by move=> i; apply/Packing.migration.simple_path.x178_path_seq_compat; exact: paths.
Qed.

Lemma gallai_odd_semiclique_path_decomposition_statement_original_compat :
  X178Original.gallai_odd_semiclique_path_decomposition_statement <->
  gallai_odd_semiclique_path_decomposition_statement.
Proof.
split=> st G conn nsc.
- by apply/x178_path_decomposition_at_most_original_compat; apply: st.
- by apply/x178_path_decomposition_at_most_original_compat; apply: st.
Qed.

Print Assumptions x178_path_edge_set_compat.
Print Assumptions x178_path_decomposition_at_most_compat.
Print Assumptions gallai_odd_semiclique_path_decomposition_statement_compat.
Print Assumptions x178_path_decomposition_at_most_original_compat.
Print Assumptions gallai_odd_semiclique_path_decomposition_statement_original_compat.
