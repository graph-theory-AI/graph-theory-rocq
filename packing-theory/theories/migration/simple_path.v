(** * Packing.migration.simple_path — frozen simple-path chains (library migration B6)

    Batch B, family [simple-path] (meta/library_primitives/simple-path.json).
    [Legacy] freezes the helper [x178_path_seq] verbatim as it stood at 95cba2c:
    [(p != [::]) /\ uniq p /\ sorted (--) p].  The live helper now unfolds to
    [GTBase.walks_paths.seq_simple_path p]; the two are not convertible, and
    [x178_path_seq_compat] proves them equivalent by [seq_simple_pathE].
    [X178Legacy] freezes the indexed path decomposition (at most [m] paths,
    pairwise edge-disjoint, covering every edge; the family may be empty) and the
    statement; the certificates transport the path condition componentwise.  The
    edge representation [x178_path_edge_set] and U9's [consec] are unchanged.
    Source hashes, the exact substitutions and the per-row theorem names are
    recorded in meta/migration_reports/simple_path.md. *)

From GTBase Require Import base.
From Packing.conjectures Require Import U9 X178.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Legacy.

Definition x178_path_seq (G : sgraph) (p : seq G) : Prop :=
  (p != [::]) /\ uniq p /\ sorted (--) p.

End Legacy.

Module X178Legacy.

Definition path_decomposition_at_most (G : sgraph) (m : nat) : Prop :=
  exists (r : nat) (P : 'I_r -> seq G),
    [/\ r <= m,
        (forall i : 'I_r, Legacy.x178_path_seq (P i)),
        (forall i j : 'I_r,
            i != j ->
            [disjoint x178_path_edge_set (P i) & x178_path_edge_set (P j)])
      & \bigcup_(i : 'I_r) x178_path_edge_set (P i) = edge_setG G].

Definition gallai_odd_semiclique_path_decomposition_statement : Prop :=
  forall G : sgraph,
    connected [set: G] ->
    ~ x178_odd_semi_clique G ->
    path_decomposition_at_most G (#|G| %/ 2).

End X178Legacy.

(** ** Certificates *)

(** Not a conversion: nonempty, [uniq] and [sorted] against the match form. *)
Lemma x178_path_seq_compat (G : sgraph) (p : seq G) :
  Legacy.x178_path_seq p <-> x178_path_seq p.
Proof. exact: iff_sym (seq_simple_pathE p). Qed.

Lemma x178_path_decomposition_at_most_compat (G : sgraph) (m : nat) :
  X178Legacy.path_decomposition_at_most G m <-> x178_path_decomposition_at_most G m.
Proof.
split=> -[r [P [rm paths disj cover]]]; exists r, P; split=> //.
- by move=> i; apply/x178_path_seq_compat; exact: paths.
- by move=> i; apply/x178_path_seq_compat; exact: paths.
Qed.

Lemma gallai_odd_semiclique_path_decomposition_statement_compat :
  X178Legacy.gallai_odd_semiclique_path_decomposition_statement <->
  gallai_odd_semiclique_path_decomposition_statement.
Proof.
split=> st G conn nsc.
- by apply/x178_path_decomposition_at_most_compat; apply: st.
- by apply/x178_path_decomposition_at_most_compat; apply: st.
Qed.
