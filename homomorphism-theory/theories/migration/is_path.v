(** * Hom.migration.is_path — frozen sequence-path chain (library migration B7)

    Batch B, family [is-path] (meta/library_primitives/is-path.json), sequence
    class.  [Legacy] freezes U3's boolean helper [is_path] verbatim as it stood at
    632e0b1, before the migration: [uniq s] and consecutive adjacency, the EMPTY
    sequence accepted.  The live helper now unfolds to
    [GTBase.walks_paths.seq_simple_walk s] ([uniq s && sorted (--) s]), whose body
    is that same boolean, so the certificates below are kernel-checked conversions.
    [U3Legacy] freezes [longest_path] (renamed [u3_longest_path], since U3's names
    carry no wave prefix) and the three-longest-paths row, with its nonempty and
    connected guards.  Source hashes, the exact substitutions and the per-row
    theorem names are recorded in meta/migration_reports/is_path.md. *)

From GTBase Require Import base.
From Hom.conjectures Require Import U3.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Legacy.

Definition is_path (G : sgraph) (s : seq G) : bool :=
  uniq s && (if s is x :: p then path (--) x p else true).

End Legacy.

Module U3Legacy.

Definition u3_longest_path (G : sgraph) (s : seq G) : Prop :=
  Legacy.is_path s /\ forall t : seq G, Legacy.is_path t -> size t <= size s.

Definition do_any_three_longest_paths_in_a_connected_graph_have_statement : Prop :=
  forall G : sgraph, 0 < #|G| -> connected [set: G] ->
    forall s1 s2 s3 : seq G,
      u3_longest_path s1 -> u3_longest_path s2 -> u3_longest_path s3 ->
      exists v : G, [/\ v \in s1, v \in s2 & v \in s3].

End U3Legacy.

(** ** Certificates *)

Lemma u3_is_path_compat (G : sgraph) (s : seq G) : Legacy.is_path s = is_path s.
Proof. by []. Qed.

Lemma u3_longest_path_compat (G : sgraph) (s : seq G) :
  U3Legacy.u3_longest_path s <-> longest_path s.
Proof. exact: iff_refl. Qed.

Lemma do_any_three_longest_paths_in_a_connected_graph_have_statement_compat :
  U3Legacy.do_any_three_longest_paths_in_a_connected_graph_have_statement <->
  do_any_three_longest_paths_in_a_connected_graph_have_statement.
Proof. exact: iff_refl. Qed.
