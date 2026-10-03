(** * Packing.migration.cycle_edges — cyclic edge extractors of X25 and U9 (library migration B11)

    Batch B, family [cycle-edges] (meta/library_primitives/cycle-edges.json).
    - X25's raw ORDERED list [x25_cycle_edge_seq] ([map (fun p => [set p.1; p.2])
      (zip c (rot 1 c))]) now unfolds to [GTBase.walks_paths.seq_cycle_edge_list c].  Its frozen
      copy, the Hamiltonian edge-set chain, the perfect one-factorization chain and Kotzig's row
      are REUSED unchanged from M1's complete snapshot
      [Packing.migration.simple_edges.X25Legacy] (frozen at 061154c and kept by C2), which also
      freezes the pre-M1 edge set and the pre-C2 perfect matching: the row reaches no live helper
      of M1, C2 or this family.  The certificates below restate M1's over that snapshot.
    - U9's successor image [cycle_edgesG] ([[set [set x; next c x] | x in [set z | z \in c]]])
      now unfolds to [GTBase.walks_paths.seq_next_edge_set c]; [Legacy] freezes it with its
      explicit [Arguments], and [U9Legacy] the hypercube matching row, with this family's helper
      only.
    Every certificate is a kernel-checked conversion, except the one-factorization chain and the
    X25 row, which go through M1's certificates (C2's [perfect_matching_exactly_oneP]).  Hashes and
    substitutions: meta/migration_reports/cycle_edges.md. *)

From GTBase Require Import base.
From Packing.conjectures Require Import X25 U9.
From Packing.migration Require simple_edges.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Legacy.

Definition cycle_edgesG (G : sgraph) (c : seq G) : {set {set G}} :=
  [set [set x; next c x] | x in [set z | z \in c]].
Arguments cycle_edgesG : clear implicits.

End Legacy.

Module U9Legacy.

Definition matchings_extends_to_hamilton_cycles_in_hypercubes_statement : Prop :=
  forall (d : nat) (M : {set {set hypercube d}}),
    2 <= d -> is_matching_edges M ->
    exists c : seq (hypercube d),
      hamiltonian_cycleG (hypercube d) c /\
      M \subset Legacy.cycle_edgesG (hypercube d) c.

End U9Legacy.

(** ** X25: certificates over M1's complete snapshot *)

Lemma x25_cycle_edge_seq_compat (G : sgraph) (c : seq G) :
  Packing.migration.simple_edges.X25Legacy.cycle_edge_seq c = x25_cycle_edge_seq c.
Proof. by []. Qed.

Lemma x25_hamiltonian_edge_set_compat (G : sgraph) (F : {set {set G}}) :
  Packing.migration.simple_edges.X25Legacy.hamiltonian_edge_set F <-> x25_hamiltonian_edge_set F.
Proof. exact: iff_refl. Qed.

Lemma x25_perfect_one_factorization_compat (n : nat) (col : {set 'K_n} -> 'I_(n.-1)) :
  Packing.migration.simple_edges.X25Legacy.perfect_one_factorization col <->
  x25_perfect_one_factorization col.
Proof. exact: Packing.migration.simple_edges.x25_perfect_one_factorization_compat. Qed.

(** studies:std_kotzig_s_perfect_1_factorization_conjecture: the complete M1/C2 snapshot,
    unchanged by this family. *)
Lemma kotzig_perfect_one_factorization_statement_compat :
  Packing.migration.simple_edges.X25Legacy.statement <-> kotzig_perfect_one_factorization_statement.
Proof. exact: Packing.migration.simple_edges.x25_statement_compat. Qed.

(** ** U9 *)

Lemma cycle_edgesG_compat (G : sgraph) (c : seq G) : Legacy.cycle_edgesG G c = cycle_edgesG G c.
Proof. by []. Qed.

Lemma matchings_extends_to_hamilton_cycles_in_hypercubes_statement_compat :
  U9Legacy.matchings_extends_to_hamilton_cycles_in_hypercubes_statement <->
  matchings_extends_to_hamilton_cycles_in_hypercubes_statement.
Proof. exact: iff_refl. Qed.

Print Assumptions x25_cycle_edge_seq_compat.
Print Assumptions kotzig_perfect_one_factorization_statement_compat.
Print Assumptions cycle_edgesG_compat.
Print Assumptions matchings_extends_to_hamilton_cycles_in_hypercubes_statement_compat.
