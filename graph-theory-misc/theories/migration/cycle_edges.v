(** * GTMisc.migration.cycle_edges — frozen raw cyclic edge support of X216 (library migration B11)

    Batch B, family [cycle-edges] (meta/library_primitives/cycle-edges.json).  [Legacy] freezes,
    verbatim as it stood at the B11 baseline 0a0203e, X216's raw finite support
    [x216_cycle_edges] ([[set e | e \in [seq [set p.1; p.2] | p <- zip c (rot 1 c)]]]), which
    now unfolds to [GTBase.walks_paths.seq_cycle_edge_set c], the same term, so the certificates
    are kernel-checked conversions.  [X216Legacy] freezes the second-Hamilton-cycle output
    specification and the row, whose BLOCKED status (computation model; search versus decision)
    and documented defect are unchanged.  Hashes and substitutions:
    meta/migration_reports/cycle_edges.md. *)

From GTBase Require Import base.
From GTMisc.conjectures Require Import X216.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Legacy.

Definition x216_cycle_edges (G : sgraph) (c : seq G) : {set {set G}} :=
  [set e : {set G} | e \in [seq [set p.1; p.2] | p <- zip c (rot 1 c)]].

End Legacy.

Module X216Legacy.

Definition second_hamilton_output (x : x216_cycle_instance) (out : data) : Prop :=
  exists c' : seq (projT1 x),
    [/\ hamiltonian_cycle (projT1 x) c',
        Legacy.x216_cycle_edges c' != Legacy.x216_cycle_edges (projT2 x) &
        out = x216_enc_seq c'].

Definition second_hamilton_cycle_cubic_polytime_statement : Prop :=
  polytime_outputs_on_class x216_enc_cycle_instance
    x216_cubic_hamiltonian_instance second_hamilton_output.

End X216Legacy.

(** ** Certificates *)

Lemma x216_cycle_edges_compat (G : sgraph) (c : seq G) : Legacy.x216_cycle_edges c = x216_cycle_edges c.
Proof. by []. Qed.

Lemma x216_second_hamilton_output_compat (x : x216_cycle_instance) (out : data) :
  X216Legacy.second_hamilton_output x out <-> x216_second_hamilton_output x out.
Proof. exact: iff_refl. Qed.

(** bm:bm-021, BLOCKED and unchanged. *)
Lemma second_hamilton_cycle_cubic_polytime_statement_compat :
  X216Legacy.second_hamilton_cycle_cubic_polytime_statement <->
  second_hamilton_cycle_cubic_polytime_statement.
Proof. exact: iff_refl. Qed.

Print Assumptions x216_cycle_edges_compat.
Print Assumptions second_hamilton_cycle_cubic_polytime_statement_compat.
