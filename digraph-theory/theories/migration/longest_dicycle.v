(** * Digraph.migration.longest_dicycle — frozen longest directed cycle of X2 (library migration B14)

    Family [longest-dicycle] (meta/library_primitives/longest-dicycle.json).  [Legacy] freezes,
    verbatim as it stood at the B14 baseline 0646ae3, X2's [longest_dicycle]: [dicycle c /\ forall c',
    dicycle c' -> (size c' <= size c)%N] over [Digraph.core.dipath.dicycle], which admits a singleton
    with a loop and a digon and rejects the empty sequence and repeated entries.  The live helper now
    unfolds to the public [Digraph.foundations.longest_cycles.longest_dicycle c], whose body is this
    term, so the certificates are kernel-checked conversions; [dicycle] itself is unchanged.  No
    orientation, looplessness, connectivity, symmetry, inhabited-carrier or minimum-length premise is
    added: B13's undirected genuine-cycle contract is a different class.  [X2Legacy] freezes the
    single row, Bucic-Hendrey-Mohar-Steiner-Yepremyan's question on longest directed cycles in
    vertex-transitive digraphs, with this family's helper only.  Its weak connectivity, vertex
    transitivity, both longest premises and the raw-membership common vertex are unchanged.  B1/B2's
    X2 helpers do not reach this row and their snapshots are untouched.  Hashes and substitutions:
    meta/migration_reports/longest_dicycle.md. *)

From HB Require Import structures.
From mathcomp Require Import all_boot.
From Digraph Require Import prelude interop_graph_theory digraph oriented dipath tournament.
From Digraph Require Import automorphism domination strong.
From Digraph Require Import classic_core heroes chi_bounded dichromatic.
From GTBase Require Import walks_paths.
From Digraph.conjectures Require Import X2.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Legacy.

Definition longest_dicycle (D : diGraphType) (c : seq D) : Prop :=
  dicycle c /\ forall c' : seq D, dicycle c' -> (size c' <= size c)%N.

End Legacy.

Module X2Legacy.

Definition vertex_transitive_longest_dicycles_intersect_statement : Prop :=
  forall D : diGraphType,
    weakly_connected D -> vertex_transitiveb D ->
    forall c1 c2 : seq D,
      Legacy.longest_dicycle c1 -> Legacy.longest_dicycle c2 ->
      exists v : D, v \in c1 /\ v \in c2.

End X2Legacy.


(** ** Certificates *)

Lemma longest_dicycle_compat (D : diGraphType) (c : seq D) :
  Legacy.longest_dicycle c <-> longest_dicycle c.
Proof. exact: iff_refl. Qed.

(** arxiv:2602.16333#02 (unchanged). *)
Lemma vertex_transitive_longest_dicycles_intersect_statement_compat :
  X2Legacy.vertex_transitive_longest_dicycles_intersect_statement <->
  vertex_transitive_longest_dicycles_intersect_statement.
Proof. exact: iff_refl. Qed.

Print Assumptions longest_dicycle_compat.
Print Assumptions vertex_transitive_longest_dicycles_intersect_statement_compat.
