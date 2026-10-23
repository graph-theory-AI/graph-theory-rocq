(** * Digraph.conjectures.long_dipath_k7 — the δ = 7 node of Cheng–Keevash Conjecture 1

    The δ = 7 instance of [cheng_keevash_conj1_statement] (long_dipath.v) is PROVED
    unconditionally in [applications/ck_path] ([ckpath_k7_concrete]: the checked C12 / C13
    certificate families).  It is recorded here, in the pattern of the δ = 3, 4, 5, 6 nodes
    of long_dipath.v, as an implication edge and a closed specialization.  It is kept in its
    own file so that the statement file long_dipath.v and its grounding dependents do not
    import the k = 7 certificate families (about 2300 generated modules). *)

From HB Require Import structures.
From mathcomp Require Import all_boot.
From Digraph Require Import prelude digraph oriented dipath long_dipath
  ckpath_k7_concrete.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** General ⟹ the δ = 7 instance (exactly the shape of [ck_conj1_at_7]). *)
Theorem conj1_implies_delta7 :
  cheng_keevash_conj1_statement ->
  forall D : orientedDigraph, 0 < #|D| -> (forall v : D, 7 <= outdeg v) -> 2 * 7 <= ell D.
Proof. by move=> H D *; apply: H. Qed.

(** ** The δ = 7 node is unconditionally PROVED ([applications/ck_path]). *)
Remark conj1_delta7_proved :
  forall D : orientedDigraph, 0 < #|D| -> (forall v : D, 7 <= outdeg v) -> 2 * 7 <= ell D.
Proof. exact: ck_conj1_at_7. Qed.
