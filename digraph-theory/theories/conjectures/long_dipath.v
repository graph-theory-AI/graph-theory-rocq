(** * Digraph.conjectures.long_dipath — Cheng–Keevash / Thomassé long-directed-path conjecture

    Statement-only formalization of Cheng–Keevash Conjecture 1 (Thomassé's directed-path
    conjecture), arXiv:2402.16776: every oriented graph with minimum out-degree ≥ d
    contains a directed simple path of length 2d, i.e. ℓ(D) ≥ 2d.
    See docs/CONJECTURES_FORMALIZATION_PLAN.md §1, §5 (P1), §7.

    [outdeg v] is the out-degree and [ell D] the length of a longest directed simple path,
    both reused from the core. The instances δ = 3, 4, 5, 6 are PROVED
    unconditionally in [applications/ck3] and [applications/ck_path], and
    are recorded below as closed specializations of the general node. *)

From HB Require Import structures.
From mathcomp Require Import all_boot.
From Digraph Require Import prelude digraph oriented dipath ck3_main
  ckpath_k4 ckpath_k5 ckpath_k6.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Node *)

Definition cheng_keevash_conj1_statement : Prop :=
  forall (D : orientedDigraph) (d : nat),
    0 < #|D| -> (forall v : D, d <= outdeg v) -> 2 * d <= ell D.

(** ** Edges (specializations) *)

(** General ⟹ the δ = 3 instance (exactly the shape of [ck_conj1_at_3]). *)
Theorem conj1_implies_delta3 :
  cheng_keevash_conj1_statement ->
  forall D : orientedDigraph, 0 < #|D| -> (forall v : D, 3 <= outdeg v) -> 2 * 3 <= ell D.
Proof. by move=> H D *; apply: H. Qed.

(** General ⟹ the δ = 4 instance. *)
Theorem conj1_implies_delta4 :
  cheng_keevash_conj1_statement ->
  forall D : orientedDigraph, 0 < #|D| -> (forall v : D, 4 <= outdeg v) -> 2 * 4 <= ell D.
Proof. by move=> H D *; apply: H. Qed.

(** General ⟹ the δ = 5 instance. *)
Theorem conj1_implies_delta5 :
  cheng_keevash_conj1_statement ->
  forall D : orientedDigraph, 0 < #|D| -> (forall v : D, 5 <= outdeg v) -> 2 * 5 <= ell D.
Proof. by move=> H D *; apply: H. Qed.

(** General ⟹ the δ = 6 instance. *)
Theorem conj1_implies_delta6 :
  cheng_keevash_conj1_statement ->
  forall D : orientedDigraph, 0 < #|D| -> (forall v : D, 6 <= outdeg v) -> 2 * 6 <= ell D.
Proof. by move=> H D *; apply: H. Qed.

(** ** The δ = 3 node is unconditionally PROVED (applications/ck3). *)
Remark conj1_delta3_proved :
  forall D : orientedDigraph, 0 < #|D| -> (forall v : D, 3 <= outdeg v) -> 2 * 3 <= ell D.
Proof. exact: ck_conj1_at_3. Qed.

(** ** The δ = 4, 5, 6 nodes are unconditionally PROVED
    ([applications/ck_path]). *)
Remark conj1_delta4_proved :
  forall D : orientedDigraph, 0 < #|D| -> (forall v : D, 4 <= outdeg v) -> 2 * 4 <= ell D.
Proof. exact: ck_conj1_at_4. Qed.

Remark conj1_delta5_proved :
  forall D : orientedDigraph, 0 < #|D| -> (forall v : D, 5 <= outdeg v) -> 2 * 5 <= ell D.
Proof. exact: ck_conj1_at_5. Qed.

Remark conj1_delta6_proved :
  forall D : orientedDigraph, 0 < #|D| -> (forall v : D, 6 <= outdeg v) -> 2 * 6 <= ell D.
Proof. exact: ck_conj1_at_6. Qed.
