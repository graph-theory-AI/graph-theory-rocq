(** Witness hint (A2 source repair, 2026-10-26): an axiom-free REFUTATION of
    [Chromatic.conjectures.X210.surface_conflict_colouring_sqrt_genus_statement] as encoded before its
    repair (corpus row arxiv:1803.10962#00).

    The body admits k = 0: for the planar graph K_1 ([surface_embeddable_K1], g = 0) the hypothesis
    C' * 0 <= 0 * 0 holds for every C and C', and K_1 has no colouring by no colour, whatever the
    conflicts.  The faithfulness audit of 2026-07-17 (meta/BLOCKED_RETARGETING_AUDIT.md) called the body
    vacuous-looking; it is false.  With the guard 0 < k this file no longer compiles (hint-stale-FIX-OK). *)
From GTBase Require Import base.
From Chromatic.conjectures Require Import X210.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma refuted : ~ surface_conflict_colouring_sqrt_genus_statement.
Proof.
move=> [C [C' h]].
have hk : C' * 0 <= 0 * 0 by rewrite muln0.
have := h 'K_1 0 0 surface_embeddable_K1 hk.
move=> /(_ (fun _ _ _ _ => false)) [].
  by split=> u v; rewrite (ord1 u) (ord1 v) sg_irrefl.
by move=> col _; case: (col ord0).
Qed.

Print Assumptions refuted.
