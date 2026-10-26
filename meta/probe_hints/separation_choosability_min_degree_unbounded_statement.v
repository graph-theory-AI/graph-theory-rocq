(** Witness hint (A2 source repair, 2026-10-26): an axiom-free REFUTATION of
    [Chromatic.conjectures.X203.separation_choosability_min_degree_unbounded_statement] as encoded before
    its repair (corpus row arxiv:1802.03727#00).

    The body quantifies over every graph, the empty graph ['K_0] included.  ['K_0] has minimum degree at
    least d for every d (it has no vertex), and it is separation j-choosable for every j (the empty
    colouring), so the required lower bound x d on its separation choosability fails as soon as x d is
    positive, and an unbounded x has such a d.  The faithfulness audit of 2026-07-17
    (meta/BLOCKED_RETARGETING_AUDIT.md) recorded the defect; this file checks it in the kernel.  A graph of
    minimum degree d has a vertex; with the guard [0 < #|G|] this file no longer compiles
    (hint-stale-FIX-OK). *)
From GTBase Require Import base.
From Chromatic.conjectures Require Import X203.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** The empty graph is separation j-choosable for every j: the empty colouring. *)
Lemma k0_separation_choosable (j : nat) : x203_separation_choosable 'K_0 j.
Proof.
move=> C L _.
have f : 'K_0 -> C by case=> m hm; exfalso; move: hm; rewrite ltn0.
by exists f; split=> [[m hm]|[m hm]]; exfalso; move: hm; rewrite ltn0.
Qed.

Lemma k0_min_degree (d : nat) : x203_min_degree_at_least 'K_0 d.
Proof. by case=> m hm; exfalso; move: hm; rewrite ltn0. Qed.

Lemma refuted : ~ separation_choosability_min_degree_unbounded_statement.
Proof.
move=> [x [hx h]].
have [d hd] := hx 1.
have := h d 'K_0 (k0_min_degree d) 0 hd.
by apply; exact: k0_separation_choosable.
Qed.

Print Assumptions refuted.
