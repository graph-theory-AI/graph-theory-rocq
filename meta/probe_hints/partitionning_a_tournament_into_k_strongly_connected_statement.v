(** Witness hint (Lancelot's lane, item 4b, 2026-10-26): an axiom-free REFUTATION of
    [Digraph.conjectures.P9.partitionning_a_tournament_into_k_strongly_connected_statement] as
    encoded before its non-emptiness guard on the list (corpus row
    opg:partitionning_a_tournament_into_k_strongly_connected_subtournaments).

    The empty list [ks = [::]] meets the positivity hypothesis vacuously.  Whatever g is, some
    tournament is g([::])-strong ([grounding_P9.kstrong_tournament_exists], rotational
    tournaments), and such a tournament has a vertex; but the conclusion then asks for a
    partition of its vertex set into [size ks = 0] parts.  The source partitions into
    k_1, ..., k_p with p >= 1.  With the guard [0 < size ks] this file no longer compiles
    (hint-stale-FIX-OK). *)
From HB Require Import structures.
From mathcomp Require Import all_boot.
From Digraph Require Import prelude digraph oriented tournament dipath strong.
From Digraph Require Import classic_core P9 grounding_P9.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma refuted : ~ partitionning_a_tournament_into_k_strongly_connected_statement.
Proof.
move=> [g h].
have [T hT] := kstrong_tournament_exists (g [::]).
have [part [hsz hpart _]] := h [::] isT T hT.
have hT0 : (0 < #|T|)%N by move: hT => /andP [hk _]; exact: leq_ltn_trans hk.
case/card_gt0P: hT0 => v _.
by move: hsz; case: part hpart => [|A part] // /forallP /(_ v).
Qed.

Print Assumptions refuted.
