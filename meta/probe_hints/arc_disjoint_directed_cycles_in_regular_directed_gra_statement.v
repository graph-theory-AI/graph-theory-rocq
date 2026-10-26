(** Witness hint (Lancelot's lane, item 4b, 2026-10-26): an axiom-free REFUTATION of
    [Digraph.conjectures.P9.arc_disjoint_directed_cycles_in_regular_directed_gra_statement] as
    encoded before its non-emptiness guard (corpus row
    opg:arc_disjoint_directed_cycles_in_regular_directed_graphs).

    The empty digraph is k-diregular for every k, vacuously, but it has no directed cycle, so at
    k = 1 it cannot carry the required binomial(2, 2) = 1 cycle.  The source's k-regular digraphs
    have vertices.  With the guard [0 < #|D|] this file no longer compiles (hint-stale-FIX-OK). *)
From HB Require Import structures.
From mathcomp Require Import all_boot.
From Digraph Require Import prelude digraph oriented tournament dipath strong.
From Digraph Require Import classic_core P9.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition empty0 : Type := 'I_0.
HB.instance Definition _ := Finite.on empty0.
HB.instance Definition _ := HasArc.Build empty0 (fun _ _ => false).

Lemma refuted : ~ arc_disjoint_directed_cycles_in_regular_directed_gra_statement.
Proof.
move=> /(_ empty0 1) h.
have hreg : diregular empty0 1.
  by apply/forallP => v; exfalso; exact: (elimF idP (ltn0 v) (ltn_ord v)).
have [P [hall _ hsz]] := h hreg.
case: P hall hsz => [|c P] //= /andP [hc _] _.
case: c hc => [|x c] //= _.
exfalso; exact: (elimF idP (ltn0 x) (ltn_ord x)).
Qed.

Print Assumptions refuted.
