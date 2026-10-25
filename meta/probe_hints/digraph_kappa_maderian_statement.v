(** Witness hint (Any-lane re-encoding, 2026-10-25): an axiom-free REFUTATION of
    [Digraph.conjectures.X179.digraph_kappa_maderian_statement] as encoded before its
    re-encoding (corpus row arxiv:1610.00876#05, Problem 16).

    [x179_k_vertex_strongly_connected G k] asks only that deleting fewer than k vertices leaves
    the remaining vertices mutually reachable; it drops the standard "at least k + 1 vertices".
    The one-vertex digraph is then k-strong for every k, and it cannot host the two injective
    branch vertices of a subdivision of the two-vertex digraph without arcs, so no k works for
    that digraph.  With the host guard [k < #|G|] this file no longer compiles
    (hint-stale-FIX-OK). *)
From HB Require Import structures.
From mathcomp Require Import all_boot.
From Digraph Require Import prelude digraph.
From Digraph.conjectures Require Import X179.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** The one-vertex digraph and the two-vertex digraph, both without arcs. *)
Definition pt1 : Type := unit.
HB.instance Definition _ := Finite.copy pt1 unit.
HB.instance Definition _ := HasArc.Build pt1 (fun _ _ => false).

Definition two2 : Type := bool.
HB.instance Definition _ := Finite.copy two2 bool.
HB.instance Definition _ := HasArc.Build two2 (fun _ _ => false).

Lemma pt1_k_strong (k : nat) : x179_k_vertex_strongly_connected pt1 k.
Proof. by move=> S _ [] [] _ _; exact: connect0. Qed.

Lemma refuted : ~ digraph_kappa_maderian_statement.
Proof.
move=> /(_ two2) [[k hk] _].
have [b [binj _]] := hk pt1 (@pt1_k_strong k).
have : (true : two2) = false by apply: binj; case: (b true); case: (b false).
by [].
Qed.

Print Assumptions refuted.
