(** * GTMisc.conjectures.implications_X312 -- a dependency-graph EDGE with an X312 endpoint.

    A machine-checked implication between two statements of the corpus.  The edge is a RELATIVE theorem: a
    [Qed]-closed [Theorem A -> B] proved WITHOUT resolving either endpoint.  Axiom-free: no [Axiom] / [Parameter] /
    [Admitted] / [Conjecture].

    The edge below is a Rocq-only edge (no corpus relation): the Sintiari-Trotignon conjecture (X312,
    studies:std_sintiari_trotignon_conjecture_bounded_treewidth: for every t there is c such that every graph with
    every hole odd, no induced diamond and no induced K_t has treewidth at most c) implies, at t = 4, the statement of
    X42 (arxiv:2001.01607#00: there is c such that every (even hole, K_4, diamond)-free graph has treewidth at most c).
    X42's encoding states the same three hypotheses in minor-theory's spellings: [x27_even_hole_free G] is "no hole
    of even length" ([x27_hole] is [hole]), [x42_induced_free] is [induced_free], and [x27_treewidth_at_most] is
    [tw_le] by implications_X42's [tw_le_x27].  It is a relative theorem and resolves neither endpoint (X312 R2
    open, X42 partial in the corpus). *)

From mathcomp Require Import all_boot.
From GraphTheory Require Import preliminaries digraph sgraph.
From GTBase Require Import base induced_cycles.
From Minor.conjectures Require Import X27 X42 implications_X42.
From GTMisc.conjectures Require Import X312.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Sintiari-Trotignon (X312, t = 4) ==> even-hole, K_4 and diamond-free bounded treewidth (X42) *)

(*@EDGE from=even_hole_diamond_kt_free_bounded_treewidth_statement to=even_hole_k4_diamond_free_bounded_treewidth_statement kind=implies status=verified proof=even_hole_diamond_kt_free_bounded_treewidth_implies_even_hole_k4_diamond_free_bounded_treewidth note="Rocq-only edge (no corpus relation): the Sintiari-Trotignon conjecture (X312, every t: every graph with every hole odd, no induced diamond and no induced K_t has treewidth at most c(t)) at t = 4 gives X42 (every even-hole, K_4 and diamond-free graph has treewidth at most c). The hypotheses agree: x27_even_hole_free G (no x27_hole of even size, x27_hole = hole) gives every hole odd, x42_induced_free is induced_free, and implications_X42 tw_le_x27 turns tw_le G c into x27_treewidth_at_most G c. It is a relative theorem and resolves neither endpoint (X312 R2 open, X42 partial in the corpus)." *)
Theorem even_hole_diamond_kt_free_bounded_treewidth_implies_even_hole_k4_diamond_free_bounded_treewidth :
  even_hole_diamond_kt_free_bounded_treewidth_statement ->
  even_hole_k4_diamond_free_bounded_treewidth_statement.
Proof.
move=> hS; have [c hc] := hS 4.
exists c => G ehf k4f df.
apply: tw_le_x27; apply: hc => //.
move=> h hh; apply/negPn/negP => ev.
exact: (ehf h hh ev).
Qed.
