(** * Minor.conjectures.implications_X228 — corpus-relation edges of wave X228

    One confirmed [implies] edge of meta/corpus_relations.json has an X228 row as
    its source: e126, from the layered-treewidth / queue-number row
    (arxiv:1810.08314#00) to [planar_graphs_bounded_queue_number_statement]
    (arxiv:1507.01120#00).  Its target lives in topological-graph-theory, which
    minor-theory does not import, so the edge is recorded as a candidate
    annotation only — the implication is a hypothesis-class containment resting on
    the external theorem "planar graphs have layered treewidth at most 3"
    (Dujmovic, Morin and Wood, JCTB 2017), which is not available here.

    The other X228 row, arxiv:2002.00496#02, is BLOCKED (see X228.v) and has no
    related edge.  Axiom-free: no [Admitted], no [Axiom]. *)

From GTBase Require Import base.
From Minor.foundations Require Import containment width_params.
From Minor.conjectures Require Import X228.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** A proved fragment of the e126 argument that needs no planarity layer: the
    conclusion of the source statement is monotone in the queue bound, so a
    class of bounded layered treewidth inherits ONE queue bound from the
    statement's function [f]. *)
Lemma queue_number_leW (G : sgraph) (m n : nat) :
  m <= n -> queue_number_le G m -> queue_number_le G n.
Proof.
move=> mn [ord [q [oinj qlt nest]]]; exists ord, q; split=> //.
by move=> e eE; exact: leq_trans (qlt e eE) mn.
Qed.

(* cross-package edge bounded_layered_treewidth_bounded_queue_number_statement -> planar_graphs_bounded_queue_number_statement: annotation and proof now live in atlas/theories/conjectures/implications_A1.v or A2.v (wave A1, 2026-09-24) *)

Print Assumptions queue_number_leW.
