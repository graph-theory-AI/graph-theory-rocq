(** * Digraph.conjectures.X193 -- v2 directed-triangle-free domination row *)

From HB Require Import structures.
From mathcomp Require Import all_boot.
From Digraph Require Import prelude digraph dipath classic_core.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X193 vocabulary ***********************************************)

Definition x193_directed_triangle_free (D : diGraphType) : Prop :=
  forall c : seq D, dicycle c -> size c != 3.

Definition x193_dominates (D : diGraphType) (S : {set D}) (v : D) : bool :=
  (v \in S) || [exists u in S, u --> v].

Definition x193_dominating_set (D : diGraphType) (S : {set D}) : Prop :=
  forall v : D, x193_dominates S v.

Definition x193_domination_number_at_most (D : diGraphType) (n : nat) : Prop :=
  exists S : {set D}, x193_dominating_set S /\ #|S| <= n.

Definition x193_independence_number (D : diGraphType) (a : nat) : Prop :=
  (exists S : {set D}, stable S /\ #|S| = a) /\
  forall S : {set D}, stable S -> #|S| <= a.

(** ** X193 statements *****************************************************)

(** Corpus row: arxiv:1708.00423#00
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/1708.00423__00/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/1708.00423__00.json
    English statement: (Harutyunyan, Le, Newman, Thomasse 2017, Domination and fractional domination in digraphs, arXiv:1708.00423, Conjecture 3.5)
      There is an exponent ell such that every finite loopless digraph D with no directed cycle
      on three vertices and with independence number alpha has a dominating set of size at most
      alpha to the power ell; a set S dominates when every vertex lies in S or has an
      in-neighbour in S.
    Definitions: [x193_directed_triangle_free D] - no directed cycle of size 3 (this file);
      [x193_dominating_set S] and [x193_domination_number_at_most D n] (this file);
      [x193_independence_number D a] - the maximum size of an arc-free set is exactly a (this
      file); [stable] (conjectures/classic_core.v).
    Notes: The looplessness guard is LOAD-BEARING: without it, a digraph whose only arcs are
      loops is directed-triangle-free with independence number 0 yet needs two vertices to
      dominate, refuting the statement for every ell, while the source conjecture (over loopless
      digraphs) is open. Recorded as an audit fix in meta/BLOCKED_RETARGETING_AUDIT.md. *)
Definition directed_triangle_free_domination_polynomial_statement : Prop :=
  exists ell : nat,
    forall (D : diGraphType) (alpha : nat),
      (forall v : D, ~~ (v --> v)) ->
      x193_directed_triangle_free D ->
      x193_independence_number D alpha ->
      x193_domination_number_at_most D (alpha ^ ell).
