(** * Digraph.conjectures.X52 -- v2 chromatic Mader bound row *)

From HB Require Import structures.
From mathcomp Require Import all_boot.
From Digraph Require Import prelude interop_graph_theory digraph oriented.
From Digraph.conjectures Require Import chi_bounded X2.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X52 vocabulary ************************************************)

(** The host [D] is guarded by [0 < #|D|]: see the GUARD REPAIR note of the row
    below.  [chi] of the empty vertex set is 0, so without the guard the bound
    [m = 0] (reached at k <= 1) would ask the EMPTY digraph to contain a
    subdivision of a nonempty tree. *)
Definition x52_mader_chi_bound (F : diGraphType) (m : nat) : Prop :=
  forall D : diGraphType, (0 < #|D|)%N ->
    (m <= χ([set: chi_bounded.underlying D]))%N ->
    contains_subdivision F D.

(** ** X52 statements ******************************************************)

(** Corpus row: arxiv:1610.00876#03
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/1610.00876__03/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/1610.00876__03.json
    English statement: (Aboulker, Cohen, Havet, Lochet, Moura, Thomasse 2016, arXiv:1610.00876, Conjecture 11)
      For every oriented tree T on k vertices, every finite NON-EMPTY digraph whose underlying
      simple graph has ordinary chromatic number at least 2k-2 contains a subdivision of T; that
      is the chromatic Mader threshold of T is at most 2k-2.
    Definitions: [x52_mader_chi_bound F m] - every NON-EMPTY digraph whose underlying graph has
      chromatic number at least m contains a subdivision of F (this file); [contains_subdivision F D]
      (conjectures/X2.v); [oriented_tree T] (conjectures/X2.v); [chi_bounded.underlying]
      (conjectures/chi_bounded.v); [chi] - coq-graph-theory's chromatic number.
    Notes: The chromatic number is the ORDINARY chi of the underlying simple graph, not the
      dichromatic number. The subtraction 2 * k - 2 is natural-number subtraction; for k = 0 or
      1 the hypothesis chromatic number at least 0 holds of every digraph, but no oriented tree
      with fewer than one vertex exists, [oriented_tree] requiring nonemptiness.
      GUARD REPAIR (2026-09-24, wave E4): [x52_mader_chi_bound] now guards its host by 0 < #|D|.
      Without it the row is FALSE at k = 1: the one-vertex oriented tree makes the threshold
      2 * 1 - 2 = 0, so EVERY digraph - the EMPTY one included, chi of the empty set being 0 -
      would have to contain a subdivision of a one-vertex digraph, which needs an injective branch
      map (wave-E3 scratch refutation degeneracy.v: X52_mader_chi_false, kept in the wave report,
      not committed). The source states the bound mader_chi(T) <= 2k-2 for every oriented tree of
      order k with NO lower bound on k, and mader_chi is a threshold on the chromatic number of a
      digraph, a notion carried by digraphs that have vertices; so the nonemptiness guard alone is
      the faithful repair and no 2 <= k guard is added. It does rescue k = 1: a one-vertex tree has
      no arc to subdivide, so any injection of its single vertex into a NON-EMPTY host is a
      subdivision model (grounding_X52.v: x52_k1_holds). Teeth and non-vacuity: grounding_X52.v
      (x52_unguarded_false, x52_hyps_nonvacuous). *)
Definition oriented_tree_mader_chi_linear_bound_statement : Prop :=
  forall (T : orientedDigraph) (k : nat),
    oriented_tree T ->
    #|T| = k ->
    x52_mader_chi_bound T (2 * k - 2).
