(** * Minor.conjectures.X127 -- v2 2-tree-width vs chromatic number row *)

From GTBase Require Export base.
From Minor.conjectures Require Import X27.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X127 vocabulary ***********************************************)

(** 2-tree-width (Dujmović–Joret–Morin–Norin–Wood; = the k=2 case of median
    tree-width, Felsner–Joret–Micek–Trotter–Wiechert arXiv:1703.07871).
    [x127_two_tree_width_le G k] holds iff G admits TWO tree-decompositions
    [(T1, bag1)] and [(T2, bag2)] (both index graphs arbitrary trees) whose bags
    are pairwise k-orthogonal: |B1_{t1} ∩ B2_{t2}| ≤ k for every t1 : T1, t2 : T2.
    "2" = the two decompositions; the parameter is the minimum such k, so
    "2-tree-width ≤ k" is exactly the existence of such a pair.  Every graph has
    2-tree-width ≤ |V(G)| via the single-bag decompositions, so it is finite
    (non-vacuous). *)
Definition x127_two_tree_width_le (G : sgraph) (k : nat) : Prop :=
  exists (T1 : sgraph) (bag1 : T1 -> {set G}) (T2 : sgraph) (bag2 : T2 -> {set G}),
    [/\ is_tree [set: T1], x27_tree_decomposition bag1,
        is_tree [set: T2], x27_tree_decomposition bag2 &
        forall (t1 : T1) (t2 : T2), #|bag1 t1 :&: bag2 t2| <= k].

(** ** X127 statements *****************************************************)

(** Corpus row: studies:std_dujmovi_joret_morin_norin_wood_question_2_tree_w
    Site: none
    Review: none
    English statement: (Dujmovic, Joret, Morin, Norin and Wood, question on 2-tree-width and
      chromatic number)
      There is a single function f from the naturals to the naturals such that for every
      natural number k, every finite simple graph of 2-tree-width at most k has chromatic
      number at most f(k).
    Definitions: [x127_two_tree_width_le G k] - G admits two tree-decompositions whose bags are
      pairwise k-orthogonal: every bag of the first decomposition meets every bag of the second
      in at most k vertices (minor-theory/theories/conjectures/X127.v);
      [x27_tree_decomposition bag] - every vertex lies in some bag, every edge has both ends in
      a common bag, and the bags containing a fixed vertex form a connected set of the index
      tree (minor-theory/theories/conjectures/X27.v).
    Notes: the function f is quantified before k and G, so one function must serve all k.  The
      "2" of 2-tree-width counts the decompositions, not the width; the parameter is the
      minimum k for which such a pair exists, so "2-tree-width at most k" is exactly the
      existence of such a pair, and every graph has 2-tree-width at most its number of vertices
      via two single-bag decompositions, so the hypothesis is not vacuous.  This is the k = 2
      case of median tree-width (Felsner, Joret, Micek, Trotter, Wiechert, arXiv:1703.07871).
      FAITHFUL-TO-REFUTED: the question is resolved negatively - the Burling graphs have
      chromatic number at least k (their Theorem 1) yet admit a tree-decomposition and a
      path-decomposition with all pairwise bag intersections of size at most 2 (their
      Theorem 2), so no such f exists and this statement is false.  The encoding is still the
      faithful reading of the row as recorded (the statement leg tracks faithfulness, not
      truth).  It is distinct from the same authors' still-open Conjecture 3, which restricts
      the first decomposition to a spaghetti tree-decomposition orthogonal to a
      path-decomposition. *)
Definition dujmovic_joret_morin_norin_wood_two_tree_width_chi_statement : Prop :=
  exists f : nat -> nat,
    forall (k : nat) (G : sgraph),
      x127_two_tree_width_le G k ->
      χ([set: G]) <= f k.
