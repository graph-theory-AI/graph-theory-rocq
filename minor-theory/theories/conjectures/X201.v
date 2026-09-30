(** * Minor.conjectures.X201 -- v2 treewidth Erdos-Posa row *)

From GTBase Require Export base.
From Minor.conjectures Require Import X27.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X201 vocabulary ***********************************************)

Definition x201_treewidth_at_least (G : sgraph) (r : nat) : Prop :=
  forall k : nat, x27_treewidth_at_most G k -> r <= k.

Definition x201_k_disjoint_large_treewidth_subgraphs
    (G : sgraph) (r k : nat) : Prop :=
  exists S : 'I_k -> {set G},
    (forall i : 'I_k, S i != set0) /\
    (forall i j : 'I_k, i != j -> S i :&: S j = set0) /\
    forall i : 'I_k, x201_treewidth_at_least (induced (S i)) r.

(** ** X201 statements *****************************************************)

(** Corpus row: arxiv:1710.06282#01
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/1710.06282__01/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/1710.06282__01.json
    English statement: (Aboulker, Fiorini, Huynh, Joret, Raymond and Sau 2018, "A tight
      Erdos-Posa function for wheel minors", Conjecture 1.4)
      There is a function f from the naturals to the naturals such that for all r and k at
      least 1, every finite simple graph of treewidth at least f(r) times k times (one plus the
      base-2 logarithm of k+1, rounded down) contains k pairwise vertex-disjoint subgraphs each
      of treewidth at least r.
    Definitions: [x201_treewidth_at_least G r] - every k for which G has treewidth at most k
      satisfies r <= k, i.e. the treewidth of G is at least r
      (minor-theory/theories/conjectures/X201.v);
      [x201_k_disjoint_large_treewidth_subgraphs G r k] - there are k nonempty pairwise disjoint
      vertex sets whose induced subgraphs each have treewidth at least r (same file);
      [x27_treewidth_at_most G k] - G admits a tree-decomposition all of whose bags have at most
      k+1 vertices (minor-theory/theories/conjectures/X27.v); [trunc_log 2 n] - the base-2
      logarithm rounded down (MathComp).
    Notes: the k subgraphs are realised as the subgraphs induced on k nonempty pairwise disjoint
      vertex sets; this is equivalent to the source's "vertex-disjoint subgraphs", since a
      subgraph is contained in the induced subgraph on its vertex set and treewidth is monotone
      under subgraphs.  "Treewidth at least r" is stated negatively, as a lower bound on every
      admissible width, which avoids a minimum operator.  The k log(k+1) factor is the finite
      envelope k * (1 + trunc_log 2 (k+1)).  The corpus records this row as solved (it follows
      from Conjecture 1.2 together with the grid-minor theorem). *)
Definition treewidth_vertex_disjoint_subgraphs_log_bound_statement : Prop :=
  exists f : nat -> nat,
    forall (r k : nat) (G : sgraph),
      1 <= r ->
      1 <= k ->
      x201_treewidth_at_least G (f r * k * (trunc_log 2 k.+1).+1) ->
      x201_k_disjoint_large_treewidth_subgraphs G r k.
