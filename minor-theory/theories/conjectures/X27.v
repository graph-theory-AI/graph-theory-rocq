(** * Minor.conjectures.X27 -- v2 bounded treewidth row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X27 vocabulary ************************************************)

Definition x27_tree_decomposition
    (G T : sgraph) (bag : T -> {set G}) : Prop :=
  (forall v : G, [exists t : T, v \in bag t]) /\
  (forall x y : G, x -- y -> [exists t : T, (x \in bag t) && (y \in bag t)]) /\
  forall v : G, connected [set t : T | v \in bag t].

Definition x27_treewidth_at_most (G : sgraph) (k : nat) : Prop :=
  exists (T : sgraph) (bag : T -> {set G}),
    is_tree [set: T] /\
    x27_tree_decomposition bag /\
    forall t : T, #|bag t| <= k.+1.

Definition x27_consecutive_in_cycle (G : sgraph) (c : seq G) (x y : G) : bool :=
  ((x, y) \in zip c (rot 1 c)) || ((y, x) \in zip c (rot 1 c)).

Definition x27_hole (G : sgraph) (c : seq G) : Prop :=
  ucycle (--) c /\ 3 < size c /\
  forall x y : G,
    x \in c -> y \in c -> x -- y -> x != y ->
    x27_consecutive_in_cycle c x y.

Definition x27_even_hole_free (G : sgraph) : Prop :=
  forall c : seq G,
    x27_hole c ->
    ~~ odd (size c) ->
    False.

(** ** X27 statements ******************************************************)

(** Corpus row: arxiv:2008.05504#00
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/2008.05504__00/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/2008.05504__00.json
    English statement: (Aboulker, Adler, Kim, Sintiari and Trotignon 2020, "On the tree-width
      of even-hole-free graphs", Conjecture 2)
      There is a function f from the naturals to the naturals such that every even-hole-free
      finite simple graph of maximum degree at most d has treewidth at most f(d).
    Definitions: [x27_consecutive_in_cycle c x y] - x and y are consecutive in the cyclic order
      of the sequence c (minor-theory/theories/conjectures/X27.v); [x27_hole c] - c is an
      induced cycle on more than three vertices: c is a uniq cycle and its only edges among its
      own vertices are the consecutive ones (same file); [x27_even_hole_free G] - G has no hole
      of even length (same file); [x27_tree_decomposition bag] - every vertex lies in some bag, every edge has both ends in
      a common bag, and the bags containing a fixed vertex form a connected set of the index
      tree (minor-theory/theories/conjectures/X27.v);
      [x27_treewidth_at_most G k] - G admits a tree-decomposition all of whose bags have at most
      k+1 vertices, i.e. treewidth at most k (same file); [Delta G] - maximum degree
      (base/theories/base.v).
    Notes: the function f is quantified before d and G, so one function serves all degrees.
      Holes are required to have more than three vertices, so triangles are not holes, matching
      the usual definition of an even hole.  The corpus records this row as solved (Abrishami,
      Chudnovsky and Vuskovic, arXiv:2009.01297). *)
Definition bounded_degree_even_hole_free_bounded_treewidth_statement : Prop :=
  exists f : nat -> nat,
    forall (d : nat) (G : sgraph),
      Delta G <= d ->
      x27_even_hole_free G ->
      x27_treewidth_at_most G (f d).
