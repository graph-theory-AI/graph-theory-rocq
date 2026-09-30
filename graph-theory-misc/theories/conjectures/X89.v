(** * GTMisc.conjectures.X89 -- v2 quartet-distance row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X89 vocabulary ************************************************)

(** Connectivity WITHIN a vertex subset [A]: a walk all of whose edges have
    both endpoints in [A] (this is exactly [connect (restrict A (--))]). *)
Definition x89_restr (G : sgraph) (A : {set G}) : rel G :=
  fun x y => (x \in A) && (y \in A) && (x -- y).
Definition x89_conn (G : sgraph) (A : {set G}) (x y : G) : bool :=
  connect (x89_restr A) x y.

(** Vertex set of the (in a tree, unique) path between [c] and [d]: the two
    endpoints and every cut-vertex whose deletion disconnects [c] from [d]. *)
Definition x89_pathset (G : sgraph) (c d : G) : {set G} :=
  [set v | (v == c) || (v == d) || ~~ x89_conn (~: [set v]) c d].

(** [{a,b}] separated from [{c,d}]: after deleting the whole [c]-[d] path, [a]
    and [b] still lie in one component -- equivalently P(a,b) and P(c,d) are
    vertex-disjoint, i.e. some edge of the tree separates {a,b} from {c,d}
    (the Bandelt-Dress / Alon-Naves-Sudakov quartet topology [ab|cd]). *)
Definition x89_split (G : sgraph) (a b c d : G) : bool :=
  x89_conn (~: x89_pathset c d) a b.

(** A phylogenetic tree on [n] leaves: a *trivalent* tree (every vertex is a
    degree-1 leaf or a degree-3 internal node -- arXiv:1505.04344 requires all
    non-leaves to have exactly three neighbours) with [n] bijectively-labelled
    degree-1 leaves. *)
Record x89_phylogenetic_tree (n : nat) := X89Tree {
  x89_tree_graph : sgraph;
  x89_leaf : 'I_n -> x89_tree_graph;
  x89_tree_is_tree : is_tree [set: x89_tree_graph];
  x89_leaf_injective : injective x89_leaf;
  x89_leaf_degree_one : forall i : 'I_n, #|N(x89_leaf i)| = 1;
  x89_trivalent : forall v : x89_tree_graph, #|N(v)| = 1 \/ #|N(v)| = 3
}.

(** Quartet topology the tree INDUCES on a 4-leaf set, as a DEFINED function of
    the tree (graph + leaves) rather than free data: take the four labels in
    ['I_n]-order [a<b<c<d] and return which pair the tree separates -- [ab|cd]
    (0), [ac|bd] (1), [ad|bc] (2).  In a trivalent tree every quartet is
    resolved, so exactly one branch fires. *)
Definition x89_quartet_shape (n : nat) (T : x89_phylogenetic_tree n)
    (Q : {set 'I_n}) : 'I_3 :=
  match enum Q with
  | [:: a; b; c; d] =>
      let L := x89_leaf T in
      if x89_split (L a) (L b) (L c) (L d) then inord 0
      else if x89_split (L a) (L c) (L b) (L d) then inord 1
      else inord 2
  | _ => inord 0
  end.

Definition x89_quartet_distance
    (n : nat) (T U : x89_phylogenetic_tree n) : nat :=
  #|[set Q : {set 'I_n} |
      (#|Q| == 4) && (x89_quartet_shape T Q != x89_quartet_shape U Q)]|.

Definition x89_max_quartet_distance (n m : nat) : Prop :=
  (exists T U : x89_phylogenetic_tree n, x89_quartet_distance T U = m) /\
  forall T U : x89_phylogenetic_tree n, x89_quartet_distance T U <= m.

Definition x89_two_thirds_asymptotic (f : nat -> nat) : Prop :=
  forall q : nat,
    3 <= q ->
    exists N : nat,
      forall n : nat,
        N <= n ->
        let b := 'C(n, 4) in
        (3 * q * f n <= (2 * q + 3) * b) /\
        ((2 * q - 3) * b <= 3 * q * f n).

(** ** X89 statements ******************************************************)

(** Corpus row: studies:std_bandelt_dress_conjecture_maximum_quartet_distanc
    Site: none
    Review: none
    English statement: (Bandelt and Dress, conjecture on the maximum quartet distance)
      There is a function f such that, for every n, f(n) is the maximum over pairs of
      phylogenetic trees on n labelled leaves of the number of four-leaf subsets on which the
      two trees induce different quartet topologies, and f(n) is asymptotically two thirds of
      binomial(n,4): for every q >= 3, eventually
      3*q*f(n) <= (2*q+3)*binomial(n,4) and (2*q-3)*binomial(n,4) <= 3*q*f(n).
    Definitions: [x89_restr A] / [x89_conn A x y] - adjacency and connectivity restricted to a
      vertex set (this file); [x89_pathset c d] - the vertex set of the unique c-d path of a
      tree, described as the two endpoints together with the vertices whose deletion separates
      them (this file); [x89_split a b c d] - the quartet topology ab|cd, i.e. a and b remain
      connected after deleting the c-d path (this file); [x89_phylogenetic_tree n] - a record
      for a trivalent tree with n injectively labelled degree-1 leaves, every non-leaf having
      exactly three neighbours (this file); [x89_quartet_shape T Q] - the topology, one of
      three values, that T induces on the four leaves of Q taken in index order (this file);
      [x89_quartet_distance T U] - the number of four-element leaf sets on which the two
      topologies differ (this file); [x89_max_quartet_distance n m] - m is attained and is an
      upper bound (this file); [x89_two_thirds_asymptotic f] - the rational-epsilon form of
      f(n) = (2/3 + o(1)) * binomial(n,4) (this file); [is_tree], [connect] - coq-graph-theory
      / MathComp.
    Notes: the quartet topology is a DEFINED function of the tree, through the edge-separation
      predicate [x89_split], not free data; this matters for faithfulness, since it prevents
      two trees from differing on all binomial(n,4) quartets - see
      meta/X10-X110_faithfulness_audit.md (X89).  The maximum is stated relationally, so the
      statement asserts both that the maximum is attained at every n and that it satisfies the
      asymptotic. *)
Definition bandelt_dress_maximum_quartet_distance_statement : Prop :=
  exists f : nat -> nat,
    (forall n : nat, x89_max_quartet_distance n (f n)) /\
    x89_two_thirds_asymptotic f.
