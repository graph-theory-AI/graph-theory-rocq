(** * Chromatic.conjectures.X189 -- v2 spaghetti/path decomposition chi-bound row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X189 vocabulary ***********************************************)

Definition x189_tree_decomposition
    (G T : sgraph) (bag : T -> {set G}) : Prop :=
  (forall v : G, exists t : T, v \in bag t) /\
  (forall x y : G, x -- y -> exists t : T, x \in bag t /\ y \in bag t) /\
  (forall v : G, connected [set t : T | v \in bag t]).

Definition x189_path_index_graph (T : sgraph) : Prop :=
  is_tree [set: T] /\ Delta T <= 2.

Definition x189_rooted_spaghetti_index
    (T : sgraph) (root : T) (bag : T -> {set T}) : Prop :=
  is_tree [set: T] /\
  forall v : T, connected [set t : T | v \in bag t].

Definition x189_spaghetti_tree_decomposition
    (G T : sgraph) (bag : T -> {set G}) : Prop :=
  exists root : T,
    is_tree [set: T] /\
    x189_tree_decomposition bag /\
    forall v : G, connected [set t : T | v \in bag t] /\
      (forall t : T, t \in [set u : T | v \in bag u] -> connect (--) root t).

Definition x189_spaghetti_path_decompositions_width (G : sgraph) (k : nat) : Prop :=
  exists (T P : sgraph) (tbag : T -> {set G}) (pbag : P -> {set G}),
    x189_spaghetti_tree_decomposition tbag /\
    x189_path_index_graph P /\
    x189_tree_decomposition pbag /\
    forall (t : T) (p : P), #|tbag t :&: pbag p| <= k.

(** ** X189 statements *****************************************************)

(** Corpus row: arxiv:1703.07871#00
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/1703.07871__00/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/1703.07871__00.json
    English statement: (Felsner, Joret, Micek, Trotter and Wiechert 2018, Conjecture 3, arXiv:1703.07871)
      There is a function f from naturals to naturals such that chi(G) <= f(k) for every k >= 1 and
      every finite simple graph G admitting both a spaghetti tree-decomposition and a path-
      decomposition whose bags pairwise intersect in at most k vertices.
    Definitions: [x189_tree_decomposition bag] - the usual three axioms: every vertex is in a bag,
      every edge is in a bag, and the bags containing a vertex form a connected set of indices (this
      file); [x189_path_index_graph P] - the index graph is a tree of maximum degree at most 2, i.e.
      a path (this file); [x189_spaghetti_tree_decomposition bag] - the intended "spaghetti"
      condition relative to a root (this file); [x189_spaghetti_path_decompositions_width G k] -
      such a pair of decompositions with all bag intersections of size at most k (this file).
    Notes: KNOWN UNFAITHFUL ENCODING, corpus leg blocked. The faithfulness audit of 2026-07-17,
      meta/BLOCKED_RETARGETING_AUDIT.md and the row's verification_note, found that the defining
      spaghetti condition, namely that for each vertex the bags containing it form a DIRECTED PATH
      away from the root, is absent: the only clause meant to carry it requires [connect (--) root
      t], which is vacuous since the index tree is connected. The hypothesis therefore reduces to an
      ordinary tree-decomposition plus a path-decomposition, making the statement stronger than the
      conjecture. The body is left untouched here, WP4 changes comments only. *)
Definition spaghetti_tree_path_decomposition_chi_bound_statement : Prop :=
  exists f : nat -> nat,
    forall (k : nat) (G : sgraph),
      1 <= k ->
      x189_spaghetti_path_decompositions_width G k ->
      χ([set: G]) <= f k.
