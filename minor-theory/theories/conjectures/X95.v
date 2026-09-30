(** * Minor.conjectures.X95 -- v2 subgraph-indexed tree-decomposition row *)

From GTBase Require Export base.
From Minor.conjectures Require Import X27.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X95 vocabulary ************************************************)

Definition x95_path_index_graph (T : sgraph) : Prop :=
  is_tree [set: T] /\ Delta T <= 2.

Definition x95_pathwidth_at_most (G : sgraph) (k : nat) : Prop :=
  exists (T : sgraph) (bag : T -> {set G}),
    x95_path_index_graph T /\
    x27_tree_decomposition bag /\
    forall t : T, #|bag t| <= k.+1.

Definition x95_index_tree_subgraph (T G : sgraph) : Prop :=
  exists f : T -> G,
    injective f /\ forall u v : T, u -- v -> f u -- f v.

Definition x95_subgraph_indexed_tree_decomposition_width_at_most
    (G : sgraph) (k : nat) : Prop :=
  exists (T : sgraph) (bag : T -> {set G}),
    is_tree [set: T] /\
    x95_index_tree_subgraph T G /\
    x27_tree_decomposition bag /\
    forall t : T, #|bag t| <= k.+1.

(** ** X95 statements ******************************************************)

(** Corpus row: studies:std_blanco_cook_hatzel_hilaire_illingworth_mccarty_q
    Site: none
    Review: none
    English statement: (Blanco, Cook, Hatzel, Hilaire, Illingworth and McCarty, question on
      subgraph tree-decompositions)
      There is a function f from the naturals to the naturals such that every connected finite
      simple graph of pathwidth at most p admits a tree-decomposition whose indexing tree
      embeds into the graph as a subgraph and whose width is at most f(p).
    Definitions: [x95_path_index_graph T] - T is a tree of maximum degree at most 2, i.e. a path
      (minor-theory/theories/conjectures/X95.v); [x95_pathwidth_at_most G k] - G admits a
      tree-decomposition indexed by such a path with all bags of at most k+1 vertices (same
      file); [x95_index_tree_subgraph T G] - there is an injective map from the vertices of T to
      those of G carrying edges to edges, i.e. T embeds into G as a (not necessarily induced)
      subgraph (same file); [x95_subgraph_indexed_tree_decomposition_width_at_most G k] - G
      admits a tree-decomposition whose index tree embeds into G as a subgraph and all of whose
      bags have at most k+1 vertices (same file); [x27_tree_decomposition bag]
      (minor-theory/theories/conjectures/X27.v).
    Notes: f is quantified before p and G.  "Indexing tree is a subgraph of G" is read as an
      injective edge-preserving embedding of the index tree into G; nothing ties a node of the
      index tree to the bag it indexes, which is the weaker (and standard) reading of the
      question.  Connectivity of G is a hypothesis, as in the source. *)
Definition subgraph_indexed_tree_decomposition_pathwidth_bound_statement : Prop :=
  exists f : nat -> nat,
    forall (p : nat) (G : sgraph),
      connected [set: G] ->
      x95_pathwidth_at_most G p ->
      x95_subgraph_indexed_tree_decomposition_width_at_most G (f p).
