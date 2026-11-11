(** * Minor.conjectures.X301 -- v2 row: Wood's conjecture, pathwidth of graphs of treewidth t without a
      subdivision of a complete binary tree of height h (record arXiv:2008.00779) *)

From GTBase Require Import base finite_graph pathwidth.
From Minor.foundations Require Import containment width_params.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** X301 statement ******************************************************)

(** Reused vocabulary: Minor.foundations.width_params [tw_le] / [tw_ge] (treewidth at most / at least),
    Minor.foundations.containment [has_subdivision] (G contains a subdivision of H), GTBase.pathwidth
    [pathwidth_at_most] (the pathwidth family's canonical) and GTBase.finite_graph [fg_mk_sgraph] (the simple
    graph of a relation).  The complete binary tree is written out in the statement.  X301 declares no helper of
    its own. *)

(** Corpus row: studies:std_wood_s_conjecture_on_pathwidth_and_binary_tree_s
    Site: none
    Review: none
    English statement: (Wood; studies slice of the corpus, record arXiv:2008.00779)
      Every graph with treewidth t and not containing a subdivision of a complete binary tree of height h has
      pathwidth at most f(t) * h for some function f.
    Definitions: [tw_le G t] - G has a tree decomposition (coq-graph-theory's [sdecomp], over a forest) whose bags
      have at most t + 1 vertices; [tw_ge G t] - every such bound t' has t <= t'; so [tw_le G t] and [tw_ge G t]
      together say that G has treewidth t; [pathwidth_at_most G k] - G has a decomposition indexed by a path whose
      bags have at most k + 1 vertices (GTBase.pathwidth); [fg_mk_sgraph (fun i j : 'I_(2 ^ h.+1).-1 => ...)] -
      the complete binary tree of height h, heap-indexed: its 2^(h+1) - 1 nodes are 0, ..., 2^(h+1) - 2, node
      j > 0 is a child of node (j - 1) / 2, so node i has the children 2i + 1 and 2i + 2 when i < 2^h - 1, and the
      nodes 2^h - 1, ..., 2^(h+1) - 2 are the leaves, h edges below the root 0; [has_subdivision G H] - G contains
      a subdivision of H as a subgraph: distinct branch vertices for the vertices of H and, for each edge of H, a
      path between their branch vertices whose interior avoids every branch vertex and the interiors of the other
      paths (Minor.foundations.containment).
    Notes: encoded as stated (arXiv:2008.00779v4, Groenland, Joret, Nadara and Walczak, arxiv_v4.tex l.129: Wood
      conjectured "a statement of this type, with a bound of the form f(t) h on the pathwidth for some function
      f"), with the record's definitions (l.182-203): graphs are finite and simple, and the graph with no vertex is
      allowed; a tree decomposition is indexed by a tree, its width is the largest bag size minus one, and the
      treewidth is the least width (a forest index gives the same values: joining the trees of a forest by edges
      keeps the nodes of every vertex connected); a path decomposition is indexed by a path; a complete binary
      tree of height h has two children at every non-leaf node and h edges on every root-to-leaf path, so
      2^(h+1) - 1 nodes; a subdivision of a tree replaces each edge by a path whose internal nodes are new and
      private to it, and it is contained as a subgraph (l.133, l.240).  One f serves every t, h and G.  For h = 0
      the tree has one node, so only the graph with no vertex qualifies; that graph has treewidth -1 in the
      record's convention and t = 0 here, and pathwidth 0 whatever f is.  Solved in the record: Theorem 1.1
      (thm1, l.119-122: every graph with treewidth t - 1 has pathwidth at most th + 1 or contains a subdivision of
      a complete binary tree of height h + 1), applied with t + 1 and h - 1, gives f(t) = t + 1 (lit30's ERRATA
      tuple).  The same theorem gives Kawarabayashi and Rossman's conjecture (l.127-128), another studies row. *)
Definition wood_pathwidth_binary_tree_statement : Prop :=
  exists f : nat -> nat,
    forall (t h : nat) (G : sgraph),
      tw_le G t -> tw_ge G t ->
      ~ has_subdivision G
          (fg_mk_sgraph (fun i j : 'I_(2 ^ h.+1).-1 => (0 < j) && (i == j.-1./2 :> nat))) ->
      pathwidth_at_most G (f t * h).
