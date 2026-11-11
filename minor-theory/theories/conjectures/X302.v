(** * Minor.conjectures.X302 -- v2 row: Kawarabayashi and Rossman's conjecture, polynomial pathwidth forces
      treewidth k or a subdivision of a complete binary tree of height k (record arXiv:2008.00779) *)

From GTBase Require Import base finite_graph pathwidth.
From Minor.foundations Require Import containment width_params.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** X302 statement ******************************************************)

(** Reused vocabulary: Minor.foundations.width_params [tw_ge] (treewidth at least), Minor.foundations.containment
    [has_subdivision] (G contains a subdivision of H), GTBase.pathwidth [pathwidth_at_most] (the pathwidth
    family's canonical) and GTBase.finite_graph [fg_mk_sgraph] (the simple graph of a relation).  The complete
    binary tree is written out in the statement, as in X301.  X302 declares no helper of its own. *)

(** Corpus row: studies:std_kawarabayashi_rossman_conjecture
    Site: none
    Review: none
    English statement: (Kawarabayashi and Rossman; studies slice of the corpus, record arXiv:2008.00779)
      There exists a universal constant c such that every graph with pathwidth Omega(k^c) has treewidth at least
      k or contains a subdivision of a complete binary tree of height k.
    Definitions: [pathwidth_at_most G m] - G has a decomposition indexed by a path whose bags have at most m + 1
      vertices (GTBase.pathwidth), so [~ pathwidth_at_most G m] says that G has pathwidth above m; [tw_ge G k] -
      every m such that G has a tree decomposition (coq-graph-theory's [sdecomp], over a forest) with bags of at
      most m + 1 vertices has k <= m, i.e. G has treewidth at least k (Minor.foundations.width_params);
      [fg_mk_sgraph (fun i j : 'I_(2 ^ k.+1).-1 => ...)] - the complete binary tree of height k, heap-indexed:
      its 2^(k+1) - 1 nodes are 0, ..., 2^(k+1) - 2, node j > 0 is a child of node (j - 1) / 2, so node i has the
      children 2i + 1 and 2i + 2 when i < 2^k - 1, and the nodes 2^k - 1, ..., 2^(k+1) - 2 are the leaves, k
      edges below the root 0; [has_subdivision G H] - G contains a subdivision of H as a subgraph: distinct
      branch vertices for the vertices of H and, for each edge of H, a path between their branch vertices whose
      interior avoids every branch vertex and the interiors of the other paths (Minor.foundations.containment).
    Notes: encoded as stated (arXiv:2008.00779v4, Groenland, Joret, Nadara and Walczak, arxiv_v4.tex l.127: "they
      conjectured the existence of a universal constant c such that every graph with pathwidth Omega(k^c) has
      treewidth at least k or contains a subdivision of a complete binary tree of height k"), with the record's
      definitions (l.182-203, as in X301): graphs are finite and simple, and the graph with no vertex is allowed;
      widths are the largest bag size minus one; a complete binary tree of height k has two children at every
      non-leaf node and k edges on every root-to-leaf path; a subdivision of a tree replaces each edge by a path
      whose internal nodes are new and private to it, and it is contained as a subgraph (l.133, l.240).
      "Pathwidth Omega(k^c)" is read as pathwidth above a * k^c for a constant a chosen with c.  The reading
      loses nothing, because both outcomes are monotone in k (a subdivision of the tree of height k contains one
      of every smaller height, and treewidth at least k is at least every smaller bound): a real constant a > 0
      or a real exponent c may be rounded up; "for k large enough", say k >= k0, is covered by the constant
      a * k0^c; and "at least" instead of "above" by the constant a + 1.  For k = 0 the conclusion holds
      trivially, and the graph with no vertex never meets the hypothesis.  Solved in the record: Theorem 1.1
      (thm1, l.119-122: every graph with treewidth t - 1 has pathwidth at most th + 1 or contains a subdivision
      of a complete binary tree of height h + 1), applied with t <= k and h = k - 1, bounds the pathwidth by
      k(k - 1) + 1 <= k^2, so c = 2 and a = 1 work (l.128: "Theorem 1.1 implies their conjecture with c = 2";
      lit30's ERRATA tuple).  The same theorem gives Wood's conjecture (l.129), X301. *)
Definition kawarabayashi_rossman_pathwidth_statement : Prop :=
  exists c a : nat,
    forall (k : nat) (G : sgraph),
      ~ pathwidth_at_most G (a * k ^ c) ->
      tw_ge G k \/
      has_subdivision G
        (fg_mk_sgraph (fun i j : 'I_(2 ^ k.+1).-1 => (0 < j) && (i == j.-1./2 :> nat))).
