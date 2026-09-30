(** * GTMisc.conjectures.X168 -- v2 spanning-tree polytope minor-closed row *)

From GraphTheory Require Import minor.
From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X168 vocabulary ***********************************************)

Definition x168_proper_minor_closed_class (C : sgraph -> Prop) : Prop :=
  (exists H : sgraph, forall G : sgraph, C G -> ~ minor G H) /\
  forall G H : sgraph, C G -> minor G H -> C H.

Definition x168_spanning_tree (G : sgraph) (T : {set {set G}}) : Prop :=
  T \subset fg_edges G /\
  is_tree [set: fg_labelled_sgraph T].

Record x168_extension_system (G : sgraph) (facets : nat) := {
  x168_aux_dim : nat;
  x168_ineq_index : finType;
  x168_ineq_count : #|{: x168_ineq_index}| <= facets;
  x168_accepts_tree : forall T : {set {set G}}, x168_spanning_tree T -> True;
  x168_rejects_non_tree : forall T : {set {set G}}, ~ x168_spanning_tree T -> True
}.

Definition x168_spanning_tree_polytope_xc (G : sgraph) (facets : nat) : Prop :=
  exists _ : x168_extension_system G facets, True.

(** ** X168 statements *****************************************************)

(** Corpus row: arxiv:1604.07976#01
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/1604.07976__01/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/1604.07976__01.json
    English statement: (Fiorini, Huynh, Joret and Pashkovich 2016, "Smaller Extended
      Formulations for the Spanning Tree Polytope of Bounded-genus Graphs", Conjecture 2)
      For every proper minor-closed class C of finite simple graphs there is a constant K such
      that every connected graph G in C admits an extension system for its spanning-tree
      polytope with at most K * (|V(G)| + 1) inequalities; that is, the extension complexity of
      the spanning-tree polytope is O(|V(G)|).
    Definitions: [x168_proper_minor_closed_class C] - some graph is a minor of no member of C,
      and C is closed under minors (this file); [x168_spanning_tree G T] - T is a set of edges
      of G whose labelled graph is a tree (this file); [x168_extension_system G facets] - a
      record carrying an auxiliary dimension, a finite index of inequalities of cardinality at
      most [facets], and two linking fields (this file);
      [x168_spanning_tree_polytope_xc G facets] - such a record exists (this file);
      [fg_edges], [fg_labelled_sgraph] - GTBase finite_graph.v; [minor], [is_tree],
      [connected] - coq-graph-theory.
    Notes: KNOWN UNFAITHFUL, row leg is blocked (faithfulness audit 2026-07-17,
      meta/BLOCKED_RETARGETING_AUDIT.md).  As in
      graph-theory-misc/theories/conjectures/X167.v, extension complexity is not modelled: the
      linking fields [x168_accepts_tree] and [x168_rejects_non_tree] have conclusion [True],
      and the only real field is a cardinality bound on an index type that an empty index
      satisfies, so the statement is vacuously provable.  Recorded in
      meta/STATEMENT_IMPROVEMENTS.md. *)
Definition minor_closed_spanning_tree_polytope_linear_xc_statement : Prop :=
  forall C : sgraph -> Prop,
    x168_proper_minor_closed_class C ->
    exists K : nat,
      forall G : sgraph,
        C G ->
        connected [set: G] ->
        x168_spanning_tree_polytope_xc G (K * #|G|.+1).
