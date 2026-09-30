(** * Chromatic.conjectures.X64 -- v2 finite homogeneous-colouring exceptions *)

From GTBase Require Export base.
From Chromatic.conjectures Require Import X63.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X64 vocabulary ************************************************)

Definition x64_edge_set (G : sgraph) : {set {set G}} :=
  [set e : {set G} |
      [exists x : G, [exists y : G, (x -- y) && (e == [set x; y])]]].

Definition x64_delete_edge_rel (G : sgraph) (e : {set G}) : rel G :=
  fun x y => (x -- y) && ([set x; y] != e).

Lemma x64_delete_edge_sym (G : sgraph) (e : {set G}) :
  symmetric (@x64_delete_edge_rel G e).
Proof. by move=> x y; rewrite /x64_delete_edge_rel sgP setUC. Qed.

Lemma x64_delete_edge_irrefl (G : sgraph) (e : {set G}) :
  irreflexive (@x64_delete_edge_rel G e).
Proof. by move=> x; rewrite /x64_delete_edge_rel sg_irrefl. Qed.

Definition x64_delete_edge_graph (G : sgraph) (e : {set G}) : sgraph :=
  SGraph (@x64_delete_edge_sym G e) (@x64_delete_edge_irrefl G e).

Definition x64_bridgeless (G : sgraph) : Prop :=
  forall e : {set G},
    e \in x64_edge_set G ->
    connected [set: @x64_delete_edge_graph G e].

(** ** X64 statements ******************************************************)

(** Corpus row: arxiv:2511.02892#05
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/2511.02892__05/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/2511.02892__05.json
    English statement: (Barat, Dvorak, Haxell, Kardos, Luzar, Onderko, Rajnik, Sotak and Ulyanov 2025, Problem 5.2, arXiv:2511.02892)
      There is a bound N such that every connected bridgeless cubic finite simple graph with at
      least N vertices admits a 2-homogeneous colouring; equivalently, only finitely many connected
      bridgeless cubic graphs fail to admit one.
    Definitions: [x64_bridgeless G] - deleting any single edge leaves the graph connected (this
      file); [x64_delete_edge_graph G e] (this file); [x64_edge_set G] (this file);
      [x63_k_homogeneous_colouring G 2] - a proper colouring in which every vertex sees exactly two
      colours among its neighbours (X63.v); [regular G 3], [connected] (GTBase
      base/theories/base.v).
    Notes: "Finitely many exceptions" is encoded as a SIZE THRESHOLD: all graphs of the class with
      at least N vertices are good. This is equivalent to finiteness up to isomorphism, since for
      each fixed number of vertices there are finitely many graphs. *)
Definition finite_bridgeless_cubic_two_homogeneous_exceptions_statement : Prop :=
  exists N : nat,
    forall G : sgraph,
      connected [set: G] ->
      regular G 3 ->
      x64_bridgeless G ->
      N <= #|G| ->
      x63_k_homogeneous_colouring G 2.
