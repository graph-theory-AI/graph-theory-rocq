(** * Cycle.migration.simple_edges -- frozen edge-helper certificates *)

From GTBase Require Import base.
From Cycle.conjectures Require Import X9 X10 X24 XE1.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Legacy.

Definition edge_set (G : sgraph) : {set {set G}} :=
  [set e : {set G} |
      [exists x : G, [exists y : G, (x -- y) && (e == [set x; y])]]].

End Legacy.

Lemma x9_edge_set_compat (G : sgraph) :
  Legacy.edge_set G = x9_edge_set G.
Proof. by []. Qed.

Lemma x10_edge_set_compat (G : sgraph) :
  Legacy.edge_set G = x10_edge_set G.
Proof. by []. Qed.

Lemma x24_edge_set_compat (G : sgraph) :
  Legacy.edge_set G = x24_edge_set G.
Proof. by []. Qed.

Lemma xe1_edge_set_compat (G : sgraph) :
  Legacy.edge_set G = xe1_edge_set G.
Proof. by []. Qed.
