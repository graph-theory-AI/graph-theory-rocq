(** * Topological.migration.simple_edges -- frozen edge-helper certificate *)

From GTBase Require Import base.
From Topological.conjectures Require Import X158.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Legacy.

Definition edge_set (G : sgraph) : {set {set G}} :=
  [set e : {set G} |
      [exists x : G, [exists y : G, (x -- y) && (e == [set x; y])]]].

End Legacy.

Lemma x158_edge_set_compat (G : sgraph) :
  Legacy.edge_set G = x158_edge_set G.
Proof. by []. Qed.
