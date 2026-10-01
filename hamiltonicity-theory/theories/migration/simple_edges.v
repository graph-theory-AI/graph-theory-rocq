(** * Hamilton.migration.simple_edges -- frozen edge-helper certificate *)

From GTBase Require Import base.
From Hamilton.conjectures Require Import U2.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Legacy.

Definition edge_set (G : sgraph) : {set {set G}} :=
  [set e : {set G} | [exists x, exists y, (x -- y) && (e == [set x; y])]].

End Legacy.

Lemma edge_set_compat (G : sgraph) :
  Legacy.edge_set G = edge_set G.
Proof. by []. Qed.
