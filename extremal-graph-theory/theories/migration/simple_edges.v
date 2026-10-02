(** * Extremal.migration.simple_edges -- frozen edge-helper certificates *)

From GTBase Require Import base.
From Extremal.conjectures Require Import X4 X36 X60 X76 X78 X84.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Legacy.

Definition edge_set (G : sgraph) : {set {set G}} :=
  [set e : {set G} |
      [exists x : G, [exists y : G, (x -- y) && (e == [set x; y])]]].

End Legacy.

Lemma x4_edge_set_compat (G : sgraph) :
  Legacy.edge_set G = x4_edge_set G.
Proof. by rewrite /x4_edge_set sg_edge_setE. Qed.

Lemma x36_edge_set_compat (G : sgraph) :
  Legacy.edge_set G = x36_edge_set G.
Proof. by rewrite /x36_edge_set sg_edge_setE. Qed.

Lemma x60_edge_set_compat (G : sgraph) :
  Legacy.edge_set G = x60_edge_set G.
Proof. by rewrite /x60_edge_set sg_edge_setE. Qed.

Lemma x76_edge_set_compat (G : sgraph) :
  Legacy.edge_set G = x76_edge_set G.
Proof. by rewrite /x76_edge_set sg_edge_setE. Qed.

Lemma x78_edge_set_compat (G : sgraph) :
  Legacy.edge_set G = x78_edge_set G.
Proof. by rewrite /x78_edge_set sg_edge_setE. Qed.

Lemma x84_edge_set_compat (G : sgraph) :
  Legacy.edge_set G = x84_edge_set G.
Proof. by rewrite /x84_edge_set sg_edge_setE. Qed.
