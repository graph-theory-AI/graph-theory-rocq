(** * GTMisc.migration.simple_edges -- frozen edge-helper certificates *)

From GTBase Require Import base.
From GTMisc.conjectures Require Import X14 X20 X37 X38 X77 X102.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Legacy.

Definition exists_edge_set (G : sgraph) : {set {set G}} :=
  [set e : {set G} |
      [exists x : G, [exists y : G, (x -- y) && (e == [set x; y])]]].

Definition clique_edge_set (G : sgraph) : {set {set G}} :=
  [set e : {set G} | (#|e| == 2) && cliqueb e].

End Legacy.

Lemma x14_edge_set_compat (G : sgraph) :
  Legacy.exists_edge_set G = x14_edge_set G.
Proof. by []. Qed.

Lemma x20_edge_set_compat (G : sgraph) :
  Legacy.exists_edge_set G = x20_edge_set G.
Proof. by []. Qed.

Lemma x37_edge_set_compat (G : sgraph) :
  Legacy.exists_edge_set G = x37_edge_set G.
Proof. by []. Qed.

Lemma x38_edge_set_compat (G : sgraph) :
  Legacy.exists_edge_set G = x38_edge_set G.
Proof. by []. Qed.

Lemma x77_edge_set_compat (G : sgraph) :
  Legacy.exists_edge_set G = x77_edge_set G.
Proof. by []. Qed.

Lemma x102_edge_set_compat (G : sgraph) :
  Legacy.clique_edge_set G = x102_edge_set G.
Proof. by rewrite /x102_edge_set simple_edge_set_cliqueE. Qed.

Module X102Legacy.

Definition line_graph_of (H L : sgraph) : Prop :=
  exists f : L -> {e : {set H} | e \in Legacy.clique_edge_set H},
    injective f /\
    (forall e : {e : {set H} | e \in Legacy.clique_edge_set H},
      exists v : L, f v = e) /\
    forall x y : L,
      (x -- y) = ~~ [disjoint val (f x) & val (f y)].

Definition line_graph_of_subdivided_multiclaw (G : sgraph) : Prop :=
  exists H : sgraph, x102_subdivided_multiclaw H /\ line_graph_of H G.

Definition statement : Prop :=
  forall (I : finType) (F : I -> sgraph),
    x102_free_class_tree_alpha_bounded F <->
    exists i1 i2 i3 : I,
      x102_complete_bipartite_graph (F i1) /\
      x102_subdivided_multiclaw (F i2) /\
      line_graph_of_subdivided_multiclaw (F i3).

End X102Legacy.

Lemma x102_line_graph_of_compat (H L : sgraph) :
  X102Legacy.line_graph_of H L <-> x102_line_graph_of H L.
Proof.
rewrite /X102Legacy.line_graph_of /x102_line_graph_of.
by rewrite x102_edge_set_compat.
Qed.

Lemma x102_line_graph_of_subdivided_multiclaw_compat (G : sgraph) :
  X102Legacy.line_graph_of_subdivided_multiclaw G <->
  x102_line_graph_of_subdivided_multiclaw G.
Proof.
split=> -[H [multi line_graph]]; exists H; split=> //.
- exact/(x102_line_graph_of_compat H G).1.
- exact/(x102_line_graph_of_compat H G).2.
Qed.

Lemma x102_statement_rhs_compat (I : finType) (F : I -> sgraph) :
  (exists i1 i2 i3 : I,
      x102_complete_bipartite_graph (F i1) /\
      x102_subdivided_multiclaw (F i2) /\
      X102Legacy.line_graph_of_subdivided_multiclaw (F i3)) <->
  (exists i1 i2 i3 : I,
      x102_complete_bipartite_graph (F i1) /\
      x102_subdivided_multiclaw (F i2) /\
      x102_line_graph_of_subdivided_multiclaw (F i3)).
Proof.
split=> -[i1 [i2 [i3 [complete [multi line_graph]]]]];
  exists i1, i2, i3; split=> //; split=> //.
- exact/(x102_line_graph_of_subdivided_multiclaw_compat (F i3)).1.
- exact/(x102_line_graph_of_subdivided_multiclaw_compat (F i3)).2.
Qed.

Lemma x102_statement_compat :
  X102Legacy.statement <->
  bounded_tree_independence_forbidden_family_statement.
Proof.
split=> statement I F.
- exact: iff_trans (statement I F) (x102_statement_rhs_compat F).
- exact: iff_trans (statement I F) (iff_sym (x102_statement_rhs_compat F)).
Qed.
