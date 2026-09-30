(** * GTMisc.conjectures.X102 -- v2 tree-independence-number row *)

From GTBase Require Export base.
From GTMisc.conjectures Require Import X14.
From Minor.conjectures Require Import X27.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X102 vocabulary ***********************************************)

Definition x102_induced_free (G H : sgraph) : Prop :=
  forall S : {set G}, ~ inhabited (induced S ≃ H).

Definition x102_tree_alpha_at_most (G : sgraph) (a : nat) : Prop :=
  exists (T : sgraph) (bag : T -> {set G}),
    is_tree [set: T] /\
    x27_tree_decomposition bag /\
    forall t : T, α(bag t) <= a.

Definition x102_free_class_tree_alpha_bounded
    (I : finType) (F : I -> sgraph) : Prop :=
  exists a : nat,
    forall G : sgraph,
      (forall i : I, x102_induced_free G (F i)) ->
      x102_tree_alpha_at_most G a.

Definition x102_complete_bipartite_graph (G : sgraph) : Prop :=
  exists a b : nat, inhabited (G ≃ KB a b).

Definition x102_edge_set (G : sgraph) : {set {set G}} :=
  [set e : {set G} | (#|e| == 2) && cliqueb e].

Definition x102_subdivided_multiclaw (G : sgraph) : Prop :=
  is_forest [set: G] /\
  x14_subcubic G /\
  forall S : {set G},
    connected S ->
    #|[set v in S | 2 < #|N(v) :&: S|]| <= 1.

Definition x102_line_graph_of (H L : sgraph) : Prop :=
  exists f : L -> {e : {set H} | e \in x102_edge_set H},
    injective f /\
    (forall e : {e : {set H} | e \in x102_edge_set H},
      exists v : L, f v = e) /\
    forall x y : L,
      (x -- y) = ~~ [disjoint val (f x) & val (f y)].

Definition x102_line_graph_of_subdivided_multiclaw (G : sgraph) : Prop :=
  exists H : sgraph, x102_subdivided_multiclaw H /\ x102_line_graph_of H G.

(** ** X102 statements *****************************************************)

(** Corpus row: studies:std_bounded_tree_independence_number_conjecture_dall
    Site: none
    Review: none
    English statement: (Dallard, Krnc, Kwon, Milanic, Munaro, Storgel and Wiederrecht, bounded
      tree-independence-number conjecture)
      For every finite family F of graphs, the class of graphs having no member of F as an
      induced subgraph has bounded tree-independence number if and only if F contains three
      members F1, F2, F3 such that F1 is complete bipartite, F2 is a subdivided multiclaw and
      F3 is the line graph of a subdivided multiclaw.
    Definitions: [x102_induced_free G H] - no induced subgraph of G is isomorphic to H (this
      file); [x102_tree_alpha_at_most G a] - G has a tree decomposition all of whose bags have
      independence number at most a (this file); [x102_free_class_tree_alpha_bounded F] - one
      bound a works for every F-free graph (this file); [x102_complete_bipartite_graph G] - G is
      isomorphic to some KB a b (this file); [x102_edge_set G] - the two-element cliques of G,
      i.e. its edges as vertex sets (this file); [x102_subdivided_multiclaw G] - G is a forest
      of maximum degree at most 3 in which every connected vertex set contains at most one
      vertex of degree greater than 2 (this file); [x102_line_graph_of H L] - L is in bijection
      with the edges of H, adjacent exactly when the corresponding edges meet (this file);
      [x102_line_graph_of_subdivided_multiclaw G] - G is the line graph of some subdivided
      multiclaw (this file); [x27_tree_decomposition bag] - the bags cover every vertex and
      every edge and each vertex occupies a connected part of the tree
      (minor-theory/theories/conjectures/X27.v); [x14_subcubic G] - maximum degree at most 3
      (graph-theory-misc/theories/conjectures/X14.v); [is_tree], [is_forest], [connected],
      [induced], [alpha], [KB] - coq-graph-theory / GTBase vocabulary.
    Notes: the corpus text writes "if (and only if)"; the Rocq body is the full biconditional.
      A "finite class of graphs" is modelled as a family F indexed by a [finType], so it is
      finite and possibly with repetitions; nothing forces the three witnesses i1, i2, i3 to be
      distinct indices.  [x102_subdivided_multiclaw] is an approximation of "subdivided
      multiclaw" by the three properties forest, subcubic, at most one branch vertex per
      connected part, not by an explicit construction from a star. *)
Definition bounded_tree_independence_forbidden_family_statement : Prop :=
  forall (I : finType) (F : I -> sgraph),
    x102_free_class_tree_alpha_bounded F <->
    exists i1 i2 i3 : I,
      x102_complete_bipartite_graph (F i1) /\
      x102_subdivided_multiclaw (F i2) /\
      x102_line_graph_of_subdivided_multiclaw (F i3).
