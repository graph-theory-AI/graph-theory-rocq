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
  simple_edge_set G.

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

(** Studies slice: Dallard-Krnc-Kwon-Milanic-Munaro-Storgel-Wiederrecht
    characterization conjecture for finite forbidden families whose free class
    has bounded tree-independence number. *)
Definition bounded_tree_independence_forbidden_family_statement : Prop :=
  forall (I : finType) (F : I -> sgraph),
    x102_free_class_tree_alpha_bounded F <->
    exists i1 i2 i3 : I,
      x102_complete_bipartite_graph (F i1) /\
      x102_subdivided_multiclaw (F i2) /\
      x102_line_graph_of_subdivided_multiclaw (F i3).
