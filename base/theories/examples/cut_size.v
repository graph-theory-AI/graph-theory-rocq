(** Downstream use of graph cuts ([cut_size]) and of the non-monochromatic count of a supplied
    family ([non_monochromatic_count]), without corpus imports. *)
From GTBase Require Import base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section GraphCuts.
Variable G : sgraph.
Implicit Types (A : {set G}).

Example empty_and_full_sides_cut_nothing : cut_size (set0 : {set G}) = 0 /\ cut_size [set: G] = 0.
Proof. by rewrite cut_size_set0 cut_size_setT. Qed.

Example a_side_and_its_complement_have_the_same_cut A : cut_size (~: A) = cut_size A.
Proof. exact: cut_sizeC. Qed.

(** The cut is the ordered edge count between the two (disjoint) sides. *)
Example cut_as_ordered_edge_count A : cut_size A = edges_between A (~: A).
Proof. exact: cut_size_edges_between. Qed.

(** The cut is the number of edges that are not monochromatic under membership in the side. *)
Example cut_as_non_monochromatic_edges A :
  cut_size A = non_monochromatic_count E(G) (fun x : G => x \in A).
Proof. exact: cut_size_non_monochromatic. Qed.

End GraphCuts.

(** A cut never exceeds the number of edges; one side of [K_2] cuts its edge, and graphs on at
    most one vertex have no cut edge. *)
Lemma cut_size_le_edge_count (G : sgraph) (A : {set G}) : cut_size A <= edge_count G.
Proof. by apply: subset_leq_card; apply/subsetP => e; rewrite inE => /andP[]. Qed.

Example K2_one_vertex_side : cut_size [set ord0 : 'K_2] = 1.
Proof. by rewrite cut_size_edges_between edges_between_Kn cards1 cardsC1 card_ord setICr cards0. Qed.

Example K0_K1_no_cut (A : {set 'K_0}) (B : {set 'K_1}) : cut_size A = 0 /\ cut_size B = 0.
Proof.
case: edge_count_K0_K1 => h0 h1; split; apply/eqP; rewrite -leqn0.
- by apply: leq_trans (cut_size_le_edge_count A) _; rewrite h0.
- by apply: leq_trans (cut_size_le_edge_count B) _; rewrite h1.
Qed.

Section ColouredFamilies.
Variables (T : finType) (C : eqType).
Implicit Types (F : {set {set T}}) (col : T -> C).

Example empty_family_counts_nothing col : non_monochromatic_count set0 col = 0.
Proof. exact: non_monochromatic_count_set0. Qed.

Example constant_map_counts_nothing F (c : C) : non_monochromatic_count F (fun _ : T => c) = 0.
Proof. exact: non_monochromatic_count_const. Qed.

(** Empty and one-element members are never counted, for any (non-uniform) family. *)
Example small_members_count_nothing F col :
  {in F, forall e : {set T}, #|e| <= 1} -> non_monochromatic_count F col = 0.
Proof. exact: non_monochromatic_count_small. Qed.

Example at_most_the_family F col : non_monochromatic_count F col <= #|F|.
Proof. exact: non_monochromatic_count_le. Qed.

(** A varying map: a two-colour pair counts once. *)
Example two_colour_pair (col : T -> C) (x y : T) :
  col x != col y -> non_monochromatic_count [set [set x; y]] col = 1.
Proof. exact: non_monochromatic_count_pair. Qed.

End ColouredFamilies.

(** Empty carrier and empty palette: every member of any family is empty, so nothing is counted. *)
Example empty_carrier_zero_palette (F : {set {set 'I_0}}) (col : 'I_0 -> 'I_0) :
  non_monochromatic_count F col = 0.
Proof. by apply: non_monochromatic_count_small => e _; apply: leq_trans (max_card _) _; rewrite card_ord. Qed.

(** A non-uniform family: a pair with two colours and a singleton count once in total. *)
Example nonuniform_family :
  non_monochromatic_count [set [set ord0; ord_max]; [set ord0]] (fun x : 'I_2 => x) = 1.
Proof.
apply: (@eq_card1 _ [set ord0; ord_max]) => e; rewrite !inE.
case: (e =P [set ord0; ord_max]) => [->|ne] /=.
  by apply/non_monochromatic_onP; exists ord0, ord_max; rewrite !inE !eqxx ?orbT.
case: (e =P [set ord0]) => [->|] //=.
by rewrite monochromatic_on_set1.
Qed.

Print Assumptions cut_as_ordered_edge_count.
Print Assumptions cut_as_non_monochromatic_edges.
Print Assumptions K2_one_vertex_side.
Print Assumptions nonuniform_family.
