(** * Chromatic.conjectures.X66 -- v2 good trees disjoint-union row *)

From GTBase Require Export base.
From Chromatic.conjectures Require Import U8 X3.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X66 vocabulary ************************************************)

Definition x66_disjoint_union_rel (G H : sgraph) : rel (G + H) :=
  fun x y =>
    match x, y with
    | inl a, inl b => a -- b
    | inr a, inr b => a -- b
    | _, _ => false
    end.

Lemma x66_disjoint_union_sym (G H : sgraph) :
  symmetric (@x66_disjoint_union_rel G H).
Proof. by move=> [a|a] [b|b] //=; rewrite sgP. Qed.

Lemma x66_disjoint_union_irrefl (G H : sgraph) :
  irreflexive (@x66_disjoint_union_rel G H).
Proof. by move=> [a|a] //=; rewrite sg_irrefl. Qed.

Definition x66_disjoint_union (G H : sgraph) : sgraph :=
  SGraph (@x66_disjoint_union_sym G H) (@x66_disjoint_union_irrefl G H).

Definition x66_good (H : sgraph) : Prop :=
  x3_polynomially_chi_bounded (fun G : sgraph => ~ has_induced H G).

(** ** X66 statements ******************************************************)

(** Corpus row: arxiv:2202.09118#03
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/2202.09118__03/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/2202.09118__03.json
    English statement: (Chudnovsky, Scott, Seymour and Spirkl 2022, open problem on disjoint unions of good trees, arXiv:2202.09118)
      For all finite simple graphs H1 and H2 that are trees, if the class of H1-free graphs and the
      class of H2-free graphs are both polynomially chi-bounded, then so is the class of graphs with
      no induced copy of the disjoint union of H1 and H2.
    Definitions: [x66_good H] - the class of graphs with no induced H is polynomially chi-bounded
      (this file); [x66_disjoint_union G H] - the graph on the sum of the two vertex types with no
      edge between the parts (this file); [x3_polynomially_chi_bounded] (X3.v); [has_induced]
      (U8.v); [is_tree] (coq-graph-theory sgraph.v via GTBase).
    Notes: The source states this as "it is not known that ..."; the Rocq body is the positive
      assertion whose status is open. Goodness is spelled out through the polynomial chi-boundedness
      of the corresponding induced-free class, as the source defines it. *)
Definition good_trees_disjoint_union_good_statement : Prop :=
  forall H1 H2 : sgraph,
    is_tree [set: H1] ->
    is_tree [set: H2] ->
    x66_good H1 ->
    x66_good H2 ->
    x66_good (x66_disjoint_union H1 H2).
