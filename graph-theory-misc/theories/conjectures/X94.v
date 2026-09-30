(** * GTMisc.conjectures.X94 -- v2 bipartite strong Erdos-Hajnal row *)

From HB Require Import structures.
From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X94 vocabulary ************************************************)

Record x94_bigraph := X94Bigraph {
  x94_left : finType;
  x94_right : finType;
  x94_biedge : x94_left -> x94_right -> bool
}.

Definition x94_vertices (B : x94_bigraph) : Type :=
  (x94_left B + x94_right B)%type.

HB.instance Definition _ (B : x94_bigraph) := Finite.on (x94_vertices B).

Definition x94_underlying_rel (B : x94_bigraph) : rel (x94_vertices B) :=
  fun u v =>
    match u, v with
    | inl x, inr y => @x94_biedge B x y
    | inr y, inl x => @x94_biedge B x y
    | _, _ => false
    end.

Lemma x94_underlying_sym (B : x94_bigraph) :
  symmetric (@x94_underlying_rel B).
Proof. by move=> [x|y] [x'|y']. Qed.

Lemma x94_underlying_irrefl (B : x94_bigraph) :
  irreflexive (@x94_underlying_rel B).
Proof. by move=> [x|y]. Qed.

Definition x94_underlying_graph (B : x94_bigraph) : sgraph :=
  SGraph (@x94_underlying_sym B) (@x94_underlying_irrefl B).

Definition x94_forest_bigraph (B : x94_bigraph) : Prop :=
  is_forest [set: @x94_underlying_graph B].

Definition x94_bicomplement (B : x94_bigraph) : x94_bigraph :=
  {| x94_left := x94_left B;
     x94_right := x94_right B;
     x94_biedge := fun x y => ~~ @x94_biedge B x y |}.

Definition x94_induced_copy (H G : x94_bigraph) : Prop :=
  exists (fL : x94_left H -> x94_left G)
         (fR : x94_right H -> x94_right G),
    injective fL /\
    injective fR /\
    forall x y : x94_left H * x94_right H,
      @x94_biedge H x.1 x.2 = @x94_biedge G (fL x.1) (fR x.2).

Definition x94_H_free (G H : x94_bigraph) : Prop :=
  ~ @x94_induced_copy H G.

Definition x94_complete_pair
    (G : x94_bigraph) (ZL : {set x94_left G}) (ZR : {set x94_right G}) : Prop :=
  forall x y, x \in ZL -> y \in ZR -> @x94_biedge G x y.

Definition x94_anticomplete_pair
    (G : x94_bigraph) (ZL : {set x94_left G}) (ZR : {set x94_right G}) : Prop :=
  forall x y, x \in ZL -> y \in ZR -> ~~ @x94_biedge G x y.

Definition x94_pure_pair
    (G : x94_bigraph) (ZL : {set x94_left G}) (ZR : {set x94_right G}) : Prop :=
  @x94_complete_pair G ZL ZR \/ @x94_anticomplete_pair G ZL ZR.

(** ** X94 statements ******************************************************)

(** Corpus row: studies:std_bipartite_strong_erd_s_hajnal_conjecture
    Site: none
    Review: none
    English statement: (Alecu, Atminas, Lozin and Zamaraev; Axenovich, Tompkins and Weber,
      bipartite strong Erdos-Hajnal conjecture)
      For every bigraph H whose underlying graph is a forest there is a positive rational
      eps = eps_num/eps_den such that every bigraph G containing no induced copy of H and no
      induced copy of the bicomplement of H has a pure pair (ZL, ZR), i.e. ZL on the left and
      ZR on the right that are either completely adjacent or completely non-adjacent, with
      eps_num * |left(G)| <= eps_den * |ZL| and eps_num * |right(G)| <= eps_den * |ZR|.
    Definitions: [x94_bigraph] - a record with a left finite type, a right finite type and a
      biadjacency relation (this file); [x94_underlying_graph B] - the simple graph on the
      disjoint union of the two sides (this file); [x94_forest_bigraph B] - that graph is a
      forest (this file); [x94_bicomplement B] - the bigraph with the complemented biadjacency,
      the two sides kept (this file); [x94_induced_copy H G] - injective side-preserving maps
      reproducing the biadjacency exactly (this file); [x94_H_free G H] - no such copy (this
      file); [x94_complete_pair], [x94_anticomplete_pair], [x94_pure_pair] - the three pair
      conditions (this file); [is_forest] - coq-graph-theory.
    Notes: bigraphs are ordered pairs of sides, so both "H-free" and the pure pair respect the
      bipartition, as the source requires.  The linear threshold eps is a positive rational
      given by a numerator and a denominator, the inequalities being cross-multiplied; both
      sides get the SAME eps, chosen before G. *)
Definition bipartite_strong_erdos_hajnal_forest_bigraph_statement : Prop :=
  forall H : x94_bigraph,
    @x94_forest_bigraph H ->
    exists eps_num eps_den : nat,
      [/\ 0 < eps_num, 0 < eps_den
        & forall G : x94_bigraph,
            @x94_H_free G H ->
            @x94_H_free G (@x94_bicomplement H) ->
            exists (ZL : {set x94_left G}) (ZR : {set x94_right G}),
              [/\ @x94_pure_pair G ZL ZR,
                  eps_num * #|x94_left G| <= eps_den * #|ZL|
                & eps_num * #|x94_right G| <= eps_den * #|ZR|]].
