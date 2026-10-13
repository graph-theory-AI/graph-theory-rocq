(** * Minor.foundations.prism_configurations -- prisms as three-path configurations

    [prism_base] is the 3-prism: the simple graph on ['I_6] whose edges are the two
    triangles [{0,1,2}] and [{3,4,5}] and the perfect matching [(0,3)], [(1,4)], [(2,5)]
    between them, given by the edge list of [el_graph] (Minor.foundations.containment).

    [prism_configuration H] says that [H] IS a prism in the three-path-configuration
    sense: [H] carries a subdivision model of [prism_base] that is SPANNING and EXACT
    ([subdiv_rep]: every vertex of [H] is a branch vertex or interior to one subdivision
    path, and every edge of [H] joins two consecutive vertices of one path), and in which
    every model edge whose two ends lie on the same side ([val u < 3] for both or for
    neither; on [prism_base] these are exactly the six triangle edges) has an EMPTY
    interior.  So the two triangles stay triangles of [H], while each of the three
    matching edges becomes a path of any length, the unsubdivided edge included
    ([prism_configuration_base]).

    - This is a property of the whole host, not containment: a graph CONTAINS a prism
      when it has an induced copy of some [H] with [prism_configuration H] (as in the X220
      row).  Unused host vertices are not allowed here.
    - The restriction has teeth: subdividing one triangle edge yields a subdivision of
      [prism_base] that is not a prism configuration (public examples).
    - There is no guard: at least six vertices is a consequence
      ([prism_configuration_card]), not a hypothesis.
    - Not identified with an isomorphism class such as Topological D6emb's [is_prism]
      (G isomorphic to C_n x K_2 for some n > 2), nor with Cartesian-product prisms. *)

From GTBase Require Import base.
From Minor.foundations Require Import containment.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition prism_base : sgraph :=
  el_graph 6 [:: (0,1); (1,2); (0,2); (3,4); (4,5); (3,5); (0,3); (1,4); (2,5)].

Definition prism_configuration (H : sgraph) : Prop :=
  exists m : subdiv_model prism_base H,
    subdiv_rep m /\
    forall u v : prism_base,
      u -- v -> ((val u < 3) == (val v < 3)) -> sdm_path m u v = [::].

(** ** The base graph *)

Lemma prism_base_card : #|prism_base| = 6.
Proof. exact: card_ord. Qed.

(** Two distinct vertices on the same side are adjacent: each side is a triangle. *)
Lemma prism_base_same_side (u v : prism_base) :
  u != v -> ((val u < 3) == (val v < 3)) -> u -- v.
Proof. by case: u => [[|[|[|[|[|[|//]]]]]] ?]; case: v => [[|[|[|[|[|[|//]]]]]] ?]. Qed.

(** An edge between the two sides is one of the three matching edges. *)
Lemma prism_base_cross (u v : prism_base) :
  u -- v -> ((val u < 3) != (val v < 3)) -> (val v == val u + 3) || (val u == val v + 3).
Proof. by case: u => [[|[|[|[|[|[|//]]]]]] ?]; case: v => [[|[|[|[|[|[|//]]]]]] ?]. Qed.

(** ** Prism configurations *)

Lemma prism_configuration_base : prism_configuration prism_base.
Proof.
exists (triv_subdiv_model prism_base); split; last by [].
split=> [x|x y xy]; first by left; exists x.
by exists x, y; split=> //=; rewrite sd_consec_nil eqxx.
Qed.

Lemma prism_configuration_is_subdivision (H : sgraph) :
  prism_configuration H -> is_subdivision_of H prism_base.
Proof. by case=> m [rep _]; exists m. Qed.

Lemma prism_configuration_card (H : sgraph) : prism_configuration H -> 6 <= #|H|.
Proof.
case=> m _; rewrite -prism_base_card.
exact: (@leq_card _ _ (sdm_branch m) (@sdm_inj _ _ m)).
Qed.

(** A same-side model edge of a prism configuration is a host edge. *)
Lemma prism_configuration_side_edge (H : sgraph) (m : subdiv_model prism_base H)
    (u v : prism_base) :
  (forall u v : prism_base,
     u -- v -> ((val u < 3) == (val v < 3)) -> sdm_path m u v = [::]) ->
  u -- v -> ((val u < 3) == (val v < 3)) -> sdm_branch m u -- sdm_branch m v.
Proof.
move=> tri uv side; have := sdm_pathP m uv.
by rewrite (tri u v uv side) sd_path_nil => /andP[].
Qed.

(** The branch vertices of the two sides are two vertex-disjoint triangles of the host. *)
Lemma prism_configuration_triangles (H : sgraph) :
  prism_configuration H ->
  exists a b : 'I_3 -> H,
    [/\ forall i j : 'I_3, i != j -> a i -- a j,
        forall i j : 'I_3, i != j -> b i -- b j &
        forall i j : 'I_3, a i != b j].
Proof.
case=> m [_ tri].
pose l (i : 'I_3) : prism_base := widen_ord (isT : 3 <= 6) i.
have rlt (i : 'I_3) : i + 3 < 6 by rewrite -[6]/(3 + 3) ltn_add2r ltn_ord.
pose r (i : 'I_3) : prism_base := Ordinal (rlt i).
have lside (i : 'I_3) : val (l i) < 3 by exact: ltn_ord i.
have rge (i : 'I_3) : 3 <= val (r i) by exact: leq_addl.
have rside (i : 'I_3) : (val (r i) < 3) = false by rewrite ltnNge rge.
exists (fun i => sdm_branch m (l i)), (fun i => sdm_branch m (r i)); split.
- move=> i j ij; apply: prism_configuration_side_edge => //.
  + apply: prism_base_same_side; last by rewrite !lside.
    apply: contraNneq ij => /(congr1 val) e; apply/eqP/val_inj; exact: e.
  + by rewrite !lside.
- move=> i j ij; apply: prism_configuration_side_edge => //.
  + apply: prism_base_same_side; last by rewrite !rside.
    apply: contraNneq ij => /(congr1 val) e; apply/eqP/val_inj/eqP.
    by rewrite -(eqn_add2r 3); apply/eqP; exact: e.
  + by rewrite !rside.
- move=> i j; apply/eqP => /(@sdm_inj _ _ m) /(congr1 val) e.
  by have := lside i; rewrite e rside.
Qed.
