(** * Extremal.foundations.edge_colourings -- edge colourings, colour classes,
      monochromatic copies and proper colourings.

    Shared vocabulary of the X215 (Ramsey), X223 (Ramsey-nice) and X229
    (rainbow-cycle) waves: all three quantify over colourings of the EDGE SET of
    a host graph and speak about the spanning subgraph carried by a set of
    colours.  Following the WP4b rule, a notion used by >= 2 waves of this
    package lives here rather than in a conjecture file.

    An edge colouring is modelled as a total map [col : {set G} -> C] on vertex
    sets; only its values on the two-element sets [ [set x; y] ] with [x -- y]
    (i.e. on [E(G)], see [sg_edge_set]) are ever read, so the totality is a
    convenience and not an extra hypothesis.

    Contents:
    - [colour_class col p]: the SPANNING subgraph of [G] keeping exactly the
      edges whose colour satisfies [p];
    - [edges_colour_class] / [card_edges_colour_class_split]: its edge set, and
      the fact that [p] and its complement split [E(G)] (the counting lemma the
      X215 Ramsey implication runs on);
    - [mono_copy F col c]: [F] embeds into the host by an injective
      adjacency-preserving map all of whose edges get colour [c], with
      [mono_copyP] identifying it with [has_subgraph] of the colour class;
    - [proper_ecolouring]: adjacent edges get distinct colours. *)

From GTBase Require Import base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section ColourClass.
Variables (G : sgraph) (C : eqType).
Variables (col : {set G} -> C) (p : pred C).

Definition cc_rel : rel G := [rel x y | (x -- y) && p (col [set x; y])].

Lemma cc_sym : symmetric cc_rel.
Proof. by move=> x y; rewrite /cc_rel /= sg_sym setUC. Qed.

Lemma cc_irrefl : irreflexive cc_rel.
Proof. by move=> x; rewrite /cc_rel /= sg_irrefl. Qed.

(** The spanning subgraph of [G] carrying exactly the [p]-coloured edges. *)
Definition colour_class : sgraph := SGraph cc_sym cc_irrefl.

Lemma colour_class_adj (x y : G) :
  @sedge colour_class x y = (x -- y) && p (col [set x; y]).
Proof. by []. Qed.

Lemma edges_colour_class : E(colour_class) = [set e in E(G) | p (col e)].
Proof.
apply/setP => e; rewrite inE; apply/idP/idP.
- case/edgesP => x [y [-> /andP[xy pc]]].
  by rewrite in_edges xy.
- case/andP => /edgesP[x [y [-> xy]]] pc.
  by apply/edgesP; exists x, y; split => //; apply/andP; split.
Qed.

End ColourClass.

Arguments colour_class [G C] col p.

Lemma card_edges_colour_class_split (G : sgraph) (C : eqType)
    (col : {set G} -> C) (p : pred C) :
  #|E(colour_class col p)| + #|E(colour_class col (predC p))| = #|E(G)|.
Proof.
rewrite !edges_colour_class.
have -> : [set e in E(G) | p (col e)] = E(G) :&: [set e | p (col e)].
  by apply/setP => e; rewrite !inE andbC.
have -> : [set e in E(G) | predC p (col e)] = E(G) :\: [set e | p (col e)].
  by apply/setP => e; rewrite !inE andbC.
exact: cardsID.
Qed.

(** ** Monochromatic copies *)

(** [F] has a copy inside the host graph all of whose edges have colour [c]:
    an injective map preserving adjacency (a not-necessarily-induced copy). *)
Definition mono_copy (Host F : sgraph) (C : eqType)
    (col : {set Host} -> C) (c : C) : Prop :=
  exists emb : F -> Host,
    [/\ injective emb,
        forall x y : F, x -- y -> emb x -- emb y &
        forall x y : F, x -- y -> col [set emb x; emb y] = c].

Arguments mono_copy [Host] F [C] col c.

Lemma mono_copyP (Host F : sgraph) (C : eqType) (col : {set Host} -> C) (c : C) :
  mono_copy F col c <-> has_subgraph (colour_class col (pred1 c)) F.
Proof.
split=> [[emb [inj hom mono]]|[emb inj hom]].
- exists emb => // x y xy _.
  apply/andP; split; first exact: (hom _ _ xy).
  by rewrite /= (mono _ _ xy) eqxx.
- have hom' : forall x y : F, x -- y ->
      @sedge (colour_class col (pred1 c)) (emb x) (emb y).
    move=> u v uv; apply: hom => //.
    by apply/eqP => /inj E; move: uv; rewrite E sg_irrefl.
  exists emb; split=> // u v uv.
  + by have /andP[] := hom' _ _ uv.
  + by have /andP[_ /eqP] := hom' _ _ uv.
Qed.

(** ** Proper edge colourings *)

(** Two edges sharing a vertex get distinct colours. *)
Definition proper_ecolouring (G : sgraph) (C : eqType) (col : {set G} -> C) : Prop :=
  forall x y z : G, x -- y -> x -- z -> y != z -> col [set x; y] != col [set x; z].

(** Specialisation to two colours: the true- and false-classes split [E(G)].
    This is the counting step of the Erdos-Sos => Burr-Erdos Ramsey reduction. *)
Lemma card_edges_bool_split (G : sgraph) (col : {set G} -> bool) :
  #|E(colour_class col (pred1 true))| + #|E(colour_class col (pred1 false))|
  = #|E(G)|.
Proof.
rewrite !edges_colour_class.
have -> : [set e in E(G) | pred1 true (col e)] = E(G) :&: [set e | col e].
  by apply/setP => e; rewrite !inE /= eqb_id.
have -> : [set e in E(G) | pred1 false (col e)] = E(G) :\: [set e | col e].
  by apply/setP => e; rewrite !inE /= eqbF_neg andbC.
exact: cardsID.
Qed.

(** Majority colour: in any 2-colouring one of the two classes carries at least
    half of the edges. *)
Lemma majority_colour (G : sgraph) (col : {set G} -> bool) :
  exists c : bool, #|E(G)| <= 2 * #|E(colour_class col (pred1 c))|.
Proof.
have H := card_edges_bool_split col.
case: (leqP #|E(colour_class col (pred1 false))|
            #|E(colour_class col (pred1 true))|) => Hle.
- by exists true; rewrite -H mul2n -addnn leq_add2l.
- by exists false; rewrite -H mul2n -addnn leq_add2r ltnW.
Qed.
