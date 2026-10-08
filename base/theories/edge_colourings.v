(** * Supplied proper edge colourings of simple graphs

    Library migration, batch C family "proper_edge_colouring"
    (meta/library_primitives/proper-edge-colouring.json).  Two supplied-map
    interfaces over an arbitrary [eqType] palette; both keep the supplied map
    and its labels, with no quotient by palette permutations and no
    surjectivity requirement.

    - SET MAPS [col : {set G} -> C]: only the values on the doubletons
      [[set x; y]] of actual edges are ever read.  [proper_edge_colouring col]
      is the endpoint form: two distinct edges [xy], [xz] at a common endpoint
      [x] get different colours.  [proper_edge_colouring_edgesP] and
      [proper_edge_colouring_meetP] are the two edge-pair presentations of the
      corpus (distinct edges with a nonempty intersection, resp. not disjoint,
      get different colours); [eq_proper_edge_colouring] shows that the values
      off [E(G)] are irrelevant.  The domain [{set G}] is inhabited even when
      [G] has no vertex, so NO total set map into an empty palette exists
      ([no_set_map_into_empty_palette]).
    - PAIR MAPS [col : G -> G -> C], symmetric on ALL ordered pairs, adjacent
      or not: [proper_pair_edge_colouring col] requires the global symmetry and
      different colours on two distinct neighbours of a vertex.  The domain
      [G * G] is empty exactly when [G] is empty: the empty graph admits every
      pair map, the unique one into an empty palette included
      ([proper_pair_edge_colouring_K0]); a nonempty edgeless graph admits no
      pair map into an empty palette ([no_pair_map_into_empty_palette]) and a
      single vertex is coloured by any one colour ([proper_pair_edge_colouring_K1]).
    - BRIDGE: [proper_edge_colouring_pairP] relates a set map [col] to the pair
      map [fun x y => col [set x; y]], symmetric since [[set x; y] = [set y; x]].
      A pair map is NOT converted back into a set map, and no map on the
      subtype of actual edges replaces either domain.
    - RELABELLING: composing with an injective palette map preserves and
      reflects properness ([proper_edge_colouring_relabel],
      [proper_pair_edge_colouring_relabel]); the supplied labels are kept.
    - GROUNDING: a constant colouring is proper on [K_2] (one edge) and improper
      on [K_3] (two edges at a vertex), in both interfaces.

    Upstream coq-graph-theory has no supplied proper-edge-colouring predicate;
    its [mgraph.line_graph] is directed and [GTBase.base.line_graph] lives on
    multigraph edge identities, so neither is used here.  This focused module
    has no conjecture import and no base re-export; consumers import it. *)

From mathcomp Require Import all_boot.
From GraphTheory Require Import digraph sgraph.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** The two interfaces *)

Definition proper_edge_colouring (G : sgraph) (C : eqType) (col : {set G} -> C) : Prop :=
  forall x y z : G, x -- y -> x -- z -> y != z -> col [set x; y] != col [set x; z].

Definition proper_pair_edge_colouring (G : sgraph) (C : eqType) (col : G -> G -> C) : Prop :=
  (forall u v : G, col u v = col v u) /\
  (forall u v w : G, u -- v -> u -- w -> v != w -> col u v != col u w).

(** ** Set maps *)

Section SetMaps.
Variables (G : sgraph) (C : eqType).
Implicit Types (col : {set G} -> C) (e f : {set G}) (x y z : G).

(** Two distinct edges that meet are two edges at a common endpoint. *)
Lemma edges_meet_endpoint e f :
  e \in E(G) -> f \in E(G) -> e != f -> e :&: f != set0 ->
  exists x y z, [/\ x -- y, x -- z, y != z, e = [set x; y] & f = [set x; z]].
Proof.
move=> /edgesP[a [b [-> ab]]] /edgesP[c [d [-> cd]]] ef /set0Pn[x].
rewrite !inE => /andP[/orP[/eqP xa|/eqP xb] /orP[/eqP xc|/eqP xd]].
- have ca : c = a by rewrite -xc xa.
  rewrite ca in cd ef *.
  by exists a, b, d; split=> //; apply: contraNneq ef => ->; rewrite eqxx.
- have da : d = a by rewrite -xd xa.
  rewrite da in cd ef *.
  exists a, b, c; split=> //; first by rewrite sg_sym.
  + by apply: contraNneq ef => ->; rewrite setUC eqxx.
  + by rewrite setUC.
- have cb : c = b by rewrite -xc xb.
  rewrite cb in cd ef *.
  exists b, a, d; split=> //; first by rewrite sg_sym.
  + by apply: contraNneq ef => ->; rewrite setUC eqxx.
  + by rewrite setUC.
- have db : d = b by rewrite -xd xb.
  rewrite db in cd ef *.
  exists b, a, c; split=> //; try by rewrite sg_sym.
  + by apply: contraNneq ef => ->; rewrite eqxx.
  + by rewrite setUC.
  + by rewrite setUC.
Qed.

(** The X142 presentation: distinct edges with a nonempty intersection get
    different colours. *)
Lemma proper_edge_colouring_edgesP col :
  proper_edge_colouring col <->
  forall e f, e \in E(G) -> f \in E(G) -> e != f -> e :&: f != set0 ->
    col e != col f.
Proof.
split=> [prop e f eG fG ef meet|prop x y z xy xz yz].
- have [x [y [z [xy xz yz -> ->]]]] := edges_meet_endpoint eG fG ef meet.
  exact: prop.
- apply: prop; rewrite ?in_edges //.
  + apply/eqP => /setP/(_ y); rewrite !inE eqxx orbT => /esym/orP[/eqP yx|/eqP yz'].
    * by move: xy; rewrite yx sg_irrefl.
    * by move: yz; rewrite yz' eqxx.
  + by apply/set0Pn; exists x; rewrite !inE eqxx.
Qed.

(** The X14 presentation: distinct edges that are not disjoint get different
    colours. *)
Lemma proper_edge_colouring_meetP col :
  proper_edge_colouring col <->
  forall e f, e \in E(G) -> f \in E(G) -> e != f -> ~~ [disjoint e & f] ->
    col e != col f.
Proof.
rewrite proper_edge_colouring_edgesP; split=> prop e f eG fG ef.
- by rewrite -setI_eq0 => meet; exact: prop.
- by rewrite setI_eq0 => meet; exact: prop.
Qed.

(** Values off the edge set are irrelevant. *)
Lemma eq_proper_edge_colouring col col' :
  {in E(G), col =1 col'} -> proper_edge_colouring col -> proper_edge_colouring col'.
Proof.
move=> eq prop x y z xy xz yz; rewrite -!eq ?in_edges //; exact: prop.
Qed.

(** Composing with a palette map reflects properness; an injective map also
    preserves it, keeping the supplied labels. *)
Lemma proper_edge_colouring_comp (D : eqType) (g : C -> D) col :
  proper_edge_colouring (g \o col) -> proper_edge_colouring col.
Proof.
by move=> prop x y z xy xz yz; apply: contraNneq (prop x y z xy xz yz) => /= ->.
Qed.

Lemma proper_edge_colouring_relabel (D : eqType) (g : C -> D) col :
  injective g ->
  proper_edge_colouring (g \o col) <-> proper_edge_colouring col.
Proof.
move=> inj; split; first exact: proper_edge_colouring_comp.
by move=> prop x y z xy xz yz; rewrite /= (inj_eq inj); exact: prop.
Qed.

(** No set map into an empty palette exists: the domain is inhabited. *)
Lemma no_set_map_into_empty_palette (col0 : {set G} -> 'I_0) : False.
Proof. by have := ltn_ord (col0 set0); rewrite ltn0. Qed.

End SetMaps.

(** ** Pair maps *)

Section PairMaps.
Variables (G : sgraph) (C : eqType).
Implicit Types (col : G -> G -> C) (u v w x y z : G).

Lemma proper_pair_edge_colouring_sym col :
  proper_pair_edge_colouring col -> forall u v, col u v = col v u.
Proof. by case. Qed.

Lemma proper_pair_edge_colouring_neighbours col :
  proper_pair_edge_colouring col ->
  forall u v w, u -- v -> u -- w -> v != w -> col u v != col u w.
Proof. by case. Qed.

Lemma proper_pair_edge_colouring_comp (D : eqType) (g : C -> D) col :
  proper_pair_edge_colouring (fun u v => g (col u v)) ->
  (forall u v, col u v = col v u) -> proper_pair_edge_colouring col.
Proof.
move=> [_ prop] sym; split=> // u v w uv uw vw.
by apply: contraNneq (prop u v w uv uw vw) => ->.
Qed.

Lemma proper_pair_edge_colouring_relabel (D : eqType) (g : C -> D) col :
  injective g ->
  proper_pair_edge_colouring (fun u v => g (col u v)) <->
  proper_pair_edge_colouring col.
Proof.
move=> inj; split=> -[sym prop]; split=> [u v|u v w uv uw vw].
- exact: inj (sym u v).
- by apply: contraNneq (prop u v w uv uw vw) => ->.
- by rewrite sym.
- by rewrite (inj_eq inj); exact: prop.
Qed.

End PairMaps.

(** ** The bridge from set maps to pair maps *)

Lemma proper_edge_colouring_pairP (G : sgraph) (C : eqType) (col : {set G} -> C) :
  proper_edge_colouring col <->
  proper_pair_edge_colouring (fun x y : G => col [set x; y]).
Proof.
split=> [prop|[_ prop]]; last exact: prop.
by split=> [u v|u v w uv uw vw]; [rewrite setUC | exact: prop].
Qed.

(** ** Grounding *)

Section Grounding.
Variable C : eqType.

(** One edge: any constant colouring of [K_2] is proper. *)
Lemma proper_edge_colouring_K2 (c : C) : proper_edge_colouring (fun _ : {set 'K_2} => c).
Proof.
move=> x y z xy xz yz; exfalso.
have yzT : [set y; z] = [set: 'K_2].
  by apply/eqP; rewrite eqEcard subsetT cardsT card_ord cards2 yz.
have : x \in [set y; z] by rewrite yzT inE.
rewrite !inE => /orP[/eqP xy'|/eqP xz'].
- by move: xy; rewrite xy' sg_irrefl.
- by move: xz; rewrite xz' sg_irrefl.
Qed.

Lemma proper_pair_edge_colouring_K2 (c : C) :
  proper_pair_edge_colouring (fun _ _ : 'K_2 => c).
Proof.
split=> // u v w uv uw vw; exfalso.
have vwT : [set v; w] = [set: 'K_2].
  by apply/eqP; rewrite eqEcard subsetT cardsT card_ord cards2 vw.
have : u \in [set v; w] by rewrite vwT inE.
rewrite !inE => /orP[/eqP uv'|/eqP uw'].
- by move: uv; rewrite uv' sg_irrefl.
- by move: uw; rewrite uw' sg_irrefl.
Qed.

(** Two edges at a vertex: no constant colouring of [K_3] is proper. *)
Lemma not_proper_edge_colouring_K3 (c : C) : ~ proper_edge_colouring (fun _ : {set 'K_3} => c).
Proof.
move=> /(_ ord0 (Ordinal (isT : 1 < 3)) (Ordinal (isT : 2 < 3)) isT isT isT).
by rewrite eqxx.
Qed.

Lemma not_proper_pair_edge_colouring_K3 (c : C) :
  ~ proper_pair_edge_colouring (fun _ _ : 'K_3 => c).
Proof.
move=> [_ /(_ ord0 (Ordinal (isT : 1 < 3)) (Ordinal (isT : 2 < 3)) isT isT isT)].
by rewrite eqxx.
Qed.

(** The empty graph: every pair map is proper, the one into an empty palette
    included (its domain is empty). *)
Lemma proper_pair_edge_colouring_K0 (D : eqType) (col : 'K_0 -> 'K_0 -> D) :
  proper_pair_edge_colouring col.
Proof. by split=> u; have := ltn_ord u; rewrite ltn0. Qed.

(** A nonempty graph, even edgeless, admits no pair map into an empty palette. *)
Lemma no_pair_map_into_empty_palette (G : sgraph) (x : G) (col0 : G -> G -> 'I_0) : False.
Proof. by have := ltn_ord (col0 x x); rewrite ltn0. Qed.

(** A single vertex is pair-coloured by any one colour (edgeless, so vacuous). *)
Lemma proper_pair_edge_colouring_K1 (c : C) :
  proper_pair_edge_colouring (fun _ _ : 'K_1 => c).
Proof. by split=> // u v w; rewrite (ord1 u) (ord1 v) sg_irrefl. Qed.

End Grounding.

(** ** Colour classes

    Library migration D12, family "edge-colour-class"
    (meta/library_primitives/edge-colour-class.json).  The shared colour-class
    contract of [Extremal.foundations.edge_colourings.colour_class], promoted
    under distinct names so that no file importing both modules rebinds a short
    name; that Extremal declaration is the same contract, and its public adapter
    is the next stage of this family.

    [edge_colour_class col p] is the SPANNING subgraph of [G] keeping exactly the
    edges whose colour satisfies [p]: the vertex type is that of [G] (isolated
    vertices stay) and [x -- y] holds iff [x -- y] in [G] and [p (col [set x; y])]
    ([edge_colour_classE]).  The palette [C] is an arbitrary [eqType], [col] a
    total set map on [{set G}], read only on actual edges
    ([eq_edge_colour_class]), and [p] any colour predicate; one colour [c] is
    [pred1 c].  Its edge set is [[set e in E(G) | p (col e)]]
    ([edges_edge_colour_class]); [p] and [predC p] split [E(G)]
    ([card_edges_edge_colour_class_split]); [predT] keeps every edge
    ([edge_colour_class_predT]), [pred0] none ([edges_edge_colour_class_pred0]);
    an edge lies in the class of its own colour and no other
    ([edges_edge_colour_class1]), so a constant colouring has one class
    ([edges_edge_colour_class_const]).  A simple graph on the same vertex type
    whose adjacency agrees pointwise with [edge_colour_class_rel col p] is
    isomorphic to [edge_colour_class col p] through the identity
    ([edge_colour_class_eq_diso], [edge_colour_class_eq_disoE]).  No guard: empty
    or edgeless hosts and unused colours are allowed, and no total set map into an
    empty palette exists ([no_set_map_into_empty_palette]). *)

(* The identity transports below compute through the bijection coercion. *)
From GraphTheory Require Import bij.

Section EdgeColourClass.
Variables (G : sgraph) (C : eqType) (col : {set G} -> C) (p : pred C).

Definition edge_colour_class_rel : rel G := [rel x y | (x -- y) && p (col [set x; y])].

Lemma edge_colour_class_sym : symmetric edge_colour_class_rel.
Proof. by move=> x y; rewrite /edge_colour_class_rel /= sg_sym setUC. Qed.

Lemma edge_colour_class_irrefl : irreflexive edge_colour_class_rel.
Proof. by move=> x; rewrite /edge_colour_class_rel /= sg_irrefl. Qed.

(** The spanning subgraph of [G] carrying exactly the [p]-coloured edges. *)
Definition edge_colour_class : sgraph :=
  SGraph edge_colour_class_sym edge_colour_class_irrefl.

Lemma edge_colour_classE (x y : G) :
  @edge_rel edge_colour_class x y = (x -- y) && p (col [set x; y]).
Proof. by []. Qed.

Lemma edges_edge_colour_class : E(edge_colour_class) = [set e in E(G) | p (col e)].
Proof.
apply/setP => e; rewrite inE; apply/idP/idP.
- case/edgesP => x [y [-> /andP[xy pc]]].
  by rewrite in_edges xy.
- case/andP => /edgesP[x [y [-> xy]]] pc.
  by apply/edgesP; exists x, y; split => //; apply/andP; split.
Qed.

(** Same-carrier transport through the identity (transparent, so the map
    computes: [edge_colour_class_eq_disoE]). *)
Lemma edge_colour_class_eq_diso (r : rel G) (r_sym : symmetric r) (r_irrefl : irreflexive r) :
  r =2 edge_colour_class_rel -> diso (SGraph r_sym r_irrefl) edge_colour_class.
Proof. by move=> rE; apply: eq_diso. Defined.

Lemma edge_colour_class_eq_disoE (r : rel G) (r_sym : symmetric r) (r_irrefl : irreflexive r)
    (rE : r =2 edge_colour_class_rel) (v : G) :
  edge_colour_class_eq_diso r_sym r_irrefl rE v = v.
Proof. by []. Qed.

End EdgeColourClass.

Arguments edge_colour_class_rel [G C] col p _ _.
Arguments edge_colour_class [G C] col p.

(** Values off the edge set are irrelevant: two colourings (over any palettes)
    whose predicates agree on the actual edges give the same adjacency, hence
    identity-isomorphic classes. *)
Lemma eq_edge_colour_class_rel (G : sgraph) (C D : eqType)
    (col : {set G} -> C) (p : pred C) (col' : {set G} -> D) (p' : pred D) :
  {in E(G), forall e, p (col e) = p' (col' e)} ->
  edge_colour_class_rel col p =2 edge_colour_class_rel col' p'.
Proof.
move=> eqE x y; rewrite /edge_colour_class_rel /=.
by case xy: (x -- y) => //=; rewrite eqE // in_edges.
Qed.

Lemma eq_edge_colour_class (G : sgraph) (C D : eqType)
    (col : {set G} -> C) (p : pred C) (col' : {set G} -> D) (p' : pred D) :
  {in E(G), forall e, p (col e) = p' (col' e)} ->
  edge_colour_class col p ≃ edge_colour_class col' p'.
Proof. by move=> eqE; apply: eq_diso; exact: eq_edge_colour_class_rel. Defined.

(** [p] and its complement split the edge set. *)
Lemma card_edges_edge_colour_class_split (G : sgraph) (C : eqType)
    (col : {set G} -> C) (p : pred C) :
  #|E(edge_colour_class col p)| + #|E(edge_colour_class col (predC p))| = #|E(G)|.
Proof.
rewrite !edges_edge_colour_class.
have -> : [set e in E(G) | p (col e)] = E(G) :&: [set e | p (col e)].
  by apply/setP => e; rewrite !inE andbC.
have -> : [set e in E(G) | predC p (col e)] = E(G) :\: [set e | p (col e)].
  by apply/setP => e; rewrite !inE andbC.
exact: cardsID.
Qed.

(** Corners: [predT] keeps the host, [pred0] keeps no edge. *)
Lemma edge_colour_class_predT (G : sgraph) (C : eqType) (col : {set G} -> C) :
  edge_colour_class col predT ≃ G.
Proof.
apply: (@Diso' (edge_colour_class col predT) G id id) => // x y.
by rewrite edge_colour_classE /= andbT.
Defined.

Lemma edges_edge_colour_class_pred0 (G : sgraph) (C : eqType) (col : {set G} -> C) :
  E(edge_colour_class col pred0) = set0.
Proof. by apply/setP => e; rewrite edges_edge_colour_class !inE andbF. Qed.

(** An edge lies in the class of its own colour and in no other. *)
Lemma edges_edge_colour_class1 (G : sgraph) (C : eqType) (col : {set G} -> C) (c : C)
    (e : {set G}) :
  e \in E(G) -> (e \in E(edge_colour_class col (pred1 c))) = (col e == c).
Proof. by move=> eG; rewrite edges_edge_colour_class inE eG. Qed.

(** A constant colouring has a single nonempty class. *)
Lemma edges_edge_colour_class_const (G : sgraph) (C : eqType) (c d : C) :
  E(edge_colour_class (fun _ : {set G} => c) (pred1 d)) = if c == d then E(G) else set0.
Proof.
apply/setP => e; rewrite edges_edge_colour_class !inE /=.
by case: (c == d); rewrite ?andbT ?andbF ?inE.
Qed.
