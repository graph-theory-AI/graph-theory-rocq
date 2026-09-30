(** * Topological.conjectures.D3D6_unblocked -- legacy blocked OPG rows *)

From GTBase Require Export base.
From GraphTheory Require Import minor.
From Topological.foundations Require Import crossing.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Record great_circle_arrangement := GreatCircleArrangement {
  gca_graph : sgraph;
  gca_general_position : Prop
}.

(** Corpus row: opg:3_colourability_of_arrangements_of_great_circles
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/3_colourability_of_arrangements_of_great_circles/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/3_colourability_of_arrangements_of_great_circles.json
    English statement: (Open Problem Garden, "3-Colourability of Arrangements of Great Circles")
      Corpus claim: every arrangement graph of a set of great circles on a sphere, no three
      of which meet at a common point, is 3-colourable (such an arrangement graph has one
      vertex per intersection point and one edge per arc joining two consecutive
      intersection points, hence is 4-regular and planar).  Back-translation of the Rocq
      body: for every pair made of a finite simple graph G and an arbitrary proposition P
      (the two fields of the record [great_circle_arrangement]), if P holds then the
      chromatic number of G is at most 3.
    Definitions: [great_circle_arrangement] - a record packing a graph [gca_graph : sgraph]
      with a FREE, uninterpreted proposition [gca_general_position : Prop] (this file);
      the chromatic number is coq-graph-theory's subset-relative [chi(A)] on the full
      vertex set.
    Notes: PROXY, and a degenerate one - the file header calls these five rows legacy
      blocked OPG rows.  Nothing of the geometry is encoded: no sphere, no circles, no
      arrangement, and the "no three circles concurrent" hypothesis is an uninterpreted
      [Prop] field, so the 4-regular planar arrangement-graph class is not captured.  As
      written the statement is classically FALSE (instantiate the record with
      [gca_graph := 'K_4] and [gca_general_position := True]).  A faithful encoding needs a
      sphere/arrangement layer above the straight-line geometry of
      topological-graph-theory/theories/foundations/geometry.v. *)
Definition three_colourability_of_arrangements_of_great_circles_statement : Prop :=
  forall A : great_circle_arrangement,
    gca_general_position A -> χ([set: gca_graph A]) <= 3.

Record pair_crossing_drawing (G : sgraph) (n : nat) := PairCrossingDrawing {
  pcd_crossing_pairs : nat;
  pcd_count : pcd_crossing_pairs = n
}.

Definition pair_crossing_number (G : sgraph) (n : nat) : Prop :=
  exists _ : pair_crossing_drawing G n, True.

(** Corpus row: opg:are_different_notions_of_the_crossing_number_the_same
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/are_different_notions_of_the_crossing_number_the_same/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/are_different_notions_of_the_crossing_number_the_same.json
    English statement: (Open Problem Garden, "Are different notions of the crossing number
      the same?")
      Corpus claim: does pair-cr(G) = cr(G) hold for every graph G, where cr(G) is the least
      number of edge crossings over all drawings of G in the plane and pair-cr(G) is the
      least number of CROSSING PAIRS of edges over all such drawings?  Back-translation of
      the Rocq body: for every finite simple graph G and all naturals m and n, if m is a
      pairwise crossing number of G and n is the split-planarization crossing number of G,
      then m = n.
    Definitions: [pair_crossing_number G n] - placeholder predicate: some record
      [pair_crossing_drawing G n] exists, whose only content is a natural
      [pcd_crossing_pairs] together with a proof that it equals n (this file);
      [is_crossing_number G n] - n crossing splits planarize G and no fewer do
      (topological-graph-theory/theories/foundations/crossing.v).
    Notes: PROXY/placeholder, refutable as written.  [pair_crossing_drawing G n] is
      inhabited for EVERY G and EVERY n (take [pcd_crossing_pairs := n]), so
      [pair_crossing_number G m] holds for all m; taking a planar G, for which
      [is_crossing_number G 0] holds, the body forces m = 0 for every m.  Neither drawings
      nor the pairing of crossings are modelled.  The right-hand side is the
      split-planarization proxy of crossing.v, which itself still lacks the local
      rotation/alternation data at crossing vertices needed for equality with the drawing
      crossing number. *)
Definition are_different_notions_of_the_crossing_number_the_sam_statement : Prop :=
  forall (G : sgraph) (m n : nat),
    pair_crossing_number G m -> is_crossing_number G n -> m = n.

Record surface_drawing (G : sgraph) := SurfaceDrawing {
  sd_crossings : nat;
  sd_component_image : {set G} -> nat -> Prop
}.

Definition disjoint_union_sides (G : sgraph) (A B : {set G}) : Prop :=
  A :&: B = set0 /\ A :|: B = [set: G].

Definition optimal_surface_drawing
    (G : sgraph) (surface : nat) (D : surface_drawing G) : Prop :=
  surface_embeddable surface G /\
  forall D' : surface_drawing G, sd_crossings D <= sd_crossings D'.

Definition drawing_components_disjoint
    (G : sgraph) (A B : {set G}) (D : surface_drawing G) : Prop :=
  forall i : nat, ~(sd_component_image D A i /\ sd_component_image D B i).

(** Corpus row: opg:drawing_disconnected_graphs_on_surfaces
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/drawing_disconnected_graphs_on_surfaces/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/drawing_disconnected_graphs_on_surfaces.json
    English statement: (Open Problem Garden, "Drawing disconnected graphs on surfaces")
      Corpus claim: if G is the disjoint union of two graphs G1 and G2 and Sigma is a
      surface, is it true that in every optimal (crossing-minimal) drawing of G on Sigma the
      images of G1 and G2 are disjoint?  Back-translation of the Rocq body: for every finite
      simple graph G, every two vertex sets A and B partitioning the vertices of G, every
      natural [surface] and every record D of type [surface_drawing G], if D is an optimal
      surface drawing then no index i is claimed by both A and B under D's component-image
      field.
    Definitions: [surface_drawing G] - a record with a FREE crossing count
      [sd_crossings : nat] and a FREE relation [sd_component_image : {set G} -> nat -> Prop]
      (this file); [disjoint_union_sides A B] - A and B are disjoint and cover every vertex
      (this file); [optimal_surface_drawing surface D] - G embeds in the surface of Euler
      genus at most [surface] and D minimises [sd_crossings] among all such records (this
      file, on top of [surface_embeddable], base/theories/surface.v);
      [drawing_components_disjoint A B D] - no i with both [sd_component_image D A i] and
      [sd_component_image D B i] (this file).
    Notes: PROXY, refutable as written.  Both fields of [surface_drawing] are free: choosing
      [sd_crossings := 0] (hence optimal) and [sd_component_image := fun _ _ => True] makes
      the hypothesis hold and the conclusion fail, so the statement is classically false.
      Moreover "disjoint union of G1 and G2" is weakened to an arbitrary vertex bipartition
      (A and B need not be unions of connected components and need not be edgeless to each
      other), and the surface is only a natural number bounding the Euler genus of the
      rotation-system layer of base/theories/surface.v - there is no drawing, no crossing,
      no image of a subgraph.
      V counts every vertex including isolated ones (base fix 2026-09-23): the old count saw
      only the vertices carrying a dart, so the Euler count overstated the genus of every
      graph with an isolated vertex and this hypothesis admitted fewer graphs than intended. *)
Definition drawing_disconnected_graphs_on_surfaces_statement : Prop :=
  forall (G : sgraph) (A B : {set G}) (surface : nat) (D : surface_drawing G),
    disjoint_union_sides A B ->
    optimal_surface_drawing surface D ->
    drawing_components_disjoint A B D.

Record obstacle_representation (G : sgraph) (k : nat) := ObstacleRepresentation {
  obstacle_points : G -> nat * nat;
  obstacle_index : finType;
  obstacle_count : #|{: obstacle_index}| <= k;
  obstacle_visibility :
    forall x y : G, x != y -> (x -- y) \/ ~ (x -- y)
}.

Definition obstacle_number_at_most (G : sgraph) (k : nat) : Prop :=
  exists _ : obstacle_representation G k, True.

Definition obstacle_number_greater_than_one (G : sgraph) : Prop :=
  ~ obstacle_number_at_most G 1.

(** Corpus row: opg:obstacle_number_of_planar_graphs
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/obstacle_number_of_planar_graphs/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/obstacle_number_of_planar_graphs.json
    English statement: (Open Problem Garden, "Obstacle number of planar graphs")
      Corpus claim: does there exist a planar graph of obstacle number greater than 1, and is
      there a k such that every planar graph has obstacle number at most k?  (The obstacle
      number of G is the least number of polygonal obstacles in the plane admitting a
      placement of the vertices whose visibility graph is exactly G.)  Back-translation of
      the Rocq body: the conjunction of (a) there exists a finite simple graph G with no K5
      and no K3,3 minor such that G has no obstacle representation with at most 1 obstacle,
      and (b) there exists a k such that every such graph has an obstacle representation with
      at most k obstacles.
    Definitions: [obstacle_representation G k] - a record with a point placement
      [obstacle_points : G -> nat * nat], a finite index type of cardinality at most k, and a
      "visibility" field asserting only [forall x y, x != y -> (x -- y) \/ ~ (x -- y)] (this
      file); [obstacle_number_at_most], [obstacle_number_greater_than_one] - derived from it
      (this file); [wagner_planar] - no K5 and no K3,3 minor, i.e. planarity by Wagner's
      theorem (base/theories/base.v).
    Notes: PROXY, refutable as written.  The visibility field is a TAUTOLOGY (excluded middle
      on a decidable adjacency), and the index type only has to be small, so
      [obstacle_representation G k] is inhabited for every G and every k (including k = 1,
      via 'I_1).  Hence clause (a) is false and the whole statement is classically false.
      No obstacles, no segments, no visibility are modelled; the integer-coordinate placement
      is never constrained.  A faithful version needs the straight-line/segment layer of
      topological-graph-theory/theories/foundations/geometry.v extended with polygonal
      obstacles. *)
Definition obstacle_number_of_planar_graphs_statement : Prop :=
  (exists G : sgraph, wagner_planar G /\ obstacle_number_greater_than_one G) /\
  (exists k : nat, forall G : sgraph, wagner_planar G -> obstacle_number_at_most G k).

Record nonorientable_embedding (G : sgraph) (g : nat) := NonorientableEmbedding {
  noe_scheme : nat;
  noe_genus_bound : noe_scheme <= g
}.

Definition embeds_nonorientable (G : sgraph) (g : nat) : Prop :=
  exists _ : nonorientable_embedding G g, True.

Definition proper_minor (G H : sgraph) : Prop :=
  minor G H /\ #|H| < #|G|.

Definition minor_minimal_nonorientable_obstruction (G : sgraph) (g : nat) : Prop :=
  ~ embeds_nonorientable G g /\
  forall H : sgraph, proper_minor G H -> embeds_nonorientable H g.

(** Corpus row: opg:consecutive_non_orientable_embedding_obstructions
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/consecutive_non_orientable_embedding_obstructions/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/consecutive_non_orientable_embedding_obstructions.json
    English statement: (Open Problem Garden, "Consecutive non-orientable embedding
      obstructions")
      Corpus claim: is there a graph G that is a minor-minimal obstruction for two
      (consecutive) non-orientable surfaces?  Back-translation of the Rocq body: there exist
      a finite simple graph G and a natural g such that G is a minor-minimal obstruction for
      the non-orientable surface of parameter g and also for the one of parameter g+1, where
      "minor-minimal obstruction for g" means G does not embed in g while every proper minor
      of G does.
    Definitions: [nonorientable_embedding G g] - a record with a FREE natural [noe_scheme]
      and a proof that it is at most g (this file); [embeds_nonorientable G g] - that record
      is inhabited (this file); [proper_minor G H] - H is a minor of G with strictly fewer
      vertices (this file, on coq-graph-theory's [minor]);
      [minor_minimal_nonorientable_obstruction] - built from the two above (this file).
    Notes: PROXY, vacuous/refutable as written.  [nonorientable_embedding G g] is inhabited
      for every G and g (take [noe_scheme := 0]), so [embeds_nonorientable] is universally
      true and no graph can satisfy its negation: the statement is classically FALSE for
      reasons unrelated to the mathematics.  Non-orientable embeddability is not modelled at
      all here; the signed-rotation layer that could carry it is
      topological-graph-theory/theories/foundations/signed_embedding.v ([semb_in_genus]),
      which is itself flagged there as NOT being "embeds in the non-orientable surface N_k".
      Also note the encoding uses "proper minor" by vertex count, which is weaker than the
      usual proper-minor relation (edge deletions do not change the vertex count). *)
Definition consecutive_non_orientable_embedding_obstructions_statement : Prop :=
  exists (G : sgraph) (g : nat),
    minor_minimal_nonorientable_obstruction G g /\
    minor_minimal_nonorientable_obstruction G g.+1.

