(** * GTMisc.conjectures.X314 -- v2 row: adding vertices of degree 1 keeps the zombie number (Bartier, Beneteau,
      Bonamy, La and Narboni, Question 4.1) *)

From GTBase Require Export base.
From GTMisc.foundations Require Import zombies.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** X314 helper ************************************************************ *)

(** [x314_pendant_extension G G']: G' is obtained from G by successively adding vertices of degree 1, up to
    isomorphism: G itself, or [add_node H [set v]] for a pendant extension H of G and a vertex v of H.
    [add_node H [set v]] is H with one new vertex adjacent to v only (coq-graph-theory), a vertex of degree 1
    ([g314_leaf_neighbours] in grounding_X314.v). *)
Inductive x314_pendant_extension (G : sgraph) : sgraph -> Prop :=
| x314_pendant_refl (G' : sgraph) : inhabited (diso G G') -> x314_pendant_extension G G'
| x314_pendant_step (H : sgraph) (v : H) (G' : sgraph) :
    x314_pendant_extension G H -> inhabited (diso (add_node H [set v]) G') ->
    x314_pendant_extension G G'.

(** ** X314 statement ********************************************************* *)

(** Corpus row: arxiv:2008.03587#00
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/2008.03587__00/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/2008.03587__00.json
    English statement: (Bartier, Beneteau, Bonamy, La and Narboni, "A note on deterministic zombies",
      arXiv:2008.03587, Question 4.1) For every graph G, and for a graph G' obtained from G by successively adding
      vertices of degree 1, does it always hold that z(G') = z(G)?  Here z(G) is the zombie number of the
      deterministic game of Zombies and Survivors of Fitzpatrick, Howell, Messinger and Pike (Discrete Applied
      Mathematics 213 (2016) 1-12): the minimum number of zombies that capture the survivor, the zombies choosing
      their vertices first and then, every round, each moving along a geodesic towards the survivor.
    Definitions: [connected [set: G]] - G is connected (coq-graph-theory); [x314_pendant_extension G G'] - G' is
      obtained from G by successively adding vertices of degree 1, up to isomorphism (this file; [add_node] and
      [diso] from coq-graph-theory); [zombie_number G k] - z(G) = k: k zombies win the game and fewer do not
      (graph-theory-misc foundations/zombies.v, where each rule is encoded and cited).
    Notes: the question is encoded as its affirmative answer, with z(G') and z(G) named by [zombie_number], which is
      functional and holds for exactly one k on every nonempty graph (between 1 and #|G|).  Both sources play on
      connected graphs (the record, main.tex l.182-184: "assume all graphs throughout the paper to be connected";
      FHMP16 l.94), hence the hypothesis [connected [set: G]]; adding vertices of degree 1 keeps G connected.  The
      hypothesis is needed: on two isolated vertices (z = 2) with a leaf added to one of them, z = 3, because a
      zombie with no geodesic to the survivor cannot move and freezes the play
      ([g314_R1_not_trivially_true] in grounding_X314.v).  The hypothesis 0 < #|G| (a vertex for the survivor) is
      the sources' standing assumption and not load-bearing: the empty graph's only pendant extension is itself.
      Status: open in its record (Question 4.1, main.tex l.420-423, with the reading at l.425-427: whether zombies
      gain by waiting at the start) and at the pin.  Line numbers are those of the deposited 2008.03587v3
      main.tex and of FHMP16's deposited paper.txt. *)
Definition zombie_number_pendant_vertices_statement : Prop :=
  forall G G' : sgraph,
    connected [set: G] -> 0 < #|G| ->
    x314_pendant_extension G G' ->
    forall z z' : nat, zombie_number G z -> zombie_number G' z' -> z' = z.
