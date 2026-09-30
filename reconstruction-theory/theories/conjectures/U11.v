(** * Reconstruction.conjectures.U11 — milestone U11 (namespace Reconstruction, plan v4)

    Statement-only formalizations (axiom-free: no Conjecture/Axiom/Parameter/
    Admitted) of four central OPEN problems of reconstruction theory:

      Row 1  Switching (Seidel) reconstruction — Stanley's Conjecture:
             "Every simple graph on five or more vertices is
              switching-reconstructible."
      Row 2  Edge reconstruction — Harary's Conjecture:
             "Every simple graph with at least 4 edges is reconstructible from
              its edge deleted subgraphs."
      Row 3  Graham's tree-reconstruction Problem:
             "Given that G is a tree, can we determine it from the integer
              sequence |V(G)|, |V(L(G))|, |V(L(L(G)))|, … ?"
      Row 4  The Reconstruction (Kelly–Ulam) Conjecture:
             "If two graphs on ≥ 3 vertices have the same deck, then they are
              isomorphic."

    CARRIER TYPE.  Every row lives on SIMPLE undirected graphs, carrier
    [sgraph]; adjacency [x -- y].  Row 3 additionally needs an iterable line-map
    [sgraph -> sgraph] (so it can be iterated by [iter]); coq-graph-theory /
    base ship a line graph only on the multigraph surface ([mgraph -> sgraph],
    not iterable), so this milestone defines its OWN simple-graph line operation
    [sline_graph : sgraph -> sgraph] (vertices = the edges of [G], two edges
    adjacent iff distinct and sharing an endpoint).  No multigraph / digraph
    surface is otherwise needed.

    CORE undirected vocabulary comes from graph-theory-base (GTBase.base), which
    re-exports the coq-graph-theory layer: [sgraph], [x -- y], [sg_sym],
    [sg_irrefl], [SGraph] (the sgraph constructor from a symmetric irreflexive
    relation), [induced] (induced subgraph on a vertex set), [E(G)] (the edge
    set [sg_edge_set]), [is_tree] (= [is_forest] ∧ [connected]) and
    [F ≃ G] = [diso] (simple-graph isomorphism, valued in Type — wrapped in
    [inhabited] to land in Prop).  These are REUSED verbatim; nothing from base
    is redefined.

    PRIMITIVES introduced here.  These split into two kinds.

    (a) GENERIC simple-graph operations — absent from base TODAY but broadly
        reusable across areas, hence each is tagged [@MOVE-to-base] so it
        migrates to GTBase.base when a 2nd area needs it (the project
        convention).  None is a redefinition of a base primitive:
      - [vertex_switch G S] / [switch_vertex G v] : the Seidel switch of [G]
        w.r.t. a vertex set [S] (toggle edges between [S] and its complement) /
        the single-vertex switch at [v].  No [switch]/[Seidel] operation exists
        in base (checked via Locate/Search).
      - [sdel_edge G e] : [G] with the undirected edge [e : {set G}] removed
        (same vertices, drop the single adjacency whose endpoint set is [e]).
        NOTE: base re-exports [GraphTheory.core.digraph.del_edge :
        forall (G : diGraph), G -> G -> diGraph], which deletes a single
        DIRECTED arc [a -> b] and returns a [diGraph] (not symmetric, not an
        [sgraph], indexed by an endpoint PAIR not an edge set).  It is therefore
        UNSUITABLE for set-indexed undirected edge deletion; we define a
        distinct simple-graph operation under a non-colliding name [sdel_edge].
      - [sline_graph] : the iterable simple-graph line operation
        [sgraph -> sgraph] (vertices = edges of [G], adjacency = distinct edges
        sharing an endpoint).  base ships only [line_graph : mgraph -> sgraph]
        (multigraph surface, not iterable as [sgraph -> sgraph]); [sline_graph]
        is the iterable simple-graph counterpart, NOT a redefinition.

    (b) RECONSTRUCTION-SPECIFIC predicates (truly area-only, not migration
        candidates):
      - [switching_deck] family [v ↦ switch_vertex G v]; [same_switching_deck]
        / [switching_reconstructible] (Row 1).
      - [same_edge_deck] / [edge_reconstructible] over the edge index type
        [{e | e ∈ E(G)}] (Row 2).
      - [vdel_card G v] : the vertex-deleted card [G − v] (induced subgraph on
        [{u | u ≠ v}]); [same_deck] / [reconstructible] (Row 4).

    DECK-EQUALITY MODEL.  A deck is a MULTISET of cards indexed by the deleted
    object (a vertex, or an edge).  Two graphs have "the same deck" exactly when
    there is a BIJECTION between their index sets matching corresponding cards up
    to isomorphism — the standard multiset-up-to-iso reading.  (The bijection
    forces equal index-set sizes, hence equal vertex / edge counts.)  This is the
    shared shape of [same_switching_deck], [same_edge_deck] and [same_deck].

    ISOMORPHISM.  Throughout, "[G] is isomorphic to [H]" is [inhabited (G ≃ H)]
    ([≃] = [diso] is Type-valued; [inhabited] lifts it to Prop). *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ============================================================================
    Custom simple-graph constructions (area-specific surface).
    ========================================================================== *)

(** *** Seidel switch w.r.t. a vertex set [S]: toggle exactly the edges between
    [S] and its complement (edges with exactly one endpoint in [S]).  Symmetric
    and irreflexive, hence a genuine [sgraph].

    [@MOVE-to-base] generic Seidel-switch operation; migrate to GTBase.base when
    a 2nd area needs it. *)
Section Switch.
Variables (G : sgraph) (S : {set G}).
Definition sw_rel : rel G := fun x y => (x -- y) (+) ((x \in S) (+) (y \in S)).
Lemma sw_sym : symmetric sw_rel.
Proof. by move=> x y; rewrite /sw_rel sg_sym [(x \in S) (+) _]addbC. Qed.
Lemma sw_irrefl : irreflexive sw_rel.
Proof. by move=> x; rewrite /sw_rel sg_irrefl addbb. Qed.
Definition vertex_switch : sgraph := SGraph sw_sym sw_irrefl.
End Switch.

(** Single-vertex switching: the Seidel switch w.r.t. the singleton [[set v]]
    (toggle all edges incident to [v]). *)
Definition switch_vertex (G : sgraph) (v : G) : sgraph := vertex_switch [set v].

(** *** Undirected edge deletion: [G] with the edge [e : {set G}] removed (same
    vertices, drop the single adjacency whose endpoint set is [e]).  Named
    [sdel_edge] to avoid colliding with base's directed-arc [del_edge :
    diGraph -> _ -> _ -> diGraph] (a different, unsuitable operation).

    [@MOVE-to-base] generic simple-graph edge deletion; migrate to GTBase.base
    when a 2nd area needs it. *)
Section DelEdge.
Variables (G : sgraph) (e : {set G}).
Definition sde_rel : rel G := fun x y => (x -- y) && ([set x; y] != e).
Lemma sde_sym : symmetric sde_rel.
Proof. by move=> x y; rewrite /sde_rel sg_sym setUC. Qed.
Lemma sde_irrefl : irreflexive sde_rel.
Proof. by move=> x; rewrite /sde_rel sg_irrefl. Qed.
Definition sdel_edge : sgraph := SGraph sde_sym sde_irrefl.
End DelEdge.

(** *** Simple-graph line operation [L(G)] (iterable [sgraph -> sgraph]):
    vertices are the edges of [G] (the sig-type over [E(G)]); two edges are
    adjacent iff they are distinct and share an endpoint (their endpoint sets
    meet).  This is the iterable simple-graph counterpart of base's multigraph
    [line_graph : mgraph -> sgraph], NOT a redefinition of it.

    [@MOVE-to-base] generic simple-graph line operation; migrate to GTBase.base
    when a 2nd area needs it. *)
Section SLine.
Variable G : sgraph.
Definition sline_rel : rel {e : {set G} | e \in E(G)} :=
  fun e1 e2 => (val e1 != val e2) && (val e1 :&: val e2 != set0).
Lemma sline_sym : symmetric sline_rel.
Proof. by move=> e1 e2; rewrite /sline_rel eq_sym setIC. Qed.
Lemma sline_irrefl : irreflexive sline_rel.
Proof. by move=> e; rewrite /sline_rel eqxx. Qed.
Definition sline_graph : sgraph := SGraph sline_sym sline_irrefl.
End SLine.

(** *** Vertex-deleted card [G − v]: the induced subgraph on [{u | u ≠ v}]. *)
Definition vdel_card (G : sgraph) (v : G) : sgraph := induced [set u : G | u != v].

(** ============================================================================
    Row 1 — Switching (Seidel) reconstruction (Stanley) — OPEN.

    Source: "Every simple graph on five or more vertices is
    switching-reconstructible."

    The switching deck of [G] is the multiset [{ switch_vertex G v : v ∈ V(G) }].
    Two graphs have the SAME switching deck iff some vertex bijection matches
    their single-vertex switches up to isomorphism.  [G] is
    switching-reconstructible iff every [H] with the same switching deck is
    isomorphic to [G].
    ========================================================================== *)

Definition same_switching_deck (G H : sgraph) : Prop :=
  exists f : G -> H,
    bijective f /\
    forall v : G, inhabited (@switch_vertex G v ≃ @switch_vertex H (f v)).

Definition switching_reconstructible (G : sgraph) : Prop :=
  forall H : sgraph, same_switching_deck G H -> inhabited (G ≃ H).

(** Corpus row: opg:switching_reconstruction_conjecture
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/switching_reconstruction_conjecture/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/switching_reconstruction_conjecture.json
    English statement: (OPG "Switching reconstruction conjecture", attributed to Stanley)
      For every simple graph G on at least five vertices and every simple graph H: if there
      is a bijection f from the vertices of G to the vertices of H such that, for every
      vertex v of G, the Seidel switch of G at v is isomorphic to the Seidel switch of H at
      f(v), then G and H are isomorphic.
    Definitions: [switch_vertex G v] — the Seidel switch of G at the single vertex v: every
      pair containing v is toggled (a neighbour of v becomes a non-neighbour and conversely)
      and all other adjacencies are kept (U11.v, built from [vertex_switch G S], the Seidel
      switch with respect to a vertex set S, which toggles the pairs with exactly one
      endpoint in S); [same_switching_deck G H] — some vertex bijection f matches the two
      switching decks card by card up to isomorphism (U11.v);
      [switching_reconstructible G] — every H with the same switching deck is isomorphic to
      G (U11.v); [sgraph], [diso] written [F ≃ G] are coq-graph-theory, re-exported by
      GTBase (base/theories/base.v).
    Notes: a deck is modelled as a family of cards indexed by the deleted object, and having
      the same deck as a bijection of the index sets matching corresponding cards up to
      isomorphism (the standard multiset-up-to-isomorphism reading; the bijection forces
      equal vertex counts). Isomorphism [≃] is Type-valued, so it is wrapped in [inhabited]
      to land in Prop. Neither GTBase nor coq-graph-theory ships a Seidel switch, hence the
      local [vertex_switch] (tagged @MOVE-to-base in this file). *)
Definition switching_reconstruction_statement : Prop :=
  forall G : sgraph, (5 <= #|G|)%N -> switching_reconstructible G.

(** ============================================================================
    Row 2 — Edge reconstruction (Harary) — OPEN.

    Source: "Every simple graph with at least 4 edges is reconstructible from
    its edge deleted subgraphs."

    The edge deck of [G] is the multiset [{ sdel_edge G e : e ∈ E(G) }], indexed
    by the edge sig-type [{e | e ∈ E(G)}].  Two graphs have the SAME edge deck
    iff some bijection between their edge sets matches the edge-deleted cards up
    to isomorphism.  [G] is edge-reconstructible iff every [H] with the same edge
    deck is isomorphic to [G].
    ========================================================================== *)

Definition same_edge_deck (G H : sgraph) : Prop :=
  exists f : {e : {set G} | e \in E(G)} -> {e : {set H} | e \in E(H)},
    bijective f /\
    forall e : {e : {set G} | e \in E(G)},
      inhabited (@sdel_edge G (val e) ≃ @sdel_edge H (val (f e))).

Definition edge_reconstructible (G : sgraph) : Prop :=
  forall H : sgraph, same_edge_deck G H -> inhabited (G ≃ H).

(** Corpus row: opg:edge_reconstruction_conjecture
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/edge_reconstruction_conjecture/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/edge_reconstruction_conjecture.json
    English statement: (OPG "Edge Reconstruction Conjecture", Harary)
      For every simple graph G with at least four edges and every simple graph H: if there
      is a bijection f from the edges of G to the edges of H such that, for every edge e of
      G, the graph obtained from G by deleting e is isomorphic to the graph obtained from H
      by deleting f(e), then G and H are isomorphic.
    Definitions: [sdel_edge G e] — the graph on the vertices of G with the single undirected
      edge e (given as its two-element endpoint set) removed and every other adjacency kept
      (U11.v; named apart from coq-graph-theory's [del_edge], which deletes a directed arc
      and returns a diGraph, so it is unusable here); [same_edge_deck G H] — some bijection
      between the edge sig-types matches the edge-deleted cards up to isomorphism (U11.v);
      [edge_reconstructible G] — every H with the same edge deck is isomorphic to G (U11.v);
      [E(G)] — the edge set [sg_edge_set] of a simple graph (coq-graph-theory).
    Notes: same deck model as the vertex-deleted case (a bijection of index sets, cards
      compared up to isomorphism), here indexed by the edge sig-type
      [{e : {set G} | e \in E(G)}], so the bijection forces G and H to have equally many
      edges. The four-edge guard is stated on G only; H inherits it through the bijection. *)
Definition edge_reconstruction_statement : Prop :=
  forall G : sgraph, (4 <= #|E(G)|)%N -> edge_reconstructible G.

(** ============================================================================
    Row 3 — Graham's tree-reconstruction Problem — OPEN.
    ========================================================================== *)

(** Corpus row: opg:grahams_conjecture_on_tree_reconstruction
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/grahams_conjecture_on_tree_reconstruction/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/grahams_conjecture_on_tree_reconstruction.json
    English statement: (OPG "Graham's conjecture on tree reconstruction", Graham)
      Write L for the line-graph operation. For any two trees T1 and T2: if for every
      natural number i the i-th iterate of L applied to T1 has the same number of vertices
      as the i-th iterate of L applied to T2 (i = 0 giving the vertex counts of T1 and T2
      themselves), then T1 and T2 are isomorphic.
    Definitions: [sline_graph G] — the simple-graph line operation, of type
      [sgraph -> sgraph]: its vertices are the edges of G, and two of them are adjacent when
      they are distinct and their endpoint sets meet (U11.v; GTBase ships only
      [line_graph : mgraph -> sgraph], which cannot be iterated on simple graphs, so this is
      a counterpart and not a redefinition); [is_tree [set: T]] — T is a connected forest
      (coq-graph-theory); [iter i f x] and the cardinality [#|_|] are MathComp.
    Notes: the corpus row is a Problem — given that G is a tree, can we determine it from
      the integer sequence |V(G)|, |V(L(G))|, |V(L(L(G)))|, ... ? It is formalized here as
      the affirmative proposition that the whole sequence determines the tree up to
      isomorphism. The sequence is indexed from i = 0 and equality is demanded at every
      index, which is the literal reading of "the integer sequence". *)

Definition grahams_conjecture_on_tree_reconstruction_statement : Prop :=
  forall T1 T2 : sgraph,
    is_tree [set: T1] -> is_tree [set: T2] ->
    (forall i : nat, #|iter i sline_graph T1| = #|iter i sline_graph T2|) ->
    inhabited (T1 ≃ T2).

(** ============================================================================
    Row 4 — The Reconstruction (Kelly–Ulam) Conjecture — OPEN.

    Source: "The deck of a graph G is the multiset consisting of all unlabelled
    subgraphs obtained from G by deleting a vertex in all possible ways (counted
    according to multiplicity).  Conjecture: If two graphs on ≥ 3 vertices have
    the same deck, then they are isomorphic."

    The deck of [G] is the multiset [{ vdel_card G v : v ∈ V(G) }].  Two graphs
    have the SAME deck iff some vertex bijection matches their vertex-deleted
    cards up to isomorphism.
    ========================================================================== *)

Definition same_deck (G H : sgraph) : Prop :=
  exists f : G -> H,
    bijective f /\
    forall v : G, inhabited (@vdel_card G v ≃ @vdel_card H (f v)).

Definition reconstructible (G : sgraph) : Prop :=
  forall H : sgraph, same_deck G H -> inhabited (G ≃ H).

(** Corpus row: opg:reconstruction_conjecture
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/reconstruction_conjecture/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/reconstruction_conjecture.json
    English statement: (OPG "Reconstruction conjecture", Kelly and Ulam)
      For any two simple graphs G and H, each on at least three vertices: if there is a
      bijection f from the vertices of G to the vertices of H such that, for every vertex v
      of G, the graph G with v deleted is isomorphic to the graph H with f(v) deleted, then
      G and H are isomorphic.
    Definitions: [vdel_card G v] — the card G - v, that is the subgraph of G induced on the
      vertices different from v (U11.v); [same_deck G H] — some vertex bijection matches the
      two vertex-deleted decks up to isomorphism (U11.v); [reconstructible G] — every H with
      the same deck is isomorphic to G (U11.v; the statement below spells the two-graph form
      out instead of using it); [induced] is coq-graph-theory.
    Notes: the corpus describes the deck as a multiset of unlabelled cards counted with
      multiplicity; the bijection-of-index-sets model used here is the standard equivalent
      reading. The three-vertex guard is imposed on both G and H, although the bijection
      already forces their vertex counts to agree. *)
Definition reconstruction_statement : Prop :=
  forall G H : sgraph,
    (3 <= #|G|)%N -> (3 <= #|H|)%N -> same_deck G H -> inhabited (G ≃ H).
