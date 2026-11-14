(** * Topological.conjectures.X307 -- v2 row: Grunbaum's torus conjecture for cubic graphs
      (studies:std_gr_nbaum_s_conjecture_torus_cubic_graphs): a 2-connected cubic graph with an embedding in the torus
      that is not 3-edge-colourable has two edges whose removal leaves a planar graph *)

From GTBase Require Import base surface edge_colourings.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** X307 statement ******************************************************)

(** Reused vocabulary, all GTBase: [k_connected] and [regular] (base.v), [surface_embeddable] (surface.v),
    [proper_edge_colouring] (edge_colourings.v), [E(G)], [del_edge_set] and [wagner_planar] (base.v, common.v).
    X307 declares no helper of its own. *)

(** Corpus row: studies:std_gr_nbaum_s_conjecture_torus_cubic_graphs
    Site: none
    Review: none
    English statement: (Grunbaum, 1968, "Conjecture 6", Proceedings of the Third Waterloo Conference on
      Combinatorics, as stated in Inoue, Kawarabayashi, Miyashita, Mohar, Sonobe, arXiv:2405.16586v1, main.tex
      l.163-165, Conjecture 2 of its text version)
      If G is a 2-connected cubic graph embedded in the torus and G is not 3-edge-colorable, then G contains two edges
      whose removal gives a planar graph.
    Definitions: [k_connected G 2] - G has more than 2 vertices and stays connected after deleting any one vertex
      (base.v); [regular G 3] - every vertex has exactly 3 neighbours (base.v); [surface_embeddable 1 G] - a rotation
      system of G has orientable genus at most 1, the count (2 + E - V - F) %/ 2 of surface.v;
      [proper_edge_colouring col] - edges at a common vertex get different colours (edge_colourings.v), so "no
      col : {set G} -> 'I_3 is proper" says G is not 3-edge-colourable; [E(G)] - the edges of G as 2-element vertex
      sets; [del_edge_set G F] - G without the edges in F (common.v); [wagner_planar H] - H has no K_5 and no K_(3,3)
      minor (base.v).
    Notes: "embedded in the torus" is read as "has an embedding of orientable genus at most 1": a planar graph also
      embeds in the torus, but a 2-connected cubic planar graph is 3-edge-colourable (the Four Colour Theorem in the
      source's Theorem 1.1, main.tex l.135-137), so genus 0 adds no graph to the hypothesis.  surface_embeddable
      understates the genus of a disconnected graph (CLAUDE.md); 2-connectivity implies connectivity, so the guard is
      in the hypothesis (grounding_X307.v, g307_k2_connected).  The source writes "(multi)graph" where it means
      multigraphs (l.99-102) and plain "graph" in the conjecture; the row is encoded over simple graphs, the carrier of
      the embedding vocabulary, and a multigraph reading is not encoded.  "Two edges" is read literally as two
      distinct edges; planarity is minor-closed and a cubic graph has at least 6 edges, so "at most two" would give
      the same statement.  [surface_embeddable 1 G] agrees with Topological's [toroidal] (embedding.v),
      [g307_surface_embeddable_genus] in grounding_X307.v.  Status: open at the source (l.155-161: Kochol refuted the
      polyhedral form at genus 5; the smaller genera are unresolved; Vodopivec's infinitely many toroidal snarks each
      have two such edges). *)
Definition grunbaum_torus_cubic_statement : Prop :=
  forall G : sgraph,
    k_connected G 2 ->
    regular G 3 ->
    surface_embeddable 1 G ->
    ~ (exists col : {set G} -> 'I_3, proper_edge_colouring col) ->
    exists e1 e2 : {set G},
      [/\ e1 \in E(G), e2 \in E(G), e1 != e2 & wagner_planar (del_edge_set G [set e1; e2])].
