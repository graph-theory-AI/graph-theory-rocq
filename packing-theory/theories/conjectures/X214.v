(** * Packing.conjectures.X214 -- spanning bipartite subgraph rows (wave X214, 2026-09-23) *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X214 vocabulary ***********************************************

    NONE.  Every notion this wave needs is already owned by the shared layer:
    [k_connected] (Whitney form) and [bipartite] live in [GTBase.base], and a
    SPANNING SUBGRAPH of [G] is exactly a [GTBase.common] edge deletion
    [del_edge_set G F] (same vertex type, the edges of [G] outside [F]).  No
    [Local x214_...] definition is introduced. *)

(** ** X214 statements ****************************************************)

(** Corpus row: bm:bm-025
    Site: https://graph-theory-ai.github.io/graph-conjectures/bm/bm-025/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/bondy_murty_reviews/bm-025.json
    English statement: (Thomassen 1989; Bondy and Murty, Graph Theory, Appendix A,
      Conjecture 25)
      For every integer k >= 1 and every finite simple graph G that is 2k-connected,
      there is a set F of vertex pairs such that the spanning subgraph of G obtained
      by deleting the edges in F — same vertices, the edges of G that are not in F —
      is bipartite and k-connected.
    Definitions: [k_connected G k] — GTBase.base, Whitney form: k < |V(G)| and
      deleting any fewer than k vertices leaves the rest of G connected;
      [bipartite G] — GTBase.base: some 2-colouring of V(G) gives the two ends of
      every edge different colours; [del_edge_set G F] — GTBase.common: the graph on
      the vertices of G whose edges are the edges of G outside F.
    Notes: "spanning subgraph" is encoded as [del_edge_set G F] with F ranging over
      all sets of vertex pairs: those graphs are exactly the subgraphs of G with the
      full vertex set (take F = E(G) \ E(H)), and the encoding makes "spanning"
      definitional rather than an extra hypothesis. Guard [0 < k]: at k = 0 both the
      hypothesis and the conclusion degenerate to "G has a vertex" (delete every
      edge), so the k = 0 instance is trivially true and is excluded, as in the
      source, whose f(k) = 2k is read for k >= 1. The source's partial results
      (Delcourt–Ferber, Yuster: connectivity 22k^2 log n suffices) are asymptotic in
      |V(G)| and are NOT part of this statement, which is the book's f(k) = 2k form. *)
Definition spanning_k_connected_bipartite_subgraph_statement : Prop :=
  forall (k : nat) (G : sgraph),
    0 < k ->
    k_connected G (2 * k) ->
    exists F : {set {set G}},
      bipartite (del_edge_set G F) /\ k_connected (del_edge_set G F) k.
