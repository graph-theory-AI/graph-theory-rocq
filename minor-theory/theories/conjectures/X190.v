(** * Minor.conjectures.X190 -- v2 thin overlay without bounded degree row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X190 vocabulary ***********************************************)

Definition x190_weight (G : sgraph) (rho : G -> nat) (S : {set G}) : nat :=
  \sum_(v in S) rho v.

Definition x190_strongly_sublinear_separator_class (C : sgraph -> Prop) : Prop :=
  exists a b K : nat,
    0 < a /\ a < b /\
    forall (G : sgraph) (rho : G -> nat),
      C G ->
      exists S : {set G},
        (#|S| ^ b <= K * (#|G|.+1 ^ a)) /\
        forall A : {set G},
          A \subset ~: S ->
          connected A ->
          2 * x190_weight rho A <= x190_weight rho [set: G].

Record x190_overlay (G : sgraph) (thin : nat) := {
  x190_cover_graph : sgraph;
  x190_cover_map : x190_cover_graph -> G;
  x190_fibre_thin : forall v : G, #|[set x : x190_cover_graph | x190_cover_map x == v]| <= thin;
  x190_edge_lift :
    forall u v : G, u -- v ->
      exists x y : x190_cover_graph,
        [/\ x190_cover_map x = u, x190_cover_map y = v & x -- y]
}.

Definition x190_thin_system_of_overlays (C : sgraph -> Prop) : Prop :=
  exists thin : nat,
    forall G : sgraph, C G -> exists _ : x190_overlay G thin, True.

(** ** X190 statements *****************************************************)

(** Corpus row: arxiv:1704.00125#00
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/1704.00125__00/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/1704.00125__00.json
    English statement: (Dvorak 2017, informal conjecture of Section 1.2 of "Thin graph classes
      and polynomial-time approximation schemes")
      Every class of finite simple graphs with strongly sublinear separators admits a thin
      system of overlays, i.e. the extra bounded-maximum-degree assumption of the paper's
      theorem can be dropped.
    Definitions: [x190_weight rho S] - the sum of the weights rho over the vertex set S
      (minor-theory/theories/conjectures/X190.v);
      [x190_strongly_sublinear_separator_class C] - there are naturals a, b, K with 0 < a < b
      such that every graph G of C and every vertex weighting rho admit a separator S with
      |S|^b <= K * (|V(G)|+1)^a and every connected vertex set avoiding S carrying at most half
      the total weight (same file); [x190_overlay G thin] - a record consisting of a cover
      graph, a map from it onto G whose fibres have at most `thin` vertices, and a lift of
      every edge of G (same file); [x190_thin_system_of_overlays C] - there is one bound
      `thin` such that every graph of C has such an overlay (same file).
    Notes: VACUOUS CONCLUSION (faithfulness audit 2026-07-17,
      meta/BLOCKED_RETARGETING_AUDIT.md).  The [x190_overlay] record is inhabited for EVERY
      graph G by the identity cover (cover graph G, cover map the identity, every fibre a
      singleton), so [x190_thin_system_of_overlays C] holds for every class C with thin = 1 and
      the whole statement is provable without capturing the intended notion.  The source's
      overlays additionally have to be structured (bounded-treewidth pieces covering G) - that
      structure is missing here, which is why the row is recorded as blocked. *)
Definition thin_overlay_without_bounded_degree_statement : Prop :=
  forall C : sgraph -> Prop,
    x190_strongly_sublinear_separator_class C ->
    x190_thin_system_of_overlays C.
