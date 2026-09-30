(** * Chromatic.conjectures.X31 -- v2 chromatic-girth subgraph row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X31 vocabulary ************************************************)

Definition x31_subgraph_of (H G : sgraph) : Prop :=
  exists f : H -> G,
    injective f /\
    forall x y : H, x -- y -> f x -- f y.

(** ** X31 statements ******************************************************)

(** Corpus row: arxiv:1808.01605#01
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/1808.01605__01/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/1808.01605__01.json
    English statement: (Mohar and Wu 2018, Conjecture 6, arXiv:1808.01605)
      For every k > 0 and every g >= 3 there is a c > 0 such that every finite simple graph with
      chromatic number at least c contains a subgraph of girth at least g whose average degree is at
      least k.
    Definitions: [x31_subgraph_of H G] - an injective adjacency-preserving map from H into G, i.e.
      H is a subgraph of G, not necessarily induced (this file); [girth_geq H g] (GTBase
      base/theories/base.v); [average_degree_geq H k 1] - the average degree of H is at least k/1,
      stated through the handshake sum of degrees (base.v).
    Notes: The quantifier order matches the source: c depends on k and g only. Subgraphs are not
      required to be induced, as in the source. *)
Definition chromatic_girth_average_degree_subgraph_statement : Prop :=
  forall k g : nat,
    0 < k ->
    3 <= g ->
    exists c : nat,
      0 < c /\
      forall G : sgraph,
        c <= χ([set: G]) ->
        exists H : sgraph,
          x31_subgraph_of H G /\
          girth_geq H g /\
          average_degree_geq H k 1.
