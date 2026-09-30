(** * Chromatic.conjectures.X50 -- v2 same-girth induced-free row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X50 vocabulary ************************************************)

Definition x50_same_girth (G H : sgraph) : Prop :=
  forall g : nat, has_girth G g <-> has_girth H g.

Definition x50_induced_F_free (F G : sgraph) : Prop :=
  forall S : {set G}, ~ inhabited (induced S ≃ F).

Definition x50_all_F_free_induced_subgraphs_c_colourable
    (F G : sgraph) (c : nat) : Prop :=
  forall S : {set G},
    x50_induced_F_free F (induced S) ->
    χ([set: induced S]) <= c.

(** ** X50 statements ******************************************************)

(** Corpus row: arxiv:2203.03612#00
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/2203.03612__00/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/2203.03612__00.json
    English statement: (Girao, Illingworth, Powierski, Savery, Scott, Tamitegama and Tan 2023, girth conjecture strengthening Theorem 3, arXiv:2203.03612)
      For every triangle-free finite simple graph F that contains a cycle, hence has a well-defined
      girth, there is a constant cF such that for every target there is a graph G with chromatic
      number at least the target, the same girth as F, and such that every induced subgraph of G
      containing no induced copy of F has chromatic number at most cF.
    Definitions: [x50_same_girth G H] - G and H satisfy [has_girth] for exactly the same values,
      i.e. they have equal girth (this file); [has_girth G g] - girth at least g together with a
      genuine g-cycle (GTBase base/theories/base.v); [x50_induced_F_free F G] - no vertex set of G
      induces a copy of F (this file); [x50_all_F_free_induced_subgraphs_c_colourable F G c] - every
      F-free induced subgraph of G has chromatic number at most c (this file); [triangle_free]
      (base.v).
    Notes: The guard that F has some girth excludes forests, for which "the same girth" is not
      expressible with [has_girth]. "Arbitrarily large chromatic number" is rendered by the
      universal quantifier over the target, with cF chosen BEFORE it, as in the source. *)
Definition triangle_free_same_girth_high_chromatic_induced_free_statement : Prop :=
  forall F : sgraph,
    triangle_free F ->
    (exists g : nat, has_girth F g) ->
    exists cF : nat,
      forall target : nat,
        exists G : sgraph,
          target <= χ([set: G]) /\
          x50_same_girth F G /\
          x50_all_F_free_induced_subgraphs_c_colourable F G cF.
