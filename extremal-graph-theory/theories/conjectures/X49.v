(** * Extremal.conjectures.X49 -- v2 induced-saturation row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X49 vocabulary ************************************************)

Definition x49_add_edge_rel (G : sgraph) (a b : G) : rel G :=
  fun x y => (x -- y) || ((x != y) && ([set x; y] == [set a; b])).

Lemma x49_add_edge_sym (G : sgraph) (a b : G) :
  symmetric (x49_add_edge_rel a b).
Proof. by move=> x y; rewrite /x49_add_edge_rel sg_sym eq_sym setUC. Qed.

Lemma x49_add_edge_irrefl (G : sgraph) (a b : G) :
  irreflexive (x49_add_edge_rel a b).
Proof. by move=> x; rewrite /x49_add_edge_rel sg_irrefl eqxx. Qed.

Definition x49_add_edge_graph (G : sgraph) (a b : G) : sgraph :=
  SGraph (x49_add_edge_sym a b) (x49_add_edge_irrefl a b).

Definition x49_has_induced_cycle (G : sgraph) (n : nat) : Prop :=
  exists S : {set G}, #|S| = n /\ inhabited (induced S ≃ cycle_graph n).

(** Corpus row: arxiv:2505.24100#00
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/2505.24100__00/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/2505.24100__00.json
    English statement: (Fan, S. Hajebi, S. Hajebi, Spirkl 2025, arXiv:2505.24100 Question 1.7)
      For every t >= 6 there is a graph G with at least one non-edge that has no induced cycle
      on 2t-2 vertices, yet adding any single non-edge to G creates an induced cycle on 2t-2
      vertices.
    Definitions: [x49_add_edge_graph G a b] - G with the pair {a,b} added as an edge (X49.v);
      [x49_has_induced_cycle G n] - some n-element vertex set induces a graph isomorphic to the
      n-cycle (X49.v); [cycle_graph], [induced], [~=] - GTBase / coq-graph-theory.
    Notes: the corpus statement_text reads "G is H-free" with H undefined in that context; the
      manifest flags this as garbled, and the intended reading, used here, is that G has no
      induced C_{2t-2}. The subtraction 2*t - 2 is nat subtraction, safe because t >= 6. *)
Definition induced_saturation_even_cycle_existence_statement : Prop :=
  forall t : nat,
    6 <= t ->
    exists G : sgraph,
      (exists a b : G, a != b /\ ~~ (a -- b)) /\
      ~ x49_has_induced_cycle G (2 * t - 2) /\
      forall a b : G,
        a != b ->
        ~~ (a -- b) ->
        x49_has_induced_cycle (@x49_add_edge_graph G a b) (2 * t - 2).
