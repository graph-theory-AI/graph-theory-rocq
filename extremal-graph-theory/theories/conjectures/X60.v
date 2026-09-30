(** * Extremal.conjectures.X60 -- v2 polynomial induced-saturation row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X60 vocabulary ************************************************)

Fixpoint x60_poly_eval (p : seq nat) (x : nat) : nat :=
  if p is a :: q then a + x * x60_poly_eval q x else 0.

Definition x60_edge_set (G : sgraph) : {set {set G}} :=
  [set e : {set G} |
      [exists x : G, [exists y : G, (x -- y) && (e == [set x; y])]]].

Definition x60_delete_edge_rel (G : sgraph) (e : {set G}) : rel G :=
  fun x y => (x -- y) && ([set x; y] != e).

Lemma x60_delete_edge_sym (G : sgraph) (e : {set G}) :
  symmetric (@x60_delete_edge_rel G e).
Proof. by move=> x y; rewrite /x60_delete_edge_rel sgP setUC. Qed.

Lemma x60_delete_edge_irrefl (G : sgraph) (e : {set G}) :
  irreflexive (@x60_delete_edge_rel G e).
Proof. by move=> x; rewrite /x60_delete_edge_rel sg_irrefl. Qed.

Definition x60_delete_edge_graph (G : sgraph) (e : {set G}) : sgraph :=
  SGraph (@x60_delete_edge_sym G e) (@x60_delete_edge_irrefl G e).

Definition x60_has_induced_cycle (G : sgraph) (n : nat) : Prop :=
  exists S : {set G}, #|S| = n /\ inhabited (induced S ≃ cycle_graph n).

(** Corpus row: arxiv:2505.24100#01
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/2505.24100__01/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/2505.24100__01.json
    English statement: (Fan, S. Hajebi, S. Hajebi, Spirkl 2025, arXiv:2505.24100 Question 1.8)
      There is a polynomial p such that for every t >= 3 there is a graph G on at most p(t)
      vertices with at least one edge that has no induced cycle on 2t-2 vertices, yet deleting
      any single edge of G creates an induced cycle on 2t-2 vertices.
    Definitions: [x60_poly_eval p x] - Horner evaluation of a coefficient list (X60.v); [x60_edge_set G] -
      the edges of G as 2-element vertex sets (X60.v); [x60_delete_edge_graph G e] - G with the
      edge e removed (X60.v); [x60_has_induced_cycle G n] - some n-element vertex set induces a
      copy of the n-cycle (X60.v); [cycle_graph], [induced] - GTBase / coq-graph-theory.
    Notes: as in X49, the corpus statement_text reads "G is H-free" with H undefined; the manifest
      flags this as garbled and the intended reading, used here, is that G has no induced
      C_{2t-2}. The polynomial is a coefficient list, so only non-negative integer coefficients
      are available. The subtraction 2*t - 2 is safe because t >= 3. *)
Definition induced_saturation_even_cycle_polynomial_size_statement : Prop :=
  exists p : seq nat,
    forall t : nat,
      3 <= t ->
      exists G : sgraph,
        #|G| <= x60_poly_eval p t /\
        0 < #|x60_edge_set G| /\
        ~ x60_has_induced_cycle G (2 * t - 2) /\
        forall e : {set G},
          e \in x60_edge_set G ->
          x60_has_induced_cycle (@x60_delete_edge_graph G e) (2 * t - 2).
