(** * Extremal.conjectures.X191 -- v2 dense H-free clique-blowup error row *)

From GTBase Require Export base.
From GraphTheory Require Import minor.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X191 vocabulary ***********************************************)

Definition x191_clique_blowup_rel (m t : nat) : rel ('I_m * 'I_t) :=
  fun x y => x.1 != y.1.

Definition x191_clique_blowup (m t : nat) : sgraph :=
  @fg_mk_sgraph ('I_m * 'I_t)%type (@x191_clique_blowup_rel m t).

Definition x191_copy_count (P G : sgraph) : nat :=
  #|[set f : {ffun P -> G} |
      [forall x : P, [forall y : P, (f x == f y) ==> (x == y)]] &&
      [forall x : P, [forall y : P, (x -- y) ==> (f x -- f y)]]]|.

Definition x191_spanning_subgraph_of (F G : sgraph) : Prop :=
  exists emb : F -> G,
    bijective emb /\
    forall x y : F, x -- y -> emb x -- emb y.

Definition x191_dense_H_free_clique_blowup_extremal
    (H G F : sgraph) (m t : nat) : Prop :=
  x191_spanning_subgraph_of F G /\
  ~ minor F H /\
  (forall F' : sgraph,
    x191_spanning_subgraph_of F' G ->
    ~ minor F' H ->
    x191_copy_count (x191_clique_blowup m t) F' <=
      x191_copy_count (x191_clique_blowup m t) F).

Definition x191_delete_edges (F : sgraph) (X : {set {set F}}) : sgraph :=
  @fg_mk_sgraph F (fun x y => (x -- y) && ([set x; y] \notin X)).

Definition x191_subquadratic_deletion_to_partite
    (F : sgraph) (parts delta_num delta_den : nat) : Prop :=
  exists C : nat,
    forall n : nat,
      #|F| = n ->
      exists X : {set {set F}},
        #|X| ^ delta_den <= C * n ^ (2 * delta_den - delta_num) + C /\
        χ([set: x191_delete_edges X]) <= parts.

(** Corpus row: arxiv:1706.05642#00
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/1706.05642__00/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/1706.05642__00.json
    English statement: (Alon, Shikhelman 2017, arXiv:1706.05642, Informal Conjecture on the error term in Proposition 1.4)
      For every graph H there are a positive rational delta = delta_num/delta_den <= 1 and
      constants C, N such that for every graph G on at least N vertices and every spanning
      H-minor-free subgraph F of G maximising the number of copies of the clique blow-up
      K_m[t], one can delete at most O(|V(F)|^(2-delta)) edges from F and obtain a graph of
      chromatic number at most chi(H) - 1.
    Definitions: [x191_clique_blowup m t] - the blow-up of K_m in which each of the m classes has t
      vertices, two vertices adjacent exactly when their classes differ (X191.v);
      [x191_copy_count P G] - the number of injective adjacency-preserving maps P -> G
      (X191.v); [x191_spanning_subgraph_of F G] - a bijection V(F) -> V(G) mapping edges to
      edges, i.e. F is a spanning subgraph of G (X191.v);
      [x191_dense_H_free_clique_blowup_extremal H G F m t] - F is a spanning H-minor-free
      subgraph of G maximising [x191_copy_count] of the blow-up (X191.v); [x191_delete_edges F
      X] - F with the edges listed in X removed (X191.v);
      [x191_subquadratic_deletion_to_partite F parts dnum dden] - a deletion set X with
      |X|^dden <= C * n^(2*dden - dnum) + C and chromatic number at most parts (X191.v);
      [minor], [chi], [fg_mk_sgraph] - coq-graph-theory / GTBase.
    Notes: this row is recorded as BLOCKED. The 2026-07-17 faithfulness audit
      (meta/BLOCKED_RETARGETING_AUDIT.md) found a FINITENESS COLLAPSE: the whole content of the
      conjecture is quantitative (improving an o(n^2) error to O(n^(2-delta))), but inside
      [x191_subquadratic_deletion_to_partite] the constant C is chosen AFTER F is fixed, and the
      apparently asymptotic [forall n, #|F| = n -> ...] pins n to the single value |V(F)|. One
      graph is not a growing family, so the exponent carries no content and the predicate is
      satisfiable by taking C large. The statement is therefore trivially true / too weak
      (ledger). [chi(H) - 1] is nat subtraction. *)
Definition dense_H_free_clique_blowup_subquadratic_error_statement : Prop :=
  forall H : sgraph,
    exists delta_num delta_den C N : nat,
      [/\ 0 < delta_num, delta_num <= delta_den &
        forall (G F : sgraph) (m t : nat),
          N <= #|G| ->
          x191_dense_H_free_clique_blowup_extremal H G F m t ->
          x191_subquadratic_deletion_to_partite F (χ([set: H]) - 1) delta_num delta_den].
