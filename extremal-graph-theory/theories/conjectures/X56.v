(** * Extremal.conjectures.X56 -- v2 C8 Erdos-Hajnal row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X56 vocabulary ************************************************)

Definition x56_stable_set (G : sgraph) (S : {set G}) : Prop :=
  forall x y : G, x \in S -> y \in S -> x -- y -> False.

Definition x56_homogeneous_set (G : sgraph) (S : {set G}) : Prop :=
  clique S \/ x56_stable_set S.

Definition x56_complement_rel (G : sgraph) : rel G :=
  fun x y => (x != y) && ~~ (x -- y).

Lemma x56_complement_sym (G : sgraph) : symmetric (@x56_complement_rel G).
Proof. by move=> x y; rewrite /x56_complement_rel eq_sym sgP. Qed.

Lemma x56_complement_irrefl (G : sgraph) : irreflexive (@x56_complement_rel G).
Proof. by move=> x; rewrite /x56_complement_rel eqxx. Qed.

Definition x56_complement (G : sgraph) : sgraph :=
  SGraph (@x56_complement_sym G) (@x56_complement_irrefl G).

Definition x56_induced_free (G H : sgraph) : Prop :=
  forall S : {set G}, ~ inhabited (induced S ≃ H).

(** Corpus row: arxiv:2102.04994#00
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/2102.04994__00/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/2102.04994__00.json
    English statement: (Chudnovsky, Scott, Seymour, Spirkl 2021, arXiv:2102.04994, Erdos-Hajnal property for {C_8, complement of C_8})
      There is a constant c > 0 such that every non-empty graph G with no induced 8-cycle and
      no induced complement of an 8-cycle has a homogeneous set S (a clique or an independent
      set) with |V(G)| <= |S|^c, i.e. |S| >= |V(G)|^(1/c).
    Definitions: [x56_stable_set S] - no two vertices of S are adjacent (X56.v); [x56_homogeneous_set S] -
      S is a clique or a stable set (X56.v); [x56_complement G] - the complement graph (X56.v);
      [x56_induced_free G H] - no vertex set of G induces a graph isomorphic to H (X56.v);
      [cycle_graph 8], [clique], [induced] - GTBase / coq-graph-theory.
    Notes: the Erdos-Hajnal exponent delta of the literature is 1/c here, with c a positive natural,
      so only reciprocals of integers are available as exponents; this is a restriction of the
      source's arbitrary positive delta (ledger). *)
Definition c8_complement_c8_erdos_hajnal_statement : Prop :=
  exists c : nat,
    0 < c /\
    forall G : sgraph,
      0 < #|G| ->
      x56_induced_free G (cycle_graph 8) ->
      x56_induced_free G (x56_complement (cycle_graph 8)) ->
      exists S : {set G},
        x56_homogeneous_set S /\
        #|G| <= (#|S|) ^ c.
