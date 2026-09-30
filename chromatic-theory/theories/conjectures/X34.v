(** * Chromatic.conjectures.X34 -- v2 odd-degree planar linear arboricity row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X34 vocabulary ************************************************)

Definition x34_edge_set (G : sgraph) : {set {set G}} :=
  [set e : {set G} |
      [exists x : G, [exists y : G, (x -- y) && (e == [set x; y])]]].

Definition x34_edge_colour_rel
    (G : sgraph) (q : nat) (col : {set G} -> 'I_q) (i : 'I_q) : rel G :=
  fun x y => (x -- y) && (col [set x; y] == i).

Lemma x34_edge_colour_sym
    (G : sgraph) (q : nat) (col : {set G} -> 'I_q) (i : 'I_q) :
  symmetric (x34_edge_colour_rel col i).
Proof. by move=> x y; rewrite /x34_edge_colour_rel sg_sym setUC. Qed.

Lemma x34_edge_colour_irrefl
    (G : sgraph) (q : nat) (col : {set G} -> 'I_q) (i : 'I_q) :
  irreflexive (x34_edge_colour_rel col i).
Proof. by move=> x; rewrite /x34_edge_colour_rel sg_irrefl. Qed.

Definition x34_colour_graph
    (G : sgraph) (q : nat) (col : {set G} -> 'I_q) (i : 'I_q) : sgraph :=
  SGraph (x34_edge_colour_sym col i) (x34_edge_colour_irrefl col i).

Definition x34_linear_forest_colour
    (G : sgraph) (q : nat) (col : {set G} -> 'I_q) (i : 'I_q) : Prop :=
  is_forest [set: x34_colour_graph col i] /\
  Delta (x34_colour_graph col i) <= 2.

Definition x34_matching_colour
    (G : sgraph) (q : nat) (col : {set G} -> 'I_q) (i : 'I_q) : Prop :=
  forall v : G, #|[set e in x34_edge_set G | (col e == i) && (v \in e)]| <= 1.

Definition x34_linear_forests_and_matching
    (G : sgraph) (q : nat) (col : {set G} -> 'I_(q.+1)) : Prop :=
  (forall i : 'I_q,
      x34_linear_forest_colour col (widen_ord (leqnSn q) i)) /\
  x34_matching_colour col ord_max.

(** ** X34 statements ******************************************************)

(** Corpus row: arxiv:2302.13312#00
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/2302.13312__00/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/2302.13312__00.json
    English statement: (Bonamy, Czyzewska, Kowalik and Pilipczuk 2023, Conjecture 2, arXiv:2302.13312)
      For every planar finite simple graph G whose maximum degree is odd and at least 9, the edges
      of G can be coloured with (Delta(G)-1)/2 + 1 colours so that each of the first (Delta(G)-1)/2
      colour classes is a linear forest, i.e. a forest of maximum degree at most 2, and the last
      colour class is a matching.
    Definitions: [x34_colour_graph col i] - the spanning subgraph formed by the edges of colour i
      (this file); [x34_linear_forest_colour col i] - that subgraph is a forest of maximum degree at
      most 2 (this file); [x34_matching_colour col i] - every vertex is in at most one edge of
      colour i (this file); [x34_linear_forests_and_matching col] - the first q colours are linear
      forests and the last is a matching (this file); [x34_edge_set G] (this file); [wagner_planar],
      [is_forest], [Delta] (GTBase base/theories/base.v).
    Notes: DISCREPANCY with the corpus text: the source conjecture assumes Delta >= 7, whereas the
      Rocq guard is 9 <= Delta G. The formal statement is therefore WEAKER than the conjecture, and
      it excludes exactly the case Delta = 7, which the corpus records as the only case still open;
      the cases Delta >= 9 are already proved in the literature. This is recorded in
      meta/STATEMENT_IMPROVEMENTS.md. The body is left untouched here, WP4 changes comments only. *)
Definition planar_odd_degree_linear_forests_plus_matching_statement : Prop :=
  forall G : sgraph,
    wagner_planar G ->
    odd (Delta G) ->
    9 <= Delta G ->
    let q := (Delta G - 1) %/ 2 in
    exists col : {set G} -> 'I_(q.+1),
      x34_linear_forests_and_matching col.
