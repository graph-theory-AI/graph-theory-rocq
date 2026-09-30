(** * Chromatic.conjectures.X43 -- v2 strong edge-colouring row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X43 vocabulary ************************************************)

Definition x43_edge_set (G : sgraph) : {set {set G}} :=
  [set e : {set G} |
      [exists x : G, [exists y : G, (x -- y) && (e == [set x; y])]]].

Definition x43_line_vertex (G : sgraph) : Type :=
  {e : {set G} | e \in x43_edge_set G}.

Definition x43_line_rel (G : sgraph) : rel (x43_line_vertex G) :=
  fun e f => (val e != val f) && (val e :&: val f != set0).

Lemma x43_line_rel_sym (G : sgraph) : symmetric (@x43_line_rel G).
Proof. by move=> e f; rewrite /x43_line_rel eq_sym setIC. Qed.

Lemma x43_line_rel_irrefl (G : sgraph) : irreflexive (@x43_line_rel G).
Proof. by move=> e; rewrite /x43_line_rel eqxx. Qed.

Definition x43_line_graph (G : sgraph) : sgraph :=
  SGraph (@x43_line_rel_sym G) (@x43_line_rel_irrefl G).

Definition x43_strong_edge_colourable (G : sgraph) (k : nat) : Prop :=
  χ([set: graph_power (x43_line_graph G) 2]) <= k.

Definition x43_diamond_rel (u v : bool + bool) : bool :=
  match u, v with
  | inl a, inl b => a != b
  | inl _, inr _ => true
  | inr _, inl _ => true
  | inr _, inr _ => false
  end.

Lemma x43_diamond_sym : symmetric x43_diamond_rel.
Proof. by move=> [a|a] [b|b] //=; rewrite eq_sym. Qed.

Lemma x43_diamond_irrefl : irreflexive x43_diamond_rel.
Proof. by move=> [a|a] //=; rewrite eqxx. Qed.

Definition x43_diamond : sgraph := SGraph x43_diamond_sym x43_diamond_irrefl.

Definition x43_claw_rel (u v : option 'I_3) : bool :=
  match u, v with
  | None, Some _ => true
  | Some _, None => true
  | _, _ => false
  end.

Lemma x43_claw_sym : symmetric x43_claw_rel.
Proof. by move=> [a|] [b|]. Qed.

Lemma x43_claw_irrefl : irreflexive x43_claw_rel.
Proof. by move=> [a|]. Qed.

Definition x43_claw : sgraph := SGraph x43_claw_sym x43_claw_irrefl.

Definition x43_induced_free (G H : sgraph) : Prop :=
  forall S : {set G}, ~ inhabited (induced S ≃ H).

(** ** X43 statements ******************************************************)

(** Corpus row: arxiv:2511.02892#03
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/2511.02892__03/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/2511.02892__03.json
    English statement: (Barat, Dvorak, Haxell, Kardos, Luzar, Onderko, Rajnik, Sotak and Ulyanov 2025, Problem 4.1, arXiv:2511.02892)
      Every cubic finite simple graph with no induced diamond, the complete graph on four vertices
      minus an edge, and no induced claw, the star with three leaves, is strongly 6-edge-colourable:
      the square of its line graph has chromatic number at most 6.
    Definitions: [x43_strong_edge_colourable G k] - chi of [graph_power (x43_line_graph G) 2] is
      at most k, the standard reduction of strong edge colouring to colouring the square of the line
      graph (this file); [x43_line_graph G] - the line graph built on the edges of a simple graph,
      two edges adjacent when distinct and meeting (this file); [x43_diamond] and [x43_claw] - the
      two forbidden graphs, built explicitly on [bool + bool] and [option 'I_3] (this file);
      [x43_induced_free G H] - no vertex set of G induces a copy of H (this file); [regular G 3]
      (GTBase base/theories/base.v).
    Notes: The corpus row is a QUESTION; the Rocq body is its affirmative reading. The source also
      gives an equivalent phrasing in terms of the truncated graph T(G) of an arbitrary cubic graph,
      which is NOT encoded here; only the diamond-free claw-free cubic formulation is. *)
Definition diamond_free_claw_free_cubic_strong_six_edge_colourable_statement : Prop :=
  forall G : sgraph,
    regular G 3 ->
    x43_induced_free G x43_diamond ->
    x43_induced_free G x43_claw ->
    x43_strong_edge_colourable G 6.
