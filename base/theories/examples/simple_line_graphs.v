(** Downstream use of the simple line graph without corpus imports: adjacency and cardinality, edgeless inputs
    (['K_0], ['K_1], three isolated vertices) collapsing to the empty graph, ['K_2] to one isolated vertex, the
    three-vertex path ['K_1,2] to ['K_2], the triangle and the claw both to ['K_3] (so the line operation is not
    injective), iteration from zero through successive line operations, and the transport of the square's
    chromatic number (strong edge colouring). *)
From GraphTheory Require Import bij.
From GTBase Require Import base simple_line_graphs.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section PublicClient.
Variable G : sgraph.

(** Adjacency: distinct edges sharing an endpoint; no edge is adjacent to itself. *)
Example line_adjacency (e f : simple_line_graph G) :
  e -- f = (val e != val f) && (val e :&: val f != set0) /\ ~~ (e -- e).
Proof. by rewrite simple_line_edgeE sg_irrefl. Qed.

(** One vertex per edge of [G]; iteration zero is [G] itself. *)
Example line_cardinality : #|simple_line_graph G| = #|E(G)| /\ iter 0 simple_line_graph G = G.
Proof. by rewrite card_simple_line_graph. Qed.

End PublicClient.

(** Edgeless inputs have empty line graphs: isolated vertices disappear. *)
Example edgeless_line_graphs :
  [/\ #|simple_line_graph 'K_0| = 0, #|simple_line_graph 'K_1| = 0 & #|simple_line_graph 'K_0,3| = 0].
Proof. by rewrite !card_simple_line_graph !card_edge_Kn card_edge_Knm. Qed.

(** Two 2-sets of a set of at most three vertices meet. *)
Lemma small_edges_meet (H : sgraph) : #|H| <= 3 -> {in E(H) &, forall e f, e :&: f != set0}.
Proof.
move=> H3 e f /edgesP[x [y [-> xy]]] /edgesP[u [v [-> uv]]].
rewrite -card_gt0 -(ltn_add2l #|[set x; y] :|: [set u; v]|) addn0 cardsUI !cards2 (sg_edgeNeq xy) (sg_edgeNeq uv).
by apply: leq_ltn_trans (leq_trans (max_card _) H3) _.
Qed.

(** Every edge of the star ['K_1,n] contains its centre. *)
Lemma star_edges_meet (n : nat) : {in E('K_1,n) &, forall e f, e :&: f != set0}.
Proof.
have centre (e : {set 'K_1,n}) : e \in E('K_1,n) -> inl ord0 \in e.
  by rewrite Knm_edges => /imset2P[x y _ _ ->]; rewrite (ord1 x) !inE eqxx.
by move=> e f eE fE; apply/set0Pn; exists (inl ord0); rewrite inE !centre.
Qed.

(** ['K_2] becomes one isolated vertex, the three-vertex path ['K_1,2] becomes ['K_2]. *)
Example line_K2 : simple_line_graph 'K_2 ≃ 'K_1.
Proof. by apply: simple_line_graph_complete; [apply: small_edges_meet; rewrite card_ord | rewrite card_edge_Kn]. Qed.

Example line_path3 : simple_line_graph 'K_1,2 ≃ 'K_2.
Proof. by apply: simple_line_graph_complete; [exact: star_edges_meet | rewrite card_edge_Knm]. Qed.

(** The triangle and the claw both have the triangle as line graph. *)
Example line_triangle : simple_line_graph 'K_3 ≃ 'K_3.
Proof. by apply: simple_line_graph_complete; [apply: small_edges_meet; rewrite card_ord | rewrite card_edge_Kn]. Qed.

Example line_claw : simple_line_graph 'K_1,3 ≃ 'K_3.
Proof. by apply: simple_line_graph_complete; [exact: star_edges_meet | rewrite card_edge_Knm]. Qed.

(** The line operation is not injective: isomorphic line graphs, non-isomorphic graphs (three vertices against
    four). *)
Example line_not_injective :
  inhabited (simple_line_graph 'K_3 ≃ simple_line_graph 'K_1,3) /\ ~ inhabited ('K_3 ≃ 'K_1,3).
Proof.
split; first exact: inhabits (diso_comp line_triangle (diso_sym line_claw)).
by case=> h; move: (card_bij (diso_v h)); rewrite card_sum !card_ord.
Qed.

(** Successive line operations: the three-vertex path, then ['K_2], then one isolated vertex, then nothing. *)
Example iterate_path3 :
  [/\ iter 0 simple_line_graph 'K_1,2 = 'K_1,2, inhabited (iter 2 simple_line_graph 'K_1,2 ≃ 'K_1)
    & #|iter 3 simple_line_graph 'K_1,2| = 0].
Proof.
have h2 : iter 2 simple_line_graph 'K_1,2 ≃ 'K_1 := diso_comp (simple_line_graph_diso line_path3) line_K2.
split=> //.
by rewrite iterS card_simple_line_graph (diso_card_edge h2) card_edge_Kn.
Qed.

(** The triangle is a fixed point at every iterate, and the claw reaches it after one step. *)
Example iterate_triangle_claw (n : nat) :
  inhabited (iter n simple_line_graph 'K_3 ≃ 'K_3) /\ inhabited (iter n.+1 simple_line_graph 'K_1,3 ≃ 'K_3).
Proof.
have tri (m : nat) : inhabited (iter m simple_line_graph 'K_3 ≃ 'K_3).
  elim: m => [|m [h]]; first exact: inhabits diso_id.
  exact: inhabits (diso_comp (simple_line_graph_diso h) line_triangle).
split=> //; elim: n => [|n [h]]; first exact: inhabits line_claw.
exact: inhabits (diso_comp (simple_line_graph_diso h) line_triangle).
Qed.

(** Strong edge colouring: the squares of isomorphic line graphs have the same chromatic number. *)
Example claw_triangle_strong_colouring :
  χ([set: graph_power (simple_line_graph 'K_1,3) 2]) = χ([set: graph_power (simple_line_graph 'K_3) 2]).
Proof. exact: chi_graph_power_diso (diso_comp line_claw (diso_sym line_triangle)). Qed.

Print Assumptions line_adjacency.
Print Assumptions edgeless_line_graphs.
Print Assumptions line_not_injective.
Print Assumptions iterate_path3.
Print Assumptions iterate_triangle_claw.
Print Assumptions claw_triangle_strong_colouring.
