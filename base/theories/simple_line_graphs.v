(** * GTBase.simple_line_graphs -- the line graph of a finite simple graph on its edge-set subtype

    [simple_line_graph G] has as vertices the edges of [G], as the subtype [{e : {set G} | e \in E(G)}] of their
    endpoint sets, two of them adjacent iff they are distinct and share an endpoint:
    [(val e != val f) && (val e :&: val f != set0)].  It is an iterable [sgraph -> sgraph] map.  Isolated vertices
    of [G] disappear and the operation is not injective (the triangle and the claw have the same line graph).  It
    is neither GTBase.base's multigraph [line_graph] (one vertex per labelled edge, parallel edges kept) nor
    upstream's directed [mgraph.line_graph].
    API: the adjacency view and #|E(G)| vertices, functoriality on isomorphisms ([simple_line_graph_diso], promoted
    from Reconstruction's Kelly development), complete line graphs when any two edges meet
    ([simple_line_graph_complete]), and the square's chromatic-number transport ([graph_power_diso],
    [chi_graph_power_diso]).
    Registry: meta/library_primitives/simple-line-graph.json (A25). *)
From GTBase Require Import base common.
From GraphTheory Require Import preliminaries bij digraph sgraph.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section SimpleLineGraph.
Variable G : sgraph.

(** The vertices: the edges of [G], as the subtype of [E(G)]. *)
Definition simple_line_vertex : Type := {e : {set G} | e \in E(G)}.

(** Two edges are adjacent iff they are distinct and share an endpoint. *)
Definition simple_line_rel : rel simple_line_vertex :=
  fun e f => (val e != val f) && (val e :&: val f != set0).

Lemma simple_line_sym : symmetric simple_line_rel.
Proof. by move=> e f; rewrite /simple_line_rel eq_sym setIC. Qed.

Lemma simple_line_irrefl : irreflexive simple_line_rel.
Proof. by move=> e; rewrite /simple_line_rel eqxx. Qed.

Definition simple_line_graph : sgraph := SGraph simple_line_sym simple_line_irrefl.

Lemma simple_line_edgeE (e f : simple_line_graph) : e -- f = (val e != val f) && (val e :&: val f != set0).
Proof. by []. Qed.

Lemma card_simple_line_graph : #|simple_line_graph| = #|E(G)|.
Proof. by rewrite card_sig. Qed.

End SimpleLineGraph.

(** ** Functoriality on isomorphisms *)

Section SimpleLineGraphDiso.
Variables (G H : sgraph) (h : diso G H).

Lemma simple_line_edge_diso (f : {set G}) : f \in E(G) -> h @: f \in E(H).
Proof.
case/edgesP => x [y] [-> xy]; rewrite imsetU1 imset_set1 in_edges.
by rewrite (edge_diso h).
Qed.

Lemma simple_line_edge_inv_diso (f : {set H}) : f \in E(H) -> h^-1 @: f \in E(G).
Proof.
case/edgesP => x [y] [-> xy]; rewrite imsetU1 imset_set1 in_edges.
by rewrite (edge_diso' h).
Qed.

Lemma simple_line_imsetK (A : {set G}) : h^-1 @: (h @: A) = A.
Proof.
apply/setP => x; apply/idP/idP.
- by case/imsetP => y /imsetP[z zA ->] ->; rewrite bijK.
- by move=> xA; rewrite -(bijK h x); exact: imset_f _ (imset_f _ xA).
Qed.

Lemma simple_line_imset_invK (A : {set H}) : h @: (h^-1 @: A) = A.
Proof.
apply/setP => x; apply/idP/idP.
- by case/imsetP => y /imsetP[z zA ->] ->; rewrite bijK'.
- by move=> xA; rewrite -(bijK' h x); exact: imset_f _ (imset_f _ xA).
Qed.

Definition simple_line_map (a : simple_line_graph G) : simple_line_graph H :=
  Sub (h @: val a) (simple_line_edge_diso (valP a)).

Definition simple_line_unmap (a : simple_line_graph H) : simple_line_graph G :=
  Sub (h^-1 @: val a) (simple_line_edge_inv_diso (valP a)).

Lemma simple_line_mapK : cancel simple_line_map simple_line_unmap.
Proof. by move=> a; apply: val_inj; rewrite /= simple_line_imsetK. Qed.

Lemma simple_line_unmapK : cancel simple_line_unmap simple_line_map.
Proof. by move=> a; apply: val_inj; rewrite /= simple_line_imset_invK. Qed.

Lemma simple_line_map_mono : {mono simple_line_map : a b / a -- b}.
Proof.
have inj_h : injective h := @bij_injective _ _ (diso_v h).
move=> a b; rewrite !simple_line_edgeE /= -(imsetI (fun x y _ _ => inj_h x y)).
by rewrite (inj_eq (imset_inj inj_h)) imset_eq0.
Qed.

End SimpleLineGraphDiso.

Lemma simple_line_graph_diso (G H : sgraph) : G ≃ H -> simple_line_graph G ≃ simple_line_graph H.
Proof. move=> h; exact: Diso' (@simple_line_mapK _ _ h) (@simple_line_unmapK _ _ h) (@simple_line_map_mono _ _ h). Qed.

(** If any two edges of [G] meet (a star, a triangle), its line graph is complete. *)
Lemma simple_line_graph_complete (G : sgraph) (n : nat) :
  {in E(G) &, forall e f, e :&: f != set0} -> #|E(G)| = n -> simple_line_graph G ≃ 'K_n.
Proof.
move=> meet <-; rewrite -card_simple_line_graph; apply: diso_Kn => a b ab.
by rewrite simple_line_edgeE val_eqE ab /=; apply: meet; apply: valP.
Qed.

(** ** Squares and chromatic numbers move along isomorphisms *)

Section PowerDiso.
Variables (G H : sgraph) (h : diso G H).

Lemma diso_imset_mem (A : {set G}) (y : H) : (y \in h @: A) = (h^-1 y \in A).
Proof.
apply/imsetP/idP => [[z zA ->]|yA]; first by rewrite bijK.
by exists (h^-1 y); rewrite ?bijK'.
Qed.

Lemma diso_open_neigh (z : G) : N(h z) = h @: N(z).
Proof. by apply/setP => y; rewrite diso_imset_mem !in_opn -(edge_diso h) bijK'. Qed.

Lemma diso_ball (k : nat) (x : G) : ball k (h x) = h @: ball k x.
Proof.
elim: k => [|k IH]; first by rewrite !ball0 imset_set1.
rewrite !ballS IH imsetU; congr (_ :|: _).
apply/setP => y; apply/bigcupP/imsetP => [[z /imsetP[w wB ->] yN]|[u /bigcupP[w wB uN] ->]].
  rewrite diso_open_neigh in yN; case/imsetP: yN => u uN ->.
  by exists u => //; apply/bigcupP; exists w.
by exists (h w); [exact: imset_f | rewrite diso_open_neigh; exact: imset_f].
Qed.

End PowerDiso.

Lemma graph_power_diso (G H : sgraph) (m : nat) : G ≃ H -> graph_power G m ≃ graph_power H m.
Proof.
move=> h; have inj_h : injective h := @bij_injective _ _ (diso_v h).
apply: (@Diso' (graph_power G m) (graph_power H m) h h^-1 (bijK h) (bijK' h)) => x y.
by rewrite /edge_rel /= /pow_rel /reach_le (inj_eq inj_h) !diso_ball !(mem_imset _ _ inj_h).
Qed.

(** The chromatic number of the square, e.g. of a line graph (strong edge colouring), along an isomorphism. *)
Lemma chi_graph_power_diso (G H : sgraph) (m : nat) : G ≃ H -> χ([set: graph_power G m]) = χ([set: graph_power H m]).
Proof. by move=> h; apply: chi_diso; exact: graph_power_diso. Qed.
