(** * GTBase.simple_edges -- reusable finite simple-edge vocabulary *)

From mathcomp Require Import all_boot.
From GraphTheory Require Import digraph sgraph.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Undirected edges represented as two-element vertex sets.  This is a thin,
    computational adapter around upstream [sg_edge_set]; irreflexivity rules
    out singleton endpoint sets. *)
Definition simple_edge_set (G : sgraph) : {set {set G}} :=
  [set e : {set G} |
      [exists x : G, [exists y : G, (x -- y) && (e == [set x; y])]]].

Lemma adjacent_neq (G : sgraph) (x y : G) : x -- y -> x != y.
Proof. by move=> xy; rewrite (sg_edgeNeq xy). Qed.

Lemma simple_edge_setE (G : sgraph) : simple_edge_set G = sg_edge_set G.
Proof.
apply/setP=> e; apply/idP/idP.
- rewrite /simple_edge_set inE.
  move/existsP=> [x]; move/existsP=> [y]; move/andP=> [xy /eqP ->].
  by rewrite in_edges.
- move/edgesP=> [x [y [-> xy]]].
  rewrite /simple_edge_set inE.
  apply/existsP; exists x; apply/existsP; exists y.
  by rewrite xy eqxx.
Qed.

Lemma simple_edge_setP (G : sgraph) (e : {set G}) :
  reflect (exists x y : G, e = [set x; y] /\ x -- y)
          (e \in simple_edge_set G).
Proof. by rewrite simple_edge_setE; exact: edgesP. Qed.

Lemma simple_edge_mem (G : sgraph) (x y : G) :
  ([set x; y] \in simple_edge_set G) = (x -- y).
Proof. by rewrite simple_edge_setE in_edges. Qed.

(** Equivalent characterization used by two legacy conjecture files. *)
Lemma simple_edge_set_cliqueE (G : sgraph) :
  simple_edge_set G = [set e : {set G} | (#|e| == 2) && cliqueb e].
Proof.
apply/setP=> e; rewrite /simple_edge_set !inE.
apply/existsP/andP.
- move=> [x]; move/existsP=> [y]; move/andP=> [xy /eqP ->].
  split; first by rewrite cards2 (sg_edgeNeq xy).
  apply/cliqueP=> u v /set2P[]-> /set2P[]-> //;
    rewrite ?eqxx // => _; by rewrite sgP.
- move=> [/cards2P [x [y [xDy ->]]] /cliqueP clique_xy].
  exists x; apply/existsP; exists y; apply/andP; split.
  + have x_in : x \in [set x; y] by rewrite !inE eqxx.
    have y_in : y \in [set x; y] by rewrite !inE eqxx orbT.
    exact: clique_xy x_in y_in xDy.
  + by rewrite eqxx.
Qed.

Definition simple_edge_incident
    (G : sgraph) (v : G) (e : {set G}) : bool :=
  (e \in simple_edge_set G) && (v \in e).

Lemma simple_edge_incidentE (G : sgraph) (v : G) (e : {set G}) :
  e \in simple_edge_set G ->
  simple_edge_incident v e = (v \in e).
Proof. by move=> edge_e; rewrite /simple_edge_incident edge_e. Qed.

Definition simple_edge_count (G : sgraph) : nat := #|simple_edge_set G|.

Definition delete_edges_rel
    (G : sgraph) (F : {set {set G}}) : rel G :=
  fun x y => (x -- y) && ([set x; y] \notin F).

Lemma delete_edges_rel_sym (G : sgraph) (F : {set {set G}}) :
  symmetric (@delete_edges_rel G F).
Proof. by move=> x y; rewrite /delete_edges_rel sgP setUC. Qed.

Lemma delete_edges_rel_irrefl (G : sgraph) (F : {set {set G}}) :
  irreflexive (@delete_edges_rel G F).
Proof. by move=> x; rewrite /delete_edges_rel sg_irrefl. Qed.

Definition delete_edges_graph
    (G : sgraph) (F : {set {set G}}) : sgraph :=
  SGraph (@delete_edges_rel_sym G F) (@delete_edges_rel_irrefl G F).

Definition delete_edge_graph (G : sgraph) (e : {set G}) : sgraph :=
  delete_edges_graph [set e].

Lemma delete_edges_graphE
    (G : sgraph) (F : {set {set G}}) (x y : G) :
  @sedge (delete_edges_graph F) x y =
    (x -- y) && ([set x; y] \notin F).
Proof. by []. Qed.

Lemma delete_edge_graphE (G : sgraph) (e : {set G}) (x y : G) :
  @sedge (delete_edge_graph e) x y =
    (x -- y) && ([set x; y] != e).
Proof. by rewrite /delete_edge_graph delete_edges_graphE inE. Qed.

Lemma delete_edge_removes (G : sgraph) (e : {set G}) (x y : G) :
  e = [set x; y] ->
  ~~ @sedge (delete_edge_graph e) x y.
Proof. by move=> ->; rewrite delete_edge_graphE eqxx andbF. Qed.

Lemma delete_edge_preserves_other
    (G : sgraph) (e : {set G}) (x y : G) :
  [set x; y] != e ->
  @sedge (delete_edge_graph e) x y = (x -- y).
Proof. by move=> other; rewrite delete_edge_graphE other andbT. Qed.

(** Small-model grounding for all degenerate cases in this API. *)
Lemma simple_edge_count_K0 : simple_edge_count 'K_0 = 0.
Proof. by rewrite /simple_edge_count simple_edge_setE card_edge_Kn. Qed.

Lemma simple_edge_count_K1 : simple_edge_count 'K_1 = 0.
Proof. by rewrite /simple_edge_count simple_edge_setE card_edge_Kn. Qed.

Lemma simple_edge_count_K2 : simple_edge_count 'K_2 = 1.
Proof. by rewrite /simple_edge_count simple_edge_setE card_edge_Kn. Qed.

Lemma simple_edge_count_K3 : simple_edge_count 'K_3 = 3.
Proof. by rewrite /simple_edge_count simple_edge_setE card_edge_Kn. Qed.
