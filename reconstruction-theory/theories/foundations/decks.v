(** * Reconstruction.foundations.decks — vertex- and edge-deletion decks of simple graphs

    Family [deletion-decks] (meta/library_primitives/deletion-decks.json): the public canonical vocabulary of the
    deletion decks of reconstruction theory, on simple graphs [sgraph] with isomorphism [≃] ([diso], Type-valued, so
    wrapped in [inhabited]).
    - [vdel_card v] is the card [G - v], the subgraph induced on the vertices other than [v]; [same_deck G H] holds
      when some BIJECTION of the vertex sets matches the cards up to isomorphism, and [reconstructible G] when every
      [H] with the same deck is isomorphic to [G].
    - [same_edge_deck G H] holds when some bijection of the edge sets ([{e : {set G} | e \in E(G)}]) matches the
      edge-deleted cards [del_edge_set G [set e]] (GTBase.common, the canonical single-edge deletion: same vertices,
      that one edge removed) up to isomorphism; [edge_reconstructible G] accordingly.
    The bijection model counts every card with its multiplicity (comparing only the SET of card classes is a
    different, wrong model).  The definitions carry no order or edge-count guard: those belong to the statements
    (the Reconstruction Conjecture asks for at least 3 vertices, the Edge Reconstruction Conjecture for at least 4
    edges).  Directed switching decks (Digraph P9), Seidel switching decks (U11 row 1) and the ell-decks of X21 are
    different models and are not defined here.  The bodies are those of Reconstruction.conjectures.U11, whose five
    names are transparent aliases of these since the deletion-decks library migration. *)

From mathcomp Require Import all_boot.
From GraphTheory Require Import preliminaries digraph sgraph.
From GTBase Require Import base.
Set SsrOldRewriteGoalsOrder.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition vdel_card (G : sgraph) (v : G) : sgraph := induced [set u : G | u != v].

Definition same_deck (G H : sgraph) : Prop :=
  exists f : G -> H,
    bijective f /\
    forall v : G, inhabited (@vdel_card G v ≃ @vdel_card H (f v)).

Definition reconstructible (G : sgraph) : Prop :=
  forall H : sgraph, same_deck G H -> inhabited (G ≃ H).

Definition same_edge_deck (G H : sgraph) : Prop :=
  exists f : {e : {set G} | e \in E(G)} -> {e : {set H} | e \in E(H)},
    bijective f /\
    forall e : {e : {set G} | e \in E(G)},
      inhabited (del_edge_set G [set val e] ≃ del_edge_set H [set val (f e)]).

Definition edge_reconstructible (G : sgraph) : Prop :=
  forall H : sgraph, same_edge_deck G H -> inhabited (G ≃ H).

(** ** Cards *)

(** The card is upstream's [induced [set~ v]], by a proved equation (not assumed convertible). *)
Lemma vdel_cardE (G : sgraph) (v : G) : vdel_card v = induced [set~ v].
Proof. by rewrite /vdel_card; congr induced; apply/setP => u; rewrite !inE. Qed.

Lemma card_vdel_card (G : sgraph) (v : G) : #|vdel_card v| = #|G|.-1.
Proof.
rewrite /vdel_card card_sig -(cardsC1 v); apply: eq_card => u.
by rewrite !inE.
Qed.

(** ** Vertex decks *)

Lemma same_deck_refl (G : sgraph) : same_deck G G.
Proof.
by exists id; split; [exact: id_bij | move=> v; exact: (inhabits diso_id)].
Qed.

(** The index bijection forces equal orders. *)
Lemma same_deck_card (G H : sgraph) : same_deck G H -> #|G| = #|H|.
Proof. by case=> f [bf _]; exact: bij_eq_card bf. Qed.

(** ** Edge decks *)

Lemma same_edge_deck_refl (G : sgraph) : same_edge_deck G G.
Proof.
by exists id; split; [exact: id_bij | move=> e; exact: (inhabits diso_id)].
Qed.

(** The index bijection forces equal edge counts. *)
Lemma same_edge_deck_card_edge (G H : sgraph) : same_edge_deck G H -> #|E(G)| = #|E(H)|.
Proof.
case=> f [bf _].
have h := bij_eq_card bf; rewrite !card_sig in h.
rewrite (eq_card (B := [pred e | e \in E(G)])); last by move=> e; rewrite inE.
rewrite [#|E(H)|](eq_card (B := [pred e | e \in E(H)])); last by move=> e; rewrite inE.
exact: h.
Qed.

(** Any two edgeless graphs, of any orders, have the same (empty) edge deck: the edge-count guard has teeth. *)
Lemma edgeless_same_edge_deck (G H : sgraph) : E(G) = set0 -> E(H) = set0 -> same_edge_deck G H.
Proof.
move=> eG eH.
have noG (e : {e : {set G} | e \in E(G)}) : False by case: e => e; rewrite eG inE.
have noH (e : {e : {set H} | e \in E(H)}) : False by case: e => e; rewrite eH inE.
exists (fun e => match noG e with end); split; last by move=> e; case: (noG e).
by exists (fun e => match noH e with end) => e; [case: (noG e) | case: (noH e)].
Qed.
