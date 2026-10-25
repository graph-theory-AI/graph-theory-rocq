(** Witness hint (Any-lane guard, 2026-10-25): an axiom-free REFUTATION of
    [Reconstruction.conjectures.X21.nydl_tree_l_deck_reconstruction_statement] as encoded before
    its [ell <= n] guard (corpus row studies:std_n_dl_s_conjecture_deck_reconstruction_of_trees).

    The threshold hypothesis floor(n/2) + 1 <= ell does not bound ell by n.  Above the vertex
    count the ell-deck index type is empty, so [x21_same_l_deck] holds with the empty bijection
    and the body claims that any two trees on n vertices are isomorphic.  At n = 4, ell = 5 the
    claw K_1,3 and the path P_4 refute it: both are trees on four vertices, and the claw's centre
    is adjacent to the three other vertices while no vertex of P_4 is.  P_4 is built from the
    edgeless graph by adding edges between vertices in different components
    ([add_edge_is_forest]).  With the guard [ell <= n] this file no longer compiles
    (hint-stale-FIX-OK). *)
From mathcomp Require Import all_boot.
From GraphTheory Require Import preliminaries digraph sgraph.
From GTBase Require Import base path_trees trees.
From Reconstruction.conjectures Require Import X21.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


(* Above the vertex count the ell-deck is empty, so any two graphs of that size share it. *)
Lemma deck_index_empty (G : sgraph) (ell : nat) :
  #|G| < ell -> x21_l_deck_index G ell -> False.
Proof.
move=> lt [S /eqP cS]; move: (max_card (mem S)); rewrite cS => le.
by move: (leq_ltn_trans le lt); rewrite ltnn.
Qed.

Lemma same_deck_above (G H : sgraph) (ell : nat) :
  #|G| < ell -> #|H| < ell -> x21_same_l_deck G H ell.
Proof.
move=> ltG ltH.
exists (fun S => False_rect _ (deck_index_empty ltG S)); split.
  exists (fun S => False_rect _ (deck_index_empty ltH S)) => S.
    by case: (deck_index_empty ltG S).
  by case: (deck_index_empty ltH S).
by move=> S; case: (deck_index_empty ltG S).
Qed.

(* A set closed under the edges separates its members from the other vertices. *)
Lemma not_connect_closed (G : sgraph) (a : pred G) (x y : G) :
  (forall u v : G, u -- v -> a u = a v) -> a x -> ~~ a y -> ~~ connect (--) x y.
Proof.
move=> cl ax nay; apply/negP => cxy.
have cla : closed (--) a by move=> u v /cl.
by move: (closed_connect cla cxy); rewrite !unfold_in ax (negbTE nay).
Qed.

(* The path 0 - 1 - 2 - 3, a tree built from the edgeless graph by adding edges between
   vertices in different components. *)
Definition e4_rel : rel 'I_4 := fun _ _ => false.
Lemma e4_sym : symmetric e4_rel. Proof. by []. Qed.
Lemma e4_irrefl : irreflexive e4_rel. Proof. by []. Qed.
Definition E4 : sgraph := SGraph e4_sym e4_irrefl.

Lemma E4_forest : is_forest [set: E4].
Proof. by apply/linear_forest_forest/linear_forest_edgeless. Qed.

Definition F0 : forest := Forest E4_forest.
Definition v0 : 'I_4 := ord0.
Definition v1 : 'I_4 := Ordinal (isT : 1 < 4).
Definition v2 : 'I_4 := Ordinal (isT : 2 < 4).
Definition v3 : 'I_4 := Ordinal (isT : 3 < 4).

Lemma F1_forest : is_forest [set: @add_edge F0 v0 v1].
Proof.
by apply: add_edge_is_forest; apply: (@not_connect_closed F0 (fun v => v == v0)).
Qed.
Definition F1 : forest := Forest F1_forest.

Lemma F2_forest : is_forest [set: @add_edge F1 v1 v2].
Proof.
apply: add_edge_is_forest; apply: (@not_connect_closed F1 (fun v : 'I_4 => val v < 2)) => //.
try by move=> [[|[|[|[|u]]]] hu] [[|[|[|[|w]]]] hw].
Qed.
Definition F2 : forest := Forest F2_forest.

Lemma F3_forest : is_forest [set: @add_edge F2 v2 v3].
Proof.
apply: add_edge_is_forest; apply: (@not_connect_closed F2 (fun v : 'I_4 => val v < 3)) => //.
try by move=> [[|[|[|[|u]]]] hu] [[|[|[|[|w]]]] hw].
Qed.

Definition P4 : sgraph := @add_edge F2 v2 v3.

Lemma P4_edge (u w : P4) : u -- w = ((val u).+1 == val w) || ((val w).+1 == val u).
Proof. by move: u w => [[|[|[|[|u]]]] hu] [[|[|[|[|w]]]] hw]. Qed.

Lemma is_tree_P4 : is_tree [set: P4].
Proof.
apply: is_treeTI; first exact: F3_forest.
have c0 : forall u : P4, connect (--) (v0 : P4) u.
  have e01 : (v0 : P4) -- v1 by rewrite P4_edge.
  have e12 : (v1 : P4) -- v2 by rewrite P4_edge.
  have e23 : (v2 : P4) -- v3 by rewrite P4_edge.
  have c1 : connect (--) (v0 : P4) v1 by exact: connect1.
  have c2 : connect (--) (v0 : P4) v2 by exact: connect_trans c1 (connect1 e12).
  have c3 : connect (--) (v0 : P4) v3 by exact: connect_trans c2 (connect1 e23).
  move=> u; have hu : [|| u == v0, u == v1, u == v2 | u == v3] by case: u => [[|[|[|[|u]]]] hu].
  by case/or4P: hu => /eqP ->; rewrite ?connect0.
apply: connectedTI => x y; apply: connect_trans (c0 y).
by rewrite connect_symI //; exact: sg_sym.
Qed.

Lemma card_P4 : #|P4| = 4. Proof. exact: card_ord. Qed.
Lemma card_claw : #|'K_1,3| = 4. Proof. by rewrite card_sum !card_ord. Qed.

(* No vertex of P4 is adjacent to all three others. *)
Lemma P4_no_centre (u : P4) : exists2 w : P4, w != u & ~~ (u -- w).
Proof.
move: u => [[|[|[|[|u]]]] hu] //.
- by exists v2; rewrite // P4_edge.
- by exists v3; rewrite ?P4_edge //; apply/eqP => /(congr1 val).
- by exists v0; rewrite ?P4_edge //; apply/eqP => /(congr1 val).
- by exists v1; rewrite ?P4_edge //; apply/eqP => /(congr1 val).
Qed.

Lemma claw_not_P4 : ~ inhabited ('K_1,3 ≃ P4).
Proof.
case=> h; set c : 'K_1,3 := inl ord0.
have [w wn nadj] := P4_no_centre (bij.bij_fwd h c).
move: nadj wn; rewrite -[w](bij.bijK' h) edge_diso.
case: (bij.bij_bwd h w) => [o|i]; first by rewrite (claw_centre o) eqxx.
by rewrite claw_adj_cl.
Qed.

Lemma refuted : ~ nydl_tree_l_deck_reconstruction_statement.
Proof.
move=> /(_ 4 5 'K_1,3 P4 isT isT card_claw card_P4 is_tree_claw is_tree_P4).
by move=> /(_ (same_deck_above _ _)) h; apply: claw_not_P4; apply: h; rewrite ?card_claw ?card_P4.
Qed.

Print Assumptions refuted.
