(** Public-only clients of [GTBase.matching_graphs]: the empty graph, edgeless graphs, K1
    and K2 are matching graphs, and so is one edge next to an isolated vertex; the path with
    two adjacent edges and K3 are not; every matching graph projects to a forest. *)
From GTBase Require Import base matching_graphs.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** A vertex has at most #|G| - 1 neighbours (no loops). *)
Lemma card_neigh_le (G : sgraph) (x : G) : #|N(x)| <= #|G|.-1.
Proof.
rewrite -(cardsC1 x); apply: subset_leq_card; apply/subsetP => y.
rewrite in_opn !inE => xy; apply/eqP => yx.
by move: xy; rewrite yx sgP.
Qed.

Lemma edgeless_matching_graph (G : sgraph) :
  (forall x y : G, ~~ x -- y) -> matching_graph G.
Proof.
move=> noedge; apply: deg_matching_graph => x.
apply: leq_trans (_ : #|N(x)| <= 0) _ => //; rewrite leqn0 cards_eq0.
by apply/eqP/setP => y; rewrite in_opn inE (negbTE (noedge x y)).
Qed.

Example K0_matching_graph : matching_graph 'K_0.
Proof. by apply: edgeless_matching_graph => -[]. Qed.

Example K1_matching_graph : matching_graph 'K_1.
Proof. by apply: edgeless_matching_graph => x y; rewrite [x]ord1 [y]ord1 sgP. Qed.

Example K2_matching_graph : matching_graph 'K_2.
Proof.
apply: deg_matching_graph => x; apply: leq_trans (card_neigh_le x) _.
by rewrite card_ord.
Qed.

Example K2_forest : is_forest [set: 'K_2].
Proof. exact: matching_graph_forest K2_matching_graph. Qed.

(** One edge 0 -- 1 and the isolated vertex 2. *)
Definition ki_rel (x y : 'I_3) : bool :=
  ((x == 0 :> nat) && (y == 1 :> nat)) || ((x == 1 :> nat) && (y == 0 :> nat)).
Lemma ki_sym : symmetric ki_rel.
Proof. by case=> -[|[|[|//]]] ? [[|[|[|//]]] ?]. Qed.
Lemma ki_irrefl : irreflexive ki_rel.
Proof. by case=> -[|[|[|//]]]. Qed.
Definition edge_and_isolated := SGraph ki_sym ki_irrefl.

Example edge_and_isolated_matching_graph : matching_graph edge_and_isolated.
Proof.
apply: deg_matching_graph => x; apply/card_le1_eqP => y z; rewrite !in_opn.
case: x y z => -[|[|[|//]]] ? [[|[|[|//]]] ?] [[|[|[|//]]] ?] //= _ _; exact: val_inj.
Qed.

(** The path 0 -- 1 -- 2: vertex 1 has two neighbours. *)
Definition p3_rel (x y : 'I_3) : bool := (x.+1 == y :> nat) || (y.+1 == x :> nat).
Lemma p3_sym : symmetric p3_rel.
Proof. by move=> x y; rewrite /p3_rel orbC. Qed.
Lemma p3_irrefl : irreflexive p3_rel.
Proof. by case=> -[|[|[|//]]]. Qed.
Definition P3 := SGraph p3_sym p3_irrefl.

Example P3_not_matching_graph : ~ matching_graph P3.
Proof.
move=> M.
have := @matching_graph_uniq_nb P3 (@Ordinal 3 1 isT) (@Ordinal 3 0 isT) (@Ordinal 3 2 isT) M isT isT.
by move/(congr1 val).
Qed.

Example K3_not_matching_graph : ~ matching_graph 'K_3.
Proof.
move=> M.
have := @matching_graph_uniq_nb 'K_3 (@Ordinal 3 0 isT) (@Ordinal 3 1 isT) (@Ordinal 3 2 isT) M isT isT.
by move/(congr1 val).
Qed.

Example matching_graph_is_forest (G : sgraph) : matching_graph G -> is_forest [set: G].
Proof. exact: matching_graph_forest. Qed.
