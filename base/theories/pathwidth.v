(** * Pathwidth bounds with supplied graph indices

    [pathwidth_at_most G k] asserts that some graph [T] and supplied bags
    [T -> {set G}] form a bag decomposition, [T] is a path tree, and every
    bag has at most [k.+1] vertices. The graph and bag witnesses occur in
    that order. Empty graphs/indices and unused empty bags remain allowed;
    no inhabited-index condition or attained numeric minimum is imposed.

    This combines the faithful B9 [path_tree] and C13 [bag_decomposition]
    contracts. Pinned coq-graph-theory has [sdecomp] over a forest and maximum
    bag-cardinality [width], but no pathwidth predicate. Minor.width_params
    gives treewidth, with the same successor convention and a general forest
    index. Its forest-to-tree construction is neither needed nor duplicated
    here. Treewidth, tree-alpha, layered width, spaghetti decompositions and
    the subgraph-indexed conclusion of X95 retain their separate contracts.

    This focused module is explicitly imported and is not re-exported by
    base, avoiding the base/path_trees dependency cycle. *)
From GTBase Require Import base path_trees bag_decompositions.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition pathwidth_at_most (G : sgraph) (k : nat) : Prop :=
  exists (T : sgraph) (bag : T -> {set G}),
    path_tree T /\ bag_decomposition bag /\
    forall t : T, #|bag t| <= k.+1.

Lemma pathwidth_at_mostI (G T : sgraph) (bag : T -> {set G}) (k : nat) :
  path_tree T -> bag_decomposition bag ->
  (forall t : T, #|bag t| <= k.+1) -> pathwidth_at_most G k.
Proof. by move=> pt dec bound; exists T, bag. Qed.

Lemma pathwidth_at_most_witness (G : sgraph) (k : nat) :
  pathwidth_at_most G k ->
  exists (T : sgraph) (bag : T -> {set G}),
    path_tree T /\ bag_decomposition bag /\
    forall t : T, #|bag t| <= k.+1.
Proof. by []. Qed.

Lemma pathwidth_at_mostW (G : sgraph) (k k' : nat) :
  k <= k' -> pathwidth_at_most G k -> pathwidth_at_most G k'.
Proof.
move=> kk' [T [bag [pt [dec bound]]]]; exists T, bag; split=> //; split=> // t.
by apply: leq_trans (bound t) _; rewrite ltnS.
Qed.

(** A single full bag is a useful general upper bound. *)
Lemma pathwidth_at_most_card (G : sgraph) (k : nat) :
  #|G| <= k.+1 -> pathwidth_at_most G k.
Proof.
move=> sizeG; apply: (@pathwidth_at_mostI G 'K_1 (fun _ => [set: G]) k).
- exact: path_tree_K1.
- split=> [v|]; first by apply/existsP; exists ord0; rewrite inE.
  split=> [x y xy|v]; first by apply/existsP; exists ord0; rewrite !inE.
  have -> : [set t : 'K_1 | v \in [set: G]] = [set ord0].
    by apply/setP => t; rewrite !inE ord1.
  exact: connected1.
- by move=> t; rewrite cardsT.
Qed.

(** Width zero forbids every edge; this is a consequence, not an extra guard. *)
Lemma pathwidth_at_most0_edgeless (G : sgraph) (x y : G) :
  pathwidth_at_most G 0 -> ~~ (x -- y).
Proof.
move=> [T [bag [_ [dec bound]]]]; apply/negP => xy.
have [t [xt yt]] := bag_decomposition_edge dec xy.
have ne : x != y by apply: contraTneq xy => ->; rewrite sgP.
have small : #|[set x; y]| <= #|bag t|.
  by apply: subset_leq_card; rewrite subUset !sub1set xt yt.
by move: (leq_trans small (bound t)); rewrite cards2 ne.
Qed.

(** The empty graph may use the empty index, even at bound zero. *)
Lemma pathwidth_at_most_K0 k : pathwidth_at_most 'K_0 k.
Proof.
apply: (@pathwidth_at_mostI 'K_0 'K_0 (fun _ => set0) k).
- exact: path_tree_K0.
- exact: bag_decomposition_K0.
- by move=> [].
Qed.

Lemma pathwidth_at_most_K1 : pathwidth_at_most 'K_1 0.
Proof. by apply: pathwidth_at_most_card; rewrite card_ord. Qed.

Lemma pathwidth_at_most_K2 : pathwidth_at_most 'K_2 1.
Proof. by apply: pathwidth_at_most_card; rewrite card_ord. Qed.

Lemma not_pathwidth_at_most_K2_0 : ~ pathwidth_at_most 'K_2 0.
Proof.
move=> pw; have := pathwidth_at_most0_edgeless (ord0 : 'K_2) ord_max pw.
by rewrite /edge_rel /=.
Qed.
