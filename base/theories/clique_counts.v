(** * GTBase.clique_counts -- counting the cliques of a finite simple graph

    Three DISTINCT numeric views over upstream [cliques] (GraphTheory.core.coloring) at the full vertex set:
    - [all_clique_count G]: every clique, the empty one included;
    - [nonempty_clique_count G]: the nonempty cliques;
    - [clique_count_size G r]: the cliques of exactly [r] vertices.
    They are different numbers: the empty clique always exists, so [nonempty_clique_count G].+1 is
    [all_clique_count G] ([nonempty_clique_countS]) and [clique_count_size G 0] is 1.  No clique predicate is
    added; each view is related to a corpus comprehension by an unconditional cardinality equality
    ([all_clique_countE], [nonempty_clique_countE], [clique_count_sizeE]), never by an equality between views.
    Registry: meta/library_primitives/clique-count.json (A17). *)
From GTBase Require Import base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section CliqueCounts.
Variable G : sgraph.

(** Every clique of [G], the empty one included. *)
Definition all_clique_count : nat := #|cliques [set: G]|.

(** The nonempty cliques of [G]. *)
Definition nonempty_clique_count : nat := #|[set S in cliques [set: G] | S != set0]|.

(** The cliques of [G] with exactly [r] vertices. *)
Definition clique_count_size (r : nat) : nat := #|[set S in cliques [set: G] | #|S| == r]|.

Lemma in_cliquesT (S : {set G}) : (S \in cliques [set: G]) = cliqueb S.
Proof. by rewrite inE subsetT. Qed.

(** The corpus comprehensions, in their own conjunction order. *)
Lemma all_clique_countE : all_clique_count = #|[set S : {set G} | cliqueb S]|.
Proof. by apply: eq_card => S; rewrite inE in_cliquesT. Qed.

Lemma nonempty_clique_countE :
  nonempty_clique_count = #|[set S : {set G} | cliqueb S && (S != set0)]|.
Proof. by apply: eq_card => S; rewrite !inE subsetT. Qed.

Lemma clique_count_sizeE (r : nat) :
  clique_count_size r = #|[set S : {set G} | (#|S| == r) && cliqueb S]|.
Proof. by apply: eq_card => S; rewrite !inE subsetT andbC. Qed.

(** The empty clique separates the first two views. *)
Lemma nonempty_clique_countS : nonempty_clique_count.+1 = all_clique_count.
Proof.
rewrite /nonempty_clique_count /all_clique_count.
rewrite (cardsD1 set0 (cliques [set: G])) in_cliquesT; have -> : cliqueb (set0 : {set G}).
  by apply/cliqueP; apply: small_clique; rewrite cards0.
by congr (_.+1); apply: eq_card => S; rewrite !inE andbC.
Qed.

Lemma clique_count_size0 : clique_count_size 0 = 1.
Proof.
rewrite /clique_count_size -(cards1 (set0 : {set G})); apply: eq_card => S.
rewrite !inE subsetT cards_eq0 /=; case: (S =P set0) => [->|_]; rewrite ?andbT ?andbF //.
by apply/cliqueP; apply: small_clique; rewrite cards0.
Qed.

Lemma clique_count_size1 : clique_count_size 1 = #|G|.
Proof.
rewrite -cardsT -(card_imset _ (@set1_inj G)) /clique_count_size.
apply: eq_card => S; rewrite !inE subsetT; apply/andP/imsetP => [[_ /cards1P[x ->]]|[x _ ->]].
  by exists x; rewrite ?inE.
by split; [apply/cliqueP; exact: clique1 | rewrite cards1].
Qed.

Lemma clique_count_size2 : clique_count_size 2 = #|E(G)|.
Proof. by rewrite clique_count_sizeE sg_edge_set_cliqueE. Qed.

Lemma clique_count_size_gt (r : nat) : #|G| < r -> clique_count_size r = 0.
Proof.
move=> Gr; apply/eqP; rewrite cards_eq0; apply/eqP/setP => S; rewrite !inE.
by apply/negbTE; rewrite negb_and orbC; apply/orP; left; apply: contraTneq Gr => <-; rewrite -leqNgt max_card.
Qed.

End CliqueCounts.
