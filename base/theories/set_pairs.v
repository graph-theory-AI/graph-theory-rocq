(** * GTBase.set_pairs -- complete and anticomplete pairs of supplied vertex sets

    Three contracts on two supplied vertex sets [A] and [B] of one simple graph, kept apart:
    - raw anticompleteness, no edge between [A] and [B] and nothing more: upstream [~~ neighbor A B]
      ([GraphTheory.core.sgraph], re-exported by [GTBase.base]), with the bounded-forall view [neighborNP];
    - [anticomplete A B]: disjoint parts with no edge between them, [[disjoint A & B] && ~~ neighbor A B], with the
      [edge -> False] and [~~ edge] Prop views [anticompleteP] and [anticomplete_nonadjP];
    - [complete_between A B]: every vertex of [A] adjacent to every vertex of [B], with the view [complete_betweenP].
      On a simple graph it forces disjointness ([complete_between_disjoint]), so the explicit conjunction
      [[disjoint A & B] /\ ...] is the same contract ([disjoint_complete_betweenP]).
    Empty parts make all three hold, on every carrier; no nonempty, order or unequal-vertex guard is involved.  A shared
    vertex separates them: in [K_1] the singleton is raw anticomplete with itself, but neither [anticomplete] nor
    [complete_between] with itself.  Completeness in [compl G] is raw anticompleteness in [G] only for disjoint parts
    ([complete_between_compl]).  One-set stability ([stable]) and the whole-graph [GTBase.common.complete_bipartite] are
    different contracts.
    Registry: meta/library_primitives/set-pair.json (A21). *)
From GTBase Require Import base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section SetPairs.
Variable G : sgraph.
Implicit Types A B C D : {set G}.

(** Disjoint parts with no edge between them. *)
Definition anticomplete A B : bool := [disjoint A & B] && ~~ neighbor A B.

(** Every vertex of [A] is adjacent to every vertex of [B]. *)
Definition complete_between A B : bool := [forall a in A, [forall b in B, a -- b]].

(** Raw anticompleteness: no supplied cross pair is an edge, and nothing more. *)
Lemma neighborNP A B :
  reflect (forall a b : G, a \in A -> b \in B -> ~~ (a -- b)) (~~ neighbor A B).
Proof.
apply: (iffP negP) => [nn a b aA bB|h /neighborP [a [b [aA bB ab]]]].
  by apply/negP => ab; apply: nn; apply/neighborP; exists a, b.
by move: (h a b aA bB); rewrite ab.
Qed.

Lemma anticompleteP A B :
  reflect ([disjoint A & B] /\ forall a b : G, a \in A -> b \in B -> a -- b -> False) (anticomplete A B).
Proof.
apply: (iffP andP) => [[dAB /neighborNP h]|[dAB h]]; split=> //.
  by move=> a b aA bB ab; move: (h a b aA bB); rewrite ab.
by apply/neighborNP => a b aA bB; apply/negP; exact: h.
Qed.

Lemma anticomplete_nonadjP A B :
  reflect ([disjoint A & B] /\ forall a b : G, a \in A -> b \in B -> ~~ (a -- b)) (anticomplete A B).
Proof. by apply: (iffP andP) => -[dAB /neighborNP h]. Qed.

Lemma complete_betweenP A B :
  reflect (forall a b : G, a \in A -> b \in B -> a -- b) (complete_between A B).
Proof.
apply: (iffP forall_inP) => [h a b aA|h a aA]; first by move/forall_inP: (h a aA); apply.
by apply/forall_inP => b; exact: h.
Qed.

(** Cross completeness forces disjoint parts: a shared vertex would be adjacent to itself. *)
Lemma complete_between_disjoint A B : complete_between A B -> [disjoint A & B].
Proof.
move/complete_betweenP => h; apply/pred0P => x /=; apply/negP => /andP [xA xB].
by move: (h x x xA xB); rewrite sg_irrefl.
Qed.

(** The explicit conjunction with disjointness is the same contract. *)
Lemma disjoint_complete_betweenP A B :
  reflect ([disjoint A & B] /\ forall a b : G, a \in A -> b \in B -> a -- b) (complete_between A B).
Proof.
apply: (iffP idP) => [c|[_ /complete_betweenP //]].
by split; [exact: complete_between_disjoint | apply/complete_betweenP].
Qed.

(** Swapping the parts. *)
Lemma anticompleteC A B : anticomplete A B = anticomplete B A.
Proof. by rewrite /anticomplete disjoint_sym neighborC. Qed.

Lemma complete_betweenC A B : complete_between A B = complete_between B A.
Proof. by apply/complete_betweenP/complete_betweenP => h a b aA bB; rewrite sgP; exact: h. Qed.

(** Restricting the parts. *)
Lemma anticompleteW A B C D : C \subset A -> D \subset B -> anticomplete A B -> anticomplete C D.
Proof.
move=> CA DB /andP [dAB nAB]; apply/andP; split; first exact: disjointWl CA (disjointWr DB dAB).
exact: contra (neighborW G C D A B CA DB) nAB.
Qed.

Lemma complete_betweenW A B C D :
  C \subset A -> D \subset B -> complete_between A B -> complete_between C D.
Proof.
move=> /subsetP CA /subsetP DB /complete_betweenP h; apply/complete_betweenP => a b aC bD.
exact: h (CA a aC) (DB b bD).
Qed.

End SetPairs.

(** Completeness in the complement is raw anticompleteness, for disjoint parts only. *)
Lemma complete_between_compl (G : sgraph) (A B : {set G}) :
  [disjoint A & B] -> @complete_between (compl G) A B = ~~ neighbor A B.
Proof.
move=> dAB; apply/complete_betweenP/neighborNP => h a b aA bB.
  by case/andP: (h a b aA bB).
have ab : a != b by apply: contraTneq bB => <-; rewrite (disjointFr dAB aA).
by rewrite /edge_rel /= ab h.
Qed.
