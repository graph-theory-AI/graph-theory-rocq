(** * GTBase.orientations — supplied orientations of a simple graph, incoming degrees and proper orientations

    Library migration D11, family [proper-orientations] (meta/library_primitives/proper-orientations.json).  For a
    simple graph [G] and an arbitrary Boolean relation [D : rel G] on its vertices:

    - [orientation_of D]: every arc of [D] joins adjacent vertices and every edge [x -- y] carries exactly one of its
      two arcs, [D x y (+) D y x].  So an orientation has no loop ([orientation_of_noloop]) and no digon
      ([orientation_of_nodigon]); on an edgeless host it is a relation without arcs.
    - [rel_indegree D v]: the number of vertices [u] with an arc [D u v] into [v] (incoming arcs, not outgoing ones; a
      loop [D v v] counts).
    - [proper_indegrees D]: adjacent vertices have different indegrees.  It is a predicate on an arbitrary [D] and
      does NOT assert that [D] is an orientation: a relation with a loop can be proper on its host.
    - [proper_orientation_bound G k]: one [D] is an orientation, has proper indegrees and has every indegree at most
      [k], the three conjuncts in this order.  Empty and edgeless hosts satisfy it at [k = 0] through the empty
      relation ([proper_orientation_bound_edgeless]); it is monotone in [k] with the same [D].

    Chromatic X81's and GTMisc X82's [orientation_of], [indegree], [proper_orientation] and [proper_orientation_bound]
    are these four definitions by conversion.  Distinct and untouched: B16's diGraphType [indeg]
    (Digraph.foundations.degree_balance), arc-set and selection indegrees (Alon-Tarsi [at_indegree], P9
    [arcset_indeg], [selindeg], [x86_sel_indeg]) and Digraph XE2's split pair [xe2_uses_only_edges] /
    [xe2_orients_edge].  Not re-exported by GTBase.base; no conjecture module is imported. *)

From mathcomp Require Import all_boot.
From GraphTheory Require Import preliminaries digraph sgraph.
From GTBase Require Import base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Orientations.
Variable G : sgraph.
Implicit Types (D : rel G) (u v x y : G) (k : nat).

(** Every arc of [D] joins adjacent vertices, and every edge carries exactly one of its two arcs. *)
Definition orientation_of D : Prop :=
  (forall x y : G, D x y -> x -- y) /\
  forall x y : G, x -- y -> (D x y) (+) (D y x).

(** The number of vertices sending an arc of [D] to [v]. *)
Definition rel_indegree D v : nat := #|[set u : G | D u v]|.

(** Adjacent vertices have different indegrees; [D] need not be an orientation. *)
Definition proper_indegrees D : Prop :=
  forall x y : G, x -- y -> rel_indegree D x != rel_indegree D y.

(** Some orientation with proper indegrees has every indegree at most [k]. *)
Definition proper_orientation_bound k : Prop :=
  exists D : rel G,
    orientation_of D /\
    proper_indegrees D /\
    forall v : G, rel_indegree D v <= k.

Lemma orientation_of_edge D x y : orientation_of D -> D x y -> x -- y.
Proof. by case=> + _; apply. Qed.

Lemma orientation_of_xor D x y : orientation_of D -> x -- y -> D x y (+) D y x.
Proof. by case=> _; apply. Qed.

(** On an edge, exactly one direction: [D x y] is the negation of [D y x]. *)
Lemma orientation_of_exclusive D x y : orientation_of D -> x -- y -> D x y = ~~ D y x.
Proof. by move=> oD /(orientation_of_xor oD); case: (D x y); case: (D y x). Qed.

Lemma orientation_of_noloop D x : orientation_of D -> ~~ D x x.
Proof. by move=> oD; apply/negP => /(orientation_of_edge oD); rewrite sg_irrefl. Qed.

Lemma orientation_of_nodigon D x y : orientation_of D -> D x y -> ~~ D y x.
Proof.
by move=> oD Dxy; move: (orientation_of_xor oD (orientation_of_edge oD Dxy)); rewrite Dxy.
Qed.

Lemma in_rel_indegree D u v : (u \in [set w : G | D w v]) = D u v.
Proof. by rewrite inE. Qed.

Lemma rel_indegree0 v : rel_indegree (fun _ _ => false) v = 0.
Proof. by apply/eqP; rewrite cards_eq0; apply/eqP/setP => u; rewrite !inE. Qed.

Lemma rel_indegree_gt0 D v : (0 < rel_indegree D v) = [exists u, D u v].
Proof.
apply/card_gt0P/existsP => [[u]|[u Duv]]; first by rewrite inE; exists u.
by exists u; rewrite inE.
Qed.

(** Without edges, the empty relation is an orientation and every relation has proper indegrees. *)
Lemma orientation_of_edgeless : (forall x y : G, ~~ x -- y) -> orientation_of (fun _ _ => false).
Proof. by move=> nE; split=> x y // xy; move: (nE x y); rewrite xy. Qed.

Lemma proper_indegrees_edgeless D : (forall x y : G, ~~ x -- y) -> proper_indegrees D.
Proof. by move=> nE x y xy; move: (nE x y); rewrite xy. Qed.

Lemma proper_orientation_bound_edgeless : (forall x y : G, ~~ x -- y) -> proper_orientation_bound 0.
Proof.
move=> nE; exists (fun _ _ => false); split; first exact: orientation_of_edgeless.
by split; [exact: proper_indegrees_edgeless | move=> v; rewrite rel_indegree0].
Qed.

(** The same witness bounds every larger [k]. *)
Lemma proper_orientation_bound_mono k k' : k <= k' -> proper_orientation_bound k -> proper_orientation_bound k'.
Proof.
move=> kk' [D [oD [pD bD]]]; exists D; split=> //; split=> // v.
exact: leq_trans (bD v) kk'.
Qed.

End Orientations.

(** An empty host has bound [0]. *)
Lemma proper_orientation_bound_card0 (G : sgraph) : #|G| = 0 -> proper_orientation_bound G 0.
Proof.
move=> G0; apply: proper_orientation_bound_edgeless => x.
by have := card0_eq G0 x; rewrite inE.
Qed.
