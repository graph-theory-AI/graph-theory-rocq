(** * GTBase.examples.orientations — public-only client of GTBase.orientations (D11)

    Compiles against GTBase.base and GTBase.orientations alone (no conjecture or migration module).  The empty host
    ['K_0] and the edgeless host ['K_1] have bound 0 through the empty relation; on ['K_2] the single arc [0 -> 1] is
    an orientation whose indegrees are 0 at its tail and 1 at its head (incoming arcs, not outgoing ones), so the bound
    holds at 1 and 2 but not at 0; both arcs together form a digon and are not an orientation; and a loop at [0] gives
    proper indegrees on ['K_2] without being an orientation. *)

From mathcomp Require Import all_boot.
From GraphTheory Require Import preliminaries digraph sgraph.
From GTBase Require Import base orientations.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Notation k2 i := (@Ordinal 2 i isT) (only parsing).

(** The single arc from [0] to [1], both arcs, and a loop at [0]. *)
Definition arc01 : rel 'K_2 := fun x y => (x == k2 0) && (y == k2 1).
Definition both_arcs : rel 'K_2 := fun x y => x != y.
Definition loop0 : rel 'K_2 := fun x y => (x == k2 0) && (y == k2 0).

Lemma K2_vertex (x : 'K_2) : x = k2 0 \/ x = k2 1.
Proof. by case: x => -[|[|//]] Hx; [left | right]; apply: val_inj. Qed.

(** Empty and edgeless hosts: bound 0 through the empty relation. *)
Lemma example_empty_edgeless : proper_orientation_bound 'K_0 0 /\ proper_orientation_bound 'K_1 0.
Proof.
split; first by apply: proper_orientation_bound_card0; rewrite card_ord.
apply: proper_orientation_bound_edgeless => x y.
by rewrite (ord1 x) (ord1 y) sg_irrefl.
Qed.

(** The single arc: an orientation with indegrees 0 (tail) and 1 (head), proper, bound 1 and 2 but not 0. *)
Lemma example_K2_single_arc :
  [/\ orientation_of arc01, rel_indegree arc01 (k2 0) = 0, rel_indegree arc01 (k2 1) = 1,
      proper_indegrees arc01 & proper_orientation_bound 'K_2 1 /\ proper_orientation_bound 'K_2 2].
Proof.
have o : orientation_of arc01.
  split=> [x y /andP[/eqP-> /eqP->] // | x y].
  by case: (K2_vertex x) => ->; case: (K2_vertex y) => ->.
have i0 : rel_indegree arc01 (k2 0) = 0.
  by apply/eqP; rewrite cards_eq0; apply/eqP/setP => u; rewrite !inE /arc01 /= andbF.
have i1 : rel_indegree arc01 (k2 1) = 1.
  rewrite /rel_indegree (_ : [set u | arc01 u (k2 1)] = [set k2 0]) ?cards1 //.
  by apply/setP => u; rewrite !inE /arc01 eqxx andbT.
have p : proper_indegrees arc01.
  move=> x y; case: (K2_vertex x) => ->; case: (K2_vertex y) => -> //; by rewrite i0 i1.
have b1 : proper_orientation_bound 'K_2 1.
  exists arc01; split=> //; split=> // v.
  by case: (K2_vertex v) => ->; rewrite ?i0 ?i1.
by split=> //; split=> //; apply: proper_orientation_bound_mono b1.
Qed.

(** No orientation of ['K_2] has all indegrees 0: the edge's arc enters one endpoint. *)
Lemma example_K2_not_bound0 : ~ proper_orientation_bound 'K_2 0.
Proof.
case=> D [oD [_ bD]]; have e01 : (k2 0 : 'K_2) -- k2 1 := isT.
have [D01 | /negbTE D01] := boolP (D (k2 0) (k2 1)).
  have := bD (k2 1); rewrite leqn0 cards_eq0 => /eqP/setP/(_ (k2 0)).
  by rewrite !inE D01.
have D10 : D (k2 1) (k2 0) by move: (orientation_of_xor oD e01); rewrite D01 addFb.
have := bD (k2 0); rewrite leqn0 cards_eq0 => /eqP/setP/(_ (k2 1)).
by rewrite !inE D10.
Qed.

(** Both arcs of the edge form a digon: not an orientation. *)
Lemma example_K2_both_arcs : ~ orientation_of both_arcs.
Proof. by case=> _ /(_ (k2 0) (k2 1) isT). Qed.

(** A loop at [0]: indegrees 1 and 0 differ on the edge, so proper, but a loop is no orientation. *)
Lemma example_K2_proper_loop : proper_indegrees loop0 /\ ~ orientation_of loop0.
Proof.
have i0 : rel_indegree loop0 (k2 0) = 1.
  rewrite /rel_indegree (_ : [set u | loop0 u (k2 0)] = [set k2 0]) ?cards1 //.
  by apply/setP => u; rewrite !inE /loop0 eqxx andbT.
have i1 : rel_indegree loop0 (k2 1) = 0.
  by apply/eqP; rewrite cards_eq0; apply/eqP/setP => u; rewrite !inE /loop0 /= andbF.
split; first by move=> x y; case: (K2_vertex x) => ->; case: (K2_vertex y) => -> //; rewrite i0 i1.
by move/orientation_of_noloop => /(_ (k2 0)).
Qed.

Print Assumptions example_empty_edgeless.
Print Assumptions example_K2_single_arc.
Print Assumptions example_K2_not_bound0.
Print Assumptions example_K2_both_arcs.
Print Assumptions example_K2_proper_loop.
