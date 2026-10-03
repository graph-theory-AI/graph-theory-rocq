(** C15: supplied branch-set models on the same map, frozen at 35b6b165295fb373d864d646d74284c4751dae65.
    Nested conjunctions, disjointness and edge-witness presentations are related
    unconditionally to upstream minor_rmap. Every whole statement retains its
    original guards, quantifier order and conclusion. *)
From GTBase Require Import base minor_models.
From Digraph Require Import prelude digraph dichromatic.
From Digraph.conjectures Require Import two_extremal P9 colouring_variants.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Legacy.
Definition sg_minor_rmap (G H : sgraph) (phi : H -> {set G}) : Prop := [/\ (forall x : H, phi x != set0), (forall x : H, connected (phi x)), (forall x y : H, x != y -> [disjoint phi x & phi y]) & (forall x y : H, x -- y -> exists p : G * G, [/\ p.1 \in phi x, p.2 \in phi y & p.1 -- p.2])].

Definition sg_minor (G H : sgraph) : Prop := exists phi, @Legacy.sg_minor_rmap G H phi.

Definition planar_sg (G : sgraph) : Prop := ~ Legacy.sg_minor G 'K_5 /\ ~ Legacy.sg_minor G 'K_3,3.

Definition conjecture_P : Prop := forall (D : diGraphType) (llD : loopless D), two_extremal llD -> Legacy.planar_sg (underlyingG llD).

Definition large_acyclic_induced_subdigraph_in_a_planar_oriente_statement : Prop := forall (D : diGraphType) (llD : loopless D), (forall u v : D, u --> v -> ~~ (v --> u)) -> Legacy.planar_sg (underlyingG llD) -> exists S : {set D}, acyclicb (induced_digraph S) /\ (3 * #|D| <= 5 * #|S|).

Definition oriented_chromatic_number_of_planar_graphs_statement : Prop := exists M : nat, (forall (D : diGraphType) (llD : loopless D), (forall u v : D, u --> v -> ~~ (v --> u)) -> Legacy.planar_sg (underlyingG llD) -> oriented_kcolouring D M) /\ (exists (D : diGraphType) (llD : loopless D), [/\ (forall u v : D, u --> v -> ~~ (v --> u)), Legacy.planar_sg (underlyingG llD) & ~ oriented_kcolouring D M.-1]).

Definition partitioning_planar_digraphs_statement : Prop := forall (D : diGraphType) (llD : loopless D), (forall u v : D, u --> v -> ~~ (v --> u)) -> Legacy.planar_sg (underlyingG llD) -> exists X : {set D}, acyclicb (induced_digraph X) /\ acyclicb (induced_digraph (~: X)).

Definition oriented_chromatic_planar_bounded_statement : Prop := exists k : nat, forall (D : diGraphType) (llD : loopless D), Legacy.planar_sg (underlyingG llD) -> oriented_kcolouring D k.

End Legacy.

Lemma sg_minor_rmap_compat (G H : sgraph) (phi : H -> {set G}) :
  @Legacy.sg_minor_rmap G H phi <-> @sg_minor_rmap G H phi.
Proof. exact: (iff_sym (@minor_rmap_pairE G H phi)). Qed.

Lemma sg_minor_compat (G H : sgraph) : Legacy.sg_minor G H <-> sg_minor G H.
Proof.
split=> -[phi model]; exists phi.
- exact: (proj1 (@sg_minor_rmap_compat G H phi) model).
- exact: (proj2 (@sg_minor_rmap_compat G H phi) model).
Qed.

Lemma planar_sg_compat (G : sgraph) : Legacy.planar_sg G <-> planar_sg G.
Proof.
split=> -[nk5 nk33]; split=> model.
- apply: nk5; exact: (proj2 (sg_minor_compat G 'K_5) model).
- apply: nk33; exact: (proj2 (sg_minor_compat G 'K_3,3) model).
- apply: nk5; exact: (proj1 (sg_minor_compat G 'K_5) model).
- apply: nk33; exact: (proj1 (sg_minor_compat G 'K_3,3) model).
Qed.

Lemma conjecture_P_compat : Legacy.conjecture_P <-> conjecture_P.
Proof.
split=> statement D llD extremal.
- exact: (proj1 (planar_sg_compat _) (statement D llD extremal)).
- exact: (proj2 (planar_sg_compat _) (statement D llD extremal)).
Qed.

Lemma large_acyclic_induced_subdigraph_in_a_planar_oriente_statement_compat :
  Legacy.large_acyclic_induced_subdigraph_in_a_planar_oriente_statement <->
  large_acyclic_induced_subdigraph_in_a_planar_oriente_statement.
Proof.
split=> statement D llD asym planar; apply: (statement D llD asym).
- exact: (proj2 (planar_sg_compat _) planar).
- exact: (proj1 (planar_sg_compat _) planar).
Qed.

Lemma oriented_chromatic_number_of_planar_graphs_statement_compat :
  Legacy.oriented_chromatic_number_of_planar_graphs_statement <->
  oriented_chromatic_number_of_planar_graphs_statement.
Proof.
split=> -[M [bound [D [llD [asym planar sharp]]]]]; exists M; split.
- move=> D' llD' asym' planar'; apply: (bound D' llD' asym').
  exact: (proj2 (planar_sg_compat _) planar').
- exists D, llD; split=> //; exact: (proj1 (planar_sg_compat _) planar).
- move=> D' llD' asym' planar'; apply: (bound D' llD' asym').
  exact: (proj1 (planar_sg_compat _) planar').
- exists D, llD; split=> //; exact: (proj2 (planar_sg_compat _) planar).
Qed.

Lemma partitioning_planar_digraphs_statement_compat :
  Legacy.partitioning_planar_digraphs_statement <-> partitioning_planar_digraphs_statement.
Proof.
split=> statement D llD asym planar; apply: (statement D llD asym).
- exact: (proj2 (planar_sg_compat _) planar).
- exact: (proj1 (planar_sg_compat _) planar).
Qed.

Lemma oriented_chromatic_planar_bounded_statement_compat :
  Legacy.oriented_chromatic_planar_bounded_statement <-> oriented_chromatic_planar_bounded_statement.
Proof.
split=> -[k bound]; exists k => D llD planar; apply: (bound D llD).
- exact: (proj2 (planar_sg_compat _) planar).
- exact: (proj1 (planar_sg_compat _) planar).
Qed.
