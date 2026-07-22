(** * Infinite.conjectures.D4legacy -- legacy D4 gate-completeness surface

    Two blocked definitions are re-exported from [D4_unblocked].  The two
    Hamilton-circle rows below remain PARTIAL: a Hamilton circle in the
    Freudenthal compactification is represented by the existing spanning
    double-ray proxy from [D4inf3].  The definitions make the partial legs real
    and gateable; they do not claim to close the deferred topology layer. *)

From mathcomp Require Import all_boot all_algebra.
From Infinite Require Import foundations.igraph.
From Infinite.conjectures Require Export D4_unblocked D4inf3 grounding_D4inf3.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Record iedge_vertex (G : iGraph) := IEdgeVertex {
  iev_src : iV G;
  iev_dst : iV G;
  iev_edge : iadj iev_src iev_dst
}.

Definition iline_adj (G : iGraph) (e f : iedge_vertex G) : Prop :=
  e <> f /\
  (iev_src e = iev_src f \/ iev_src e = iev_dst f \/
   iev_dst e = iev_src f \/ iev_dst e = iev_dst f).

Lemma iline_adj_sym (G : iGraph) : irel_sym (@iline_adj G).
Proof.
move=> e f [ne share]; split.
- by move=> eq; apply: ne; symmetry.
- case: share => [h | [h | [h | h]]].
  + by left; symmetry.
  + by right; right; left; symmetry.
  + by right; left; symmetry.
  + by right; right; right; symmetry.
Qed.

Lemma iline_adj_irr (G : iGraph) : irel_irr (@iline_adj G).
Proof. by move=> e [ne _]; apply: ne. Qed.

Definition iline_graph (G : iGraph) : iGraph :=
  Build_iGraph (@iline_adj_sym G) (@iline_adj_irr G).

Definition i_connected (G : iGraph) : Prop :=
  connected_set (G := G) (fun _ => True).

Definition i_vertex_connected_at_least (k : nat) (G : iGraph) : Prop :=
  (exists vertices : 'I_k -> iV G, injective vertices) /\
  forall (m : nat) (cut : 'I_m -> iV G),
    m < k -> connected_set (G := G) (fun v => forall i, v <> cut i).

Definition i_edge_connected_at_least (k : nat) (G : iGraph) : Prop :=
  i_vertex_connected_at_least k (iline_graph G).

Definition i_hamilton_circle_proxy (G : iGraph) : Prop :=
  exists d : int -> iV G, spanning_dray (G := G) d.

(** Partial double-ray rendering of the two OPG line-graph clauses.

    The [infinite_graph G] guard is LOAD-BEARING (audit fix 2026-07-22): the
    double-ray proxy demands an INJECTIVE [int]-indexed ray, so any finite
    carrier refutes an unguarded clause (machine-checked at K_1 for the powers
    row), while the source conjectures hold on finite graphs via ordinary
    Hamilton cycles — the honest proxy domain is the infinite case, which is
    also where the conjectures live.  Second documented proxy axis: the
    edge-connectivity hypothesis is rendered as vertex-connectivity of the line
    graph (kappa(L(G)) >= 4), classically implied by lambda(G) >= 4; a genuine
    edge-deletion connectivity notion is part of the deferred layer. *)
Definition hamiltonian_cycles_in_line_graphs_of_infinite_graphs_statement : Prop :=
  (forall G : iGraph,
      infinite_graph G ->
      locally_finite G ->
      i_edge_connected_at_least 4 G ->
      i_hamilton_circle_proxy (iline_graph G)) /\
  (forall G : iGraph,
      infinite_graph G ->
      locally_finite G ->
      i_vertex_connected_at_least 4 (iline_graph G) ->
      i_hamilton_circle_proxy (iline_graph G)).

(** Partial double-ray rendering of the countable cube/square clauses (same
    load-bearing [infinite_graph] guard as above; without it K_1 refutes the
    cube clause axiom-free). *)
Definition hamiltonian_cycles_in_powers_of_infinite_graphs_statement : Prop :=
  (forall G : iGraph,
      infinite_graph G ->
      countable_graph G -> i_connected G ->
      i_hamilton_circle_proxy (ipow 3 G)) /\
  (forall G : iGraph,
      infinite_graph G ->
      countable_graph G -> i_vertex_connected_at_least 2 G ->
      i_hamilton_circle_proxy (ipow 2 G)).
