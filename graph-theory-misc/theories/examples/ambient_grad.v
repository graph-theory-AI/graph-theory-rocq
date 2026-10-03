(** Public-only ambient grad clients. The empty pattern always meets the bound with
    0 <= 0; the empty host has every bound at every radius; the edgeless one-vertex
    host 'K_1 has bound 0 at every radius (hence every bound); 'K_2 has no bound 0 at any
    radius, because the host itself is an ambient shallow minor. *)
From GTBase Require Import base.
From GTMisc.foundations Require Import ambient_shallow_minors.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** A pattern without edges has public edge count 0. *)
Lemma fg_edge_count_edgeless (H : sgraph) :
  (forall x y : H, ~~ x -- y) -> fg_edge_count H = 0.
Proof.
move=> noedge; rewrite /fg_edge_count /GTBase.common.edge_count.
apply/eqP; rewrite cards_eq0; apply/eqP/setP => e; rewrite in_set0.
apply/negbTE/negP => /edgesP[x [y [_ xy]]].
by move: (noedge x y); rewrite xy.
Qed.

Example empty_pattern_bound (G : sgraph) (r d : nat) :
  ambient_shallow_minor G 'K_0 r /\ 2 * fg_edge_count 'K_0 <= d * #|'K_0|.
Proof.
split; first exact: ambient_shallow_minor_empty_pattern.
by rewrite /fg_edge_count (proj1 edge_count_K0_K1) muln0.
Qed.

Example empty_host_grad (r d : nat) : ambient_grad_at_most 'K_0 r d.
Proof.
move=> H model; have noH (h : H) : False := @not_ambient_shallow_minor_empty_host H h r model.
have -> : fg_edge_count H = 0 by apply: fg_edge_count_edgeless => x; case: (noH x).
by rewrite muln0.
Qed.

Example K1_grad_zero (r : nat) : ambient_grad_at_most 'K_1 r 0.
Proof.
move=> H model; rewrite (@fg_edge_count_edgeless H) ?muln0 ?mul0n // => x y.
apply/negP => xy.
have [branch [_ [_ [_ [_ ed]]]]] := proj1 (ambient_shallow_minor_nestedE 'K_1 H r) model.
have [u [v [_ _ uv]]] := ed x y xy.
by rewrite [u]ord1 [v]ord1 sg_irrefl in uv.
Qed.

Example K1_grad (r d : nat) : ambient_grad_at_most 'K_1 r d.
Proof. exact: ambient_grad_at_mostW (leq0n d) (@K1_grad_zero r). Qed.

Example K2_no_grad_zero (r : nat) : ~ ambient_grad_at_most 'K_2 r 0.
Proof.
move=> /ambient_grad_at_most_host.
by rewrite /fg_edge_count edge_count_K2 mul0n muln1.
Qed.

Example grad_restricts_radius (G : sgraph) (d : nat) :
  ambient_grad_at_most G 3 d -> ambient_grad_at_most G 1 d.
Proof. exact: ambient_grad_at_most_radiusW. Qed.

Example grad_bound_on_model (G H : sgraph) (r d : nat) :
  ambient_grad_at_most G r d -> ambient_shallow_minor G H r ->
  2 * fg_edge_count H <= d * #|H|.
Proof. exact: ambient_grad_at_most_bound. Qed.
