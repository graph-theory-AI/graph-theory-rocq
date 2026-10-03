(** Public-only clients of upstream minor_rmap and its presentation adapters. *)
From GTBase Require Import base minor_models.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Example empty_pattern (G : sgraph) :
  minor_rmap (fun _ : 'K_0 => (set0 : {set G})).
Proof. exact: minor_rmap_empty_pattern. Qed.

Example singleton_identity : minor_rmap (fun x : 'K_1 => [set x]).
Proof. exact: minor_rmap_singletons. Qed.

Example edge_identity : minor_rmap (fun x : 'K_2 => [set x]).
Proof. exact: minor_rmap_singletons. Qed.

Example nonempty_pattern_empty_host :
  ~ minor_rmap (fun _ : 'K_1 => (set0 : {set 'K_0})).
Proof. exact: (@not_minor_rmap_empty_host 'K_1 ord0 (fun _ => set0)). Qed.

Example empty_branch_rejected :
  ~ minor_rmap (fun _ : 'K_1 => (set0 : {set 'K_1})).
Proof. by move=> [ne _ _ _]; move: (ne ord0); rewrite eqxx. Qed.

Example overlapping_branches_rejected :
  ~ minor_rmap (fun _ : 'K_2 => [set: 'K_1]).
Proof.
move=> model.
have eq := GraphTheory.core.minor.rmap_disjE model (in_setT ord0) (in_setT ord0).
have bad : (ord0 : 'I_2) = ord_max := eq ord0 ord_max.
by have := congr1 val bad.
Qed.

Definition isolated_pair : sgraph :=
  @SGraph 'I_2 preliminaries.rel0 preliminaries.rel0_sym preliminaries.rel0_irrefl.

Example disconnected_branch_rejected :
  ~ minor_rmap (fun _ : 'K_1 => [set: isolated_pair]).
Proof.
move=> [_ co _ _].
have := co ord0 ord0 ord_max (in_setT _) (in_setT _).
case/connectP => -[|a p] /= pth eq; first by have := congr1 val eq.
by move: pth => /andP[rel _]; move: rel; rewrite /preliminaries.restrict_mem /= !inE /=.
Qed.

(** The host has an edge absent from the supplied pattern. *)
Example extra_host_edges_allowed :
  @minor_rmap 'K_2 isolated_pair (fun h => [set h]).
Proof.
split.
- by move=> x; apply/set0Pn; exists x; rewrite inE.
- by move=> x; exact: (@connected1 'K_2 x).
- by move=> x y xy; rewrite disjoints1 !inE.
- by move=> x y; rewrite /edge_rel /=.
Qed.

Example unused_host_vertices_allowed :
  @minor_rmap 'K_2 'K_1 (fun _ => [set ord0]).
Proof.
split.
- by move=> x; apply/set0Pn; exists ord0; rewrite inE.
- by move=> x; exact: connected1.
- by move=> x y; rewrite !ord1 eqxx.
- by move=> x y; rewrite !ord1 sgP.
Qed.

Example composed_singletons (G : sgraph) :
  minor_rmap (fun x : G => \bigcup_(y in [set x]) [set y]).
Proof. exact: minor_rmap_compose (minor_rmap_singletons G) (minor_rmap_singletons G). Qed.
