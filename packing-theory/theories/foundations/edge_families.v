(** * Indexed families of simple-edge sets

    C4 extracts X15's edge-family contract. Each indexed member is a subset
    of E(G). There is no cover, disjointness, nonemptiness or positive-index
    requirement. Repeated and overlapping members are allowed, and zero
    indices are valid on every graph. The upstream powerset/subset API gives
    the equivalent membership presentation; this wrapper preserves the
    original Prop-valued, ordinal-indexed interface.

    Registry/fidelity: meta/library_primitives/edge-family.json and
    meta/foundation_fidelity/edge-family.json. Public client:
    theories/examples/edge_families.v. Frozen historical bridges:
    theories/migration/edge_families.v and meta/LIBRARY_MIGRATION_C4.md. *)

From GTBase Require Import base common.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition edge_family (G : sgraph) (m : nat) (E : 'I_m -> {set {set G}}) : Prop :=
  forall i : 'I_m, E i \subset E(G).

Section API.
Variables (G : sgraph) (m : nat) (E : 'I_m -> {set {set G}}).

Lemma edge_family_powersetP :
  edge_family E <-> forall i, E i \in powerset E(G).
Proof.
split=> fam i; first by rewrite powersetE; apply: fam.
by have := fam i; rewrite powersetE.
Qed.

Lemma edge_family_member :
  edge_family E -> forall i e, e \in E i -> e \in E(G).
Proof. by move=> fam i e; apply: (subsetP (fam i)). Qed.

Lemma edge_family_subfamily (F : 'I_m -> {set {set G}}) :
  edge_family E -> (forall i, F i \subset E i) -> edge_family F.
Proof. by move=> fam sub i; exact: subset_trans (sub i) (fam i). Qed.

Lemma edge_family_reindex (n : nat) (f : 'I_n -> 'I_m) :
  edge_family E -> edge_family (fun j => E (f j)).
Proof. by move=> fam j; apply: fam. Qed.

Lemma edge_family_unionP :
  edge_family E <-> (\bigcup_i E i) \subset E(G).
Proof.
split=> [fam|/subsetP fam].
- apply/subsetP => e /bigcupP[i _ ei]; exact: (subsetP (fam i) _ ei).
- move=> i; apply/subsetP => e ei; apply: fam.
  by apply/bigcupP; exists i.
Qed.

Lemma not_edge_family_non_edge i e :
  e \in E i -> e \notin E(G) -> ~ edge_family E.
Proof. by move=> ei /negP bad fam; apply: bad; exact: (subsetP (fam i) _ ei). Qed.

End API.

Lemma edge_family0 (G : sgraph) (E : 'I_0 -> {set {set G}}) : edge_family E.
Proof. by move=> i; have := ltn_ord i; rewrite ltn0. Qed.

Lemma edge_family_empty (G : sgraph) (m : nat) :
  edge_family (fun _ : 'I_m => (set0 : {set {set G}})).
Proof. by move=> i; rewrite sub0set. Qed.

Lemma edge_family_full (G : sgraph) (m : nat) :
  edge_family (fun _ : 'I_m => E(G)).
Proof. by move=> i; rewrite subxx. Qed.

(** Two identical, overlapping nonempty members are valid. *)
Lemma edge_family_K2_repeated : edge_family (fun _ : 'I_2 => E('K_2)).
Proof. exact: edge_family_full. Qed.

Lemma K2_repeated_members_overlap : ~ [disjoint E('K_2) & E('K_2)].
Proof.
move/disjointFr=> disj.
have eG : [set: 'K_2] \in E('K_2).
  apply: (perfect_matching_edge perfect_matching_K2).
  by rewrite inE.
by have := disj _ eG; rewrite eG.
Qed.

(** A singleton vertex is not a simple edge. *)
Lemma not_edge_family_loop (G : sgraph) (x : G) :
  ~ edge_family (fun _ : 'I_1 => [set [set x]]).
Proof.
apply: (@not_edge_family_non_edge G 1 _ ord0 [set x]).
- by rewrite inE.
- have -> : [set x] = [set x; x] by rewrite setUid.
  by rewrite in_edges sg_irrefl.
Qed.

(** An empty member is permitted; an empty vertex-set as a member's element
    is not an edge and is rejected, even on a graph with no vertices. *)
Lemma not_edge_family_empty_edge (G : sgraph) :
  ~ edge_family (fun _ : 'I_1 => [set (set0 : {set G})]).
Proof.
apply: (@not_edge_family_non_edge G 1 _ ord0 set0).
- by rewrite inE.
- apply/negP=> /edgesP[x [y [he _]]].
  have : x \in (set0 : {set G}) by rewrite he !inE eqxx.
  by rewrite inE.
Qed.

Print Assumptions edge_family_powersetP.
Print Assumptions edge_family_reindex.
Print Assumptions edge_family_unionP.
Print Assumptions edge_family_K2_repeated.
Print Assumptions not_edge_family_loop.
Print Assumptions not_edge_family_empty_edge.
