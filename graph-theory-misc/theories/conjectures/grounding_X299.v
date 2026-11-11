(** * GTMisc.conjectures.grounding_X299 -- grounding certificates for wave X299 (2026-11-11)

    For the one row (Reed and Seymour's chordal partition question): hyp_inhabited (the row's instance holds at K_3,
    and the statement gives it there) and not_trivially_true (the variant "every graph is chordal" implies the
    statement and is false).  X299 has no helper, so no helper_sanity.
    - [g299_partition G]: the row's property at one graph G (the statement's body, without its quantifier);
    - [g299_singleton]: a chordal graph has the singleton partition (H = G, phi v = [set v]: a single vertex induces
      a connected, bipartite graph, and the quotient is G itself);
    - hyp: K_3 has at most three vertices, so it is chordal (chordal_by_cycles_small);
    - ntt: the 4-cycle 0-1-2-3 of cycle_graph 4 is a chordless genuine cycle of four vertices. *)

From GTBase Require Import base induced_cycles chordal.
From GraphTheory Require Import minor.
From GTMisc.conjectures Require Import X299.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* The row's property at one graph. *)
Definition g299_partition (G : sgraph) : Prop :=
  exists (H : sgraph) (phi : H -> {set G}),
    [/\ minor_rmap phi,
        forall v : G, exists h : H, v \in phi h,
        forall x y : H, x != y -> neighbor (phi x) (phi y) -> x -- y,
        chordal_by_cycles H &
        forall h : H, bipartite (induced (phi h))].

(* A chordal graph has the singleton partition: H = G, phi v = [set v]. *)
Lemma g299_singleton (G : sgraph) : chordal_by_cycles G -> g299_partition G.
Proof.
move=> ch; exists G, (fun v => [set v]); split.
- split.
  + by move=> x; apply/set0Pn; exists x; rewrite inE.
  + by move=> x; exact: connected1.
  + by move=> x y xy; rewrite disjoint_set1l in_set1.
  + move=> x y xy; apply/existsP; exists x; rewrite in_set1 eqxx /=.
    by apply/existsP; exists y; rewrite in_set1 eqxx.
- by move=> v; exists v; rewrite in_set1.
- move=> x y _ /existsP [a /andP [ax /existsP [b /andP [yb ab]]]].
  by move: ax yb; rewrite !in_set1 => /eqP ea /eqP eb; rewrite -ea -eb.
- exact: ch.
- move=> h; exists (fun _ => true) => a b ab; exfalso.
  have := valP a; have := valP b; rewrite !in_set1 => /eqP eb /eqP ea.
  by move: ab; rewrite /edge_rel /= ea eb sgP.
Qed.

(* ** hyp_inhabited: the instance at K_3 (at most three vertices, so chordal: the singleton partition), and the
   statement gives it there. *)
Definition g299_hyp_claim : Prop :=
  g299_partition 'K_3 /\ (reed_seymour_chordal_partition_statement -> g299_partition 'K_3).

Theorem g299_hyp_inhabited : g299_hyp_claim.
Proof.
split; last by move=> S; exact: S.
by apply: g299_singleton; apply: chordal_by_cycles_small; rewrite card_ord.
Qed.

(* ** not_trivially_true: "every graph is chordal" implies the row (singleton partitions) and fails at C_4. *)
Definition g299_all_chordal : Prop := forall G : sgraph, chordal_by_cycles G.

Definition g299_ntt_claim : Prop :=
  ~ g299_all_chordal /\ (g299_all_chordal -> reed_seymour_chordal_partition_statement).

Theorem g299_not_trivially_true : g299_ntt_claim.
Proof.
split; last by move=> V G; exact: g299_singleton (V G).
move=> V.
pose c : seq (cycle_graph 4) := [:: @Ordinal 4 0 isT; @Ordinal 4 1 isT; @Ordinal 4 2 isT; @Ordinal 4 3 isT].
have cc : chordless_cycle c by apply/chordless_cycleP; vm_compute.
by have := V _ c cc.
Qed.
