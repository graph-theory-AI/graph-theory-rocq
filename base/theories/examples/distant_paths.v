(** * GTBase.examples.distant_paths — public-only client of GTBase.distant_paths (B27)

    Compiles against public modules alone (no conjecture module).  Corner cases: the empty host and the empty and
    singleton families; equal raw duplicates, accepted by the raw relation but never a [uniq] witness; [d = 0] and
    [d = 1] as the same disjointness; [k = 0] and [k = 1] (a one-vertex path between overlapping endpoint sets);
    monotonicity in [d] and restriction of the family; the edge of [K_2], whose two endpoints are distant for [d = 1]
    but not for [d = 2]; and two isolated vertices, whose one-vertex paths satisfy the relation for every [d]. *)

From mathcomp Require Import all_boot.
From GraphTheory Require Import preliminaries digraph sgraph.
From GTBase Require Import base walks_paths balls bag_decompositions distant_paths.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Notation k2_0 := (@Ordinal 2 0 isT).
Local Notation k2_1 := (@Ordinal 2 1 isT).

(** Empty host: the empty family is the only witness. *)
Lemma example_empty_host (d : nat) (X Y : {set 'K_0}) :
  has_k_distant_set_paths d 0 X Y /\ ~ has_k_distant_set_paths d 1 X Y.
Proof.
split; first exact: has_k_distant_set_paths0.
by case/has_k_distant_set_paths1 => -[|x q] //; have := ltn_ord x; rewrite ltn0.
Qed.

(** Empty and singleton families satisfy the raw relation. *)
Lemma example_families (d : nat) (p : seq 'K_2) :
  @pairwise_distant_seqs 'K_2 d [::] /\ pairwise_distant_seqs d [:: p].
Proof. by split; [exact: pairwise_distant_seqs_nil | exact: pairwise_distant_seqs1]. Qed.

(** Equal raw duplicates are ignored by the relation, but the existence wrapper's list is [uniq]. *)
Lemma example_duplicates (d : nat) (p : seq 'K_2) :
  pairwise_distant_seqs d [:: p; p] /\ ~~ uniq [:: p; p].
Proof. by split; [exact: pairwise_distant_seqs_dup | rewrite /= inE eqxx]. Qed.

(** [d = 0] and [d = 1] are the same disjointness condition. *)
Lemma example_d0_d1 (paths : seq (seq 'K_3)) :
  pairwise_distant_seqs 0 paths <-> pairwise_distant_seqs 1 paths.
Proof. exact: pairwise_distant_seqs01. Qed.

(** Overlapping endpoint sets: a one-vertex path is a family of one, at any distance. *)
Lemma example_singleton_path (d : nat) : @has_k_distant_set_paths 'K_2 d 1 [set k2_0] [set k2_0].
Proof. by apply/has_k_distant_set_paths1; exists [:: k2_0]; apply/seq_set_path_seq1; rewrite !inE. Qed.

(** The two endpoints of [K_2]: disjoint ([d = 1]) but adjacent, so not distant for [d = 2]. *)
Lemma example_K2_vertices :
  @pairwise_distant_seqs 'K_2 1 [:: [:: k2_0]; [:: k2_1]] /\
  ~ @pairwise_distant_seqs 'K_2 2 [:: [:: k2_0]; [:: k2_1]].
Proof.
have sv1 (x : 'K_2) : seq_vertices [:: x] = [set x] by apply/setP => y; rewrite in_seq_vertices !inE.
split.
  move=> p q; rewrite !inE => /orP[] /eqP-> /orP[] /eqP-> //= _;
    by rewrite !sv1 set_ball0; apply/disjointP => z; rewrite !inE => /eqP-> /eqP/(congr1 val).
move=> h; have /disjointP /(_ k2_1) := h [:: k2_0] [:: k2_1] isT isT isT; apply.
  rewrite sv1 set_ball1 ballS ball0 !inE; apply/orP; right; apply/bigcupP; exists k2_0; first by rewrite inE.
  by rewrite in_opn.
by rewrite sv1 inE.
Qed.

(** Monotonicity in [d] and restriction of the family. *)
Lemma example_mono_restrict (paths : seq (seq 'K_3)) (p : seq 'K_3) :
  pairwise_distant_seqs 3 (p :: paths) -> pairwise_distant_seqs 1 paths.
Proof.
move=> h; apply: (pairwise_distant_seqs_mono (e := 3)) => //.
by apply: (pairwise_distant_seqs_sub _ h) => q qP; rewrite inE qP orbT.
Qed.

(** Two isolated vertices: every ball is the centre, so the two one-vertex paths qualify for every [d]. *)
Lemma example_disconnected (d : nat) :
  has_k_distant_set_paths d 2 [set: two_isolated] [set: two_isolated].
Proof.
have sv1 (x : two_isolated) : seq_vertices [:: x] = [set x] by apply/setP => y; rewrite in_seq_vertices !inE.
have ballx (r : nat) (x : two_isolated) : ball r x = [set x].
  elim: r => [|r IH]; first exact: ball0.
  rewrite ballS IH big_set1; apply/setP => y; rewrite !inE.
  by case: (y == x).
exists [:: [:: ord0]; [:: ord_max]]; split=> //; split=> //; split.
  by move=> p; rewrite !inE => /orP[] /eqP->; apply/seq_set_path_seq1; rewrite !inE.
move=> p q; rewrite !inE => /orP[] /eqP-> /orP[] /eqP-> //= _;
  by rewrite !sv1 set_ball1 ballx; apply/disjointP => z; rewrite !inE => /eqP-> /eqP/(congr1 val).
Qed.

Print Assumptions example_empty_host.
Print Assumptions example_duplicates.
Print Assumptions example_singleton_path.
Print Assumptions example_K2_vertices.
Print Assumptions example_mono_restrict.
Print Assumptions example_disconnected.
