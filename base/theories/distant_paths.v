(** * GTBase.distant_paths — supplied families of pairwise distant vertex sequences

    Library migration B27, family [distant-paths] (meta/library_primitives/distant-paths.json).  Two public contracts
    over a supplied list [paths : seq (seq G)] and a distance parameter [d]:

    - [pairwise_distant_seqs d paths]: for every two UNEQUAL sequence values [p != q] of the list, the closed
      [d.-1]-ball around the support of [p] ([set_ball], GTBase.balls, over [seq_vertices], GTBase.walks_paths) misses
      the support of [q].  Equal duplicates in the list are ignored, and nothing requires pathhood, uniqueness or a
      nonempty sequence.  [d = 0] and [d = 1] both mean disjoint supports ([pairwise_distant_seqs0]), and a larger
      [d] is stronger ([pairwise_distant_seqs_mono]).  [pairwise_distant_seqsP] is the unconditional bridge to the
      presentation that also asks for disjoint supports: that conjunct is redundant because every seed set lies in
      its closed ball ([set_ball_sub]).
    - [has_k_distant_set_paths d k X Y]: some supplied list has exactly [k] entries, no repeated entry ([uniq]), every
      entry a set-to-set simple path ([seq_set_path X Y]) and is [pairwise_distant_seqs d]; [has_k_distant_set_pathsP]
      is the same bridge for the existence form.  [k = 0] always holds (the empty list); [k = 1] is the existence of
      one [X]-[Y] path, a one-vertex path when [X] and [Y] meet.

    Closed balls never leave a component, so supports in different components satisfy the relation for every
    [d]; no comparison with a truncated graph distance is made.  Distinct and untouched: X113's distant cycles (radius
    [d], not [d.-1]) and X146's A-path existence chain (distinct endpoints in [A], internal avoidance).  Not
    re-exported by GTBase.base; no conjecture module is imported. *)

From mathcomp Require Import all_boot.
From GraphTheory Require Import preliminaries digraph sgraph.
From GTBase Require Import base walks_paths balls.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section DistantPaths.
Variable G : sgraph.
Implicit Types (X Y : {set G}) (p q : seq G) (paths : seq (seq G)).

(** For unequal sequence values of the family, the closed [d.-1]-ball around one support misses the other. *)
Definition pairwise_distant_seqs (d : nat) paths : Prop :=
  forall p q : seq G, p \in paths -> q \in paths -> p != q ->
    [disjoint set_ball d.-1 (seq_vertices p) & seq_vertices q].

(** Exactly [k] distinct set-to-set simple paths from [X] to [Y] whose unequal values are
    [pairwise_distant_seqs d]. *)
Definition has_k_distant_set_paths (d k : nat) X Y : Prop :=
  exists paths : seq (seq G),
    size paths = k /\
    uniq paths /\
    (forall p : seq G, p \in paths -> seq_set_path X Y p) /\
    pairwise_distant_seqs d paths.

(** The presentation with an additional support-disjointness conjunct is equivalent, without premises. *)
Lemma pairwise_distant_seqsP (d : nat) paths :
  (forall p q : seq G, p \in paths -> q \in paths -> p != q ->
     [disjoint seq_vertices p & seq_vertices q] /\
     [disjoint set_ball d.-1 (seq_vertices p) & seq_vertices q]) <->
  pairwise_distant_seqs d paths.
Proof.
split=> h p q pP qP pq; first by case: (h p q pP qP pq).
by split; [exact: (disjointWl (set_ball_sub _ _) (h p q pP qP pq)) | exact: h].
Qed.

Lemma has_k_distant_set_pathsP (d k : nat) X Y :
  (exists paths : seq (seq G),
     size paths = k /\
     uniq paths /\
     (forall p : seq G, p \in paths -> seq_set_path X Y p) /\
     (forall p q : seq G, p \in paths -> q \in paths -> p != q ->
        [disjoint seq_vertices p & seq_vertices q] /\
        [disjoint set_ball d.-1 (seq_vertices p) & seq_vertices q])) <->
  has_k_distant_set_paths d k X Y.
Proof.
split=> -[ps [sz [u [pp dist]]]]; exists ps; split=> //; split=> //; split=> //.
  exact: (proj1 (pairwise_distant_seqsP d ps) dist).
exact: (proj2 (pairwise_distant_seqsP d ps) dist).
Qed.

(** Radius corners: [d = 0] and [d = 1] both mean pairwise disjoint supports of unequal values. *)
Lemma pairwise_distant_seqs0 paths :
  pairwise_distant_seqs 0 paths <->
  (forall p q : seq G, p \in paths -> q \in paths -> p != q -> [disjoint seq_vertices p & seq_vertices q]).
Proof.
by split=> h p q pP qP pq; have := h p q pP qP pq; rewrite /= set_ball0.
Qed.

Lemma pairwise_distant_seqs01 paths : pairwise_distant_seqs 0 paths <-> pairwise_distant_seqs 1 paths.
Proof. exact: iff_refl. Qed.

Lemma pairwise_distant_seqs_mono (d e : nat) paths :
  d <= e -> pairwise_distant_seqs e paths -> pairwise_distant_seqs d paths.
Proof.
move=> de h p q pP qP pq; apply: (disjointWl _ (h p q pP qP pq)).
by apply: set_ball_mono; rewrite -!subn1; exact: leq_sub2r.
Qed.

(** Restricting the family keeps the relation; only the values present matter. *)
Lemma pairwise_distant_seqs_sub (d : nat) paths paths' :
  {subset paths' <= paths} -> pairwise_distant_seqs d paths -> pairwise_distant_seqs d paths'.
Proof. by move=> sub h p q pP qP; apply: h; apply: sub. Qed.

Lemma pairwise_distant_seqs_nil (d : nat) : pairwise_distant_seqs d [::].
Proof. by []. Qed.

Lemma pairwise_distant_seqs1 (d : nat) p : pairwise_distant_seqs d [:: p].
Proof. by move=> a b; rewrite !inE => /eqP-> /eqP->; rewrite eqxx. Qed.

(** Equal raw duplicates are ignored by the relation. *)
Lemma pairwise_distant_seqs_dup (d : nat) p : pairwise_distant_seqs d [:: p; p].
Proof. by move=> a b; rewrite !inE !orbb => /eqP-> /eqP->; rewrite eqxx. Qed.

(** [k = 0] always holds; [k = 1] is one set-to-set path. *)
Lemma has_k_distant_set_paths0 (d : nat) X Y : has_k_distant_set_paths d 0 X Y.
Proof. by exists [::]. Qed.

Lemma has_k_distant_set_paths1 (d : nat) X Y :
  has_k_distant_set_paths d 1 X Y <-> exists p : seq G, seq_set_path X Y p.
Proof.
split=> [[ps [sz [_ [pp _]]]] | [p pp]].
  by case: ps sz pp => [|p [|q ps]] //= _ pp; exists p; exact: (pp p (mem_head p [::])).
exists [:: p]; split=> //; split=> //; split; last exact: pairwise_distant_seqs1.
by move=> a; rewrite inE => /eqP->.
Qed.

Lemma has_k_distant_set_paths_uniq (d k : nat) X Y paths :
  size paths = k -> uniq paths -> (forall p, p \in paths -> seq_set_path X Y p) ->
  pairwise_distant_seqs d paths -> has_k_distant_set_paths d k X Y.
Proof. by move=> sz u pp dist; exists paths. Qed.

End DistantPaths.
