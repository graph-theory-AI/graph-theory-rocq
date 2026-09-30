(** * Packing.conjectures.X26 -- v2 distant induced-Menger row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X26 vocabulary ************************************************)

Fixpoint x26_ball (G : sgraph) (r : nat) (x : G) : {set G} :=
  if r is r'.+1 then x26_ball r' x :|: \bigcup_(z in x26_ball r' x) N(z)
  else [set x].

Definition x26_set_ball (G : sgraph) (r : nat) (S : {set G}) : {set G} :=
  \bigcup_(x in S) x26_ball r x.

Definition x26_path_vertices (G : sgraph) (p : seq G) : {set G} :=
  [set v | v \in p].

Definition x26_xy_path (G : sgraph) (X Y : {set G}) (p : seq G) : Prop :=
  match p with
  | [::] => False
  | x :: q => x \in X /\ last x q \in Y /\ uniq p /\ path (--) x q
  end.

Definition x26_pairwise_distant_paths
    (G : sgraph) (d : nat) (paths : seq (seq G)) : Prop :=
  forall p q : seq G,
    p \in paths -> q \in paths -> p != q ->
    [disjoint x26_set_ball (d.-1) (x26_path_vertices p) & x26_path_vertices q].

Definition x26_has_k_distant_xy_paths
    (G : sgraph) (d k : nat) (X Y : {set G}) : Prop :=
  exists paths : seq (seq G),
    size paths = k /\
    uniq paths /\
    (forall p : seq G, p \in paths -> x26_xy_path X Y p) /\
    x26_pairwise_distant_paths d paths.

Definition x26_separates_xy (G : sgraph) (X Y Z : {set G}) : Prop :=
  forall p : seq G,
    x26_xy_path X Y p ->
    [disjoint x26_path_vertices p & Z] ->
    False.

(** ** X26 statements ******************************************************)

(** Corpus row: arxiv:2309.07905#00
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/2309.07905__00/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/2309.07905__00.json
    English statement: (Hendrey, Norin, Steiner, Turcotte 2023, "Conjecture 1.4")
      For all natural numbers d and Dmax there is a constant C > 0 such that for every
      k, every simple graph G of maximum degree at most Dmax and all vertex sets X and
      Y: either G contains k pairwise distinct X-Y paths that are pairwise at distance
      at least d, or there is a vertex set Z of fewer than C * k vertices meeting every
      X-Y path.
    Definitions: [x26_ball r x] / [x26_set_ball r S] — the vertices at distance at most
      r from x, resp. from some member of S (this file); [x26_path_vertices p] — the
      set of vertices on the sequence p (this file); [x26_xy_path X Y p] — a nonempty
      vertex sequence with no repetitions, starting in X, ending in Y and with
      consecutive entries adjacent (this file); [x26_pairwise_distant_paths d paths] —
      for distinct members p, q of the list, the (d-1)-ball around the vertices of p is
      disjoint from the vertices of q (this file); [x26_has_k_distant_xy_paths d k X Y]
      — such a list of k pairwise distinct X-Y paths (this file); [x26_separates_xy X Y
      Z] — no X-Y path avoids Z (this file); [Delta] — maximum degree (GTBase base).
    Notes: "pairwise at distance at least d" is encoded as the (d-1)-ball around one
      path missing the other path's vertex set, so d = 0 degenerates to "the paths are
      vertex-disjoint from their own 0-balls". The k paths are required to be distinct
      as sequences (a uniq list), not vertex-disjoint. The separator Z is not required
      to avoid X and Y. C is quantified after d and Dmax and before k, matching the
      source's C = C(d, Delta). *)
Definition bounded_degree_distant_induced_menger_statement : Prop :=
  forall d Dmax : nat, exists C : nat,
    0 < C /\
    forall (k : nat) (G : sgraph) (X Y : {set G}),
      Delta G <= Dmax ->
      x26_has_k_distant_xy_paths d k X Y \/
      exists Z : {set G},
        #|Z| < C * k /\
        x26_separates_xy X Y Z.
