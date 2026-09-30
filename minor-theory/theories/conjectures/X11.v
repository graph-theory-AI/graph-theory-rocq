(** * Minor.conjectures.X11 -- v2 minor/list and induced-Menger rows *)

From GraphTheory Require Import minor.
From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X11 vocabulary ************************************************)

Definition x11_path_vertices (G : sgraph) (p : seq G) : {set G} :=
  [set v | v \in p].

Definition x11_xy_path (G : sgraph) (X Y : {set G}) (p : seq G) : Prop :=
  match p with
  | [::] => False
  | x :: q =>
      x \in X /\ last x q \in Y /\ uniq p /\ path (--) x q
  end.

Definition x11_closed_neighbourhood (G : sgraph) (Z : {set G}) : {set G} :=
  Z :|: \bigcup_(z in Z) N(z).

Definition x11_anticomplete_sets (G : sgraph) (A B : {set G}) : Prop :=
  [disjoint A & B] /\
  forall x y : G, x \in A -> y \in B -> ~~ (x -- y).

Definition x11_pairwise_anticomplete_paths
    (G : sgraph) (paths : seq (seq G)) : Prop :=
  forall p q : seq G,
    p \in paths -> q \in paths -> p != q ->
    @x11_anticomplete_sets G (x11_path_vertices p) (x11_path_vertices q).

Definition x11_has_k_anticomplete_xy_paths
    (G : sgraph) (k : nat) (X Y : {set G}) : Prop :=
  exists paths : seq (seq G),
    size paths = k /\
    uniq paths /\
    (forall p : seq G, p \in paths -> @x11_xy_path G X Y p) /\
    @x11_pairwise_anticomplete_paths G paths.

Definition x11_no_xy_path_after_closed_neighbourhood
    (G : sgraph) (X Y Z : {set G}) : Prop :=
  forall p : seq G,
    @x11_xy_path G X Y p ->
    [disjoint x11_path_vertices p & x11_closed_neighbourhood Z] ->
    False.

(** ** X11 statements ******************************************************)

(** Corpus row: arxiv:2201.09115#02
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/2201.09115__02/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/2201.09115__02.json
    English statement: (Steiner 2022, open problem stated in "Disproof of a Conjecture by Woodall")
      For every s at least 1 there is a threshold T, at least s, such that for every t at
      least T, every finite simple graph with no minor isomorphic to the complete bipartite
      graph K_(s,t) has list chromatic number at most s + t - 1.
    Definitions: standard
    Notes: this is the fixed-s regime that Steiner's Theorem 1 leaves open; the disproof of
      Woodall's conjecture covers only s and t of comparable size.  The choice number is the
      GTBase [is_choice_number G ch] (the least k for which G is k-choosable), used as a
      hypothesis "ch is the choice number" followed by the bound ch <= s + t - 1; a graph with
      no choice number would make the conclusion vacuous, which cannot happen for finite
      graphs.  [s + t - 1] is truncated natural subtraction but s >= 1 and t >= T >= s >= 1
      keep it faithful. *)
Definition woodall_fixed_s_eventual_choosability_statement : Prop :=
  forall s : nat, 1 <= s ->
    exists T : nat,
      s <= T /\
      forall (t ch : nat) (G : sgraph),
        T <= t ->
        ~ minor G (KB s t) ->
        is_choice_number G ch ->
        ch <= s + t - 1.

(** Corpus row: arxiv:2512.17232#00
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/2512.17232__00/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/2512.17232__00.json
    English statement: (Hickingbotham, Joret, "An Induced A-Path Theorem", Conjecture 6)
      For every natural number k, every finite simple graph G and all vertex subsets X and Y
      of G, at least one of the following holds: G contains k pairwise anticomplete X-Y paths;
      or there is a vertex set Z of size at most k-1 such that after deleting the closed
      neighbourhood of Z from G there is no X-Y path left.
    Definitions: [x11_path_vertices p] - the set of vertices occurring in the sequence p
      (minor-theory/theories/conjectures/X11.v); [x11_xy_path X Y p] - p is a nonempty
      sequence of pairwise distinct vertices forming a path of G whose first vertex lies in X
      and whose last vertex lies in Y (same file); [x11_anticomplete_sets A B] - A and B are
      disjoint and no edge of G joins a vertex of A to a vertex of B (same file);
      [x11_pairwise_anticomplete_paths paths] - any two distinct entries of the list have
      anticomplete vertex sets (same file); [x11_has_k_anticomplete_xy_paths G k X Y] - there
      is a list of exactly k distinct X-Y paths that are pairwise anticomplete (same file);
      [x11_closed_neighbourhood Z] - Z together with every neighbour of a member of Z (same
      file); [x11_no_xy_path_after_closed_neighbourhood X Y Z] - every X-Y path of G meets the
      closed neighbourhood of Z (same file).
    Notes: "G - N[Z] has no X-Y path" is encoded contrapositively, as "no X-Y path of G avoids
      N[Z]", rather than by building the induced subgraph; the two readings agree because an
      X-Y path of the deleted graph is exactly an X-Y path of G avoiding N[Z].  Anticomplete
      paths are in particular vertex-disjoint, since disjointness is part of
      [x11_anticomplete_sets].  [k.-1] is the predecessor, so for k = 0 the bound is |Z| <= 0
      and the left disjunct already holds with the empty list. *)
Definition induced_menger_anticomplete_paths_statement : Prop :=
  forall (k : nat) (G : sgraph) (X Y : {set G}),
    @x11_has_k_anticomplete_xy_paths G k X Y \/
    exists Z : {set G},
      #|Z| <= k.-1 /\
      @x11_no_xy_path_after_closed_neighbourhood G X Y Z.
