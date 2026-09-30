(** * GTMisc.conjectures.X113 -- v2 coarse Erdos-Posa (cycles/forest) row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X113 vocabulary ***********************************************

    Coarse metric vocabulary, mirroring
    [GTMisc.conjectures.X39] so this file is self-contained.
    [x113_ball r x] is the closed [r]-ball around [x] (all vertices at graph
    distance at most [r]); [x113_set_ball r S] is the union of the [r]-balls
    over a vertex set [S].  A "cycle" is a genuine simple cycle (a uniform
    closed walk on at least three vertices, following adjacency [--]),
    encoded exactly as in base's [girth]/[exact_girth] via
    [ucycle (--) c /\ 2 < size c]. *)

Fixpoint x113_ball (G : sgraph) (r : nat) (x : G) : {set G} :=
  if r is r'.+1 then x113_ball r' x :|: \bigcup_(z in x113_ball r' x) N(z)
  else [set x].

Definition x113_set_ball (G : sgraph) (r : nat) (S : {set G}) : {set G} :=
  \bigcup_(x in S) x113_ball r x.

Definition x113_path_vertices (G : sgraph) (p : seq G) : {set G} :=
  [set v | v \in p].

(** A genuine cycle: a uniform closed adjacency-walk on at least 3 vertices. *)
Definition x113_is_cycle (G : sgraph) (c : seq G) : Prop :=
  ucycle (--) c /\ 2 < size c.

(** Cycles [p], [q] are at distance greater than [d] iff the closed [d]-ball
    around one avoids the vertex set of the other.  For [d >= 1] this already
    forces the two cycles to be vertex-disjoint. *)
Definition x113_pairwise_distant_cycles
    (G : sgraph) (d : nat) (cs : seq (seq G)) : Prop :=
  forall p q : seq G,
    p \in cs -> q \in cs -> p != q ->
    [disjoint x113_set_ball d (x113_path_vertices p) & x113_path_vertices q].

(** [k] distinct genuine cycles that are pairwise at distance greater than [d]. *)
Definition x113_has_k_distant_cycles
    (G : sgraph) (d k : nat) : Prop :=
  exists cs : seq (seq G),
    size cs = k /\
    uniq cs /\
    (forall c : seq G, c \in cs -> x113_is_cycle c) /\
    x113_pairwise_distant_cycles d cs.

(** [G] minus the vertex set [A] is a forest, i.e. the subgraph induced on the
    remaining vertices is acyclic: no genuine cycle of [G] avoids [A].  (Because
    [--] is inherited by induced subgraphs, a genuine cycle whose vertices all
    miss [A] is exactly a cycle of [G - A].) *)
Definition x113_is_forest_after
    (G : sgraph) (A : {set G}) : Prop :=
  forall c : seq G,
    x113_is_cycle c ->
    [disjoint x113_path_vertices c & A] ->
    False.

(** ** X113 statement *****************************************************)

(** Corpus row: studies:std_chudnovsky_seymour_coarse_erd_s_p_sa_conjecture
    Site: none
    Review: none
    English statement: (Chudnovsky and Seymour; also Ahn, Gollin, Huynh and Kwon, coarse
      Erdos-Posa conjecture)
      There are functions f and g from naturals to naturals such that for all integers
      k, d >= 1 and every finite simple graph G, either G contains k distinct cycles that are
      pairwise at distance greater than d, or there is a vertex set X with |X| <= f(k) such
      that deleting the closed g(d)-ball around X leaves a forest.
    Definitions: [x113_ball r x] / [x113_set_ball r S] - the closed r-ball around a vertex, and
      the union of the r-balls over a vertex set (this file); [x113_path_vertices p] - the
      vertex set of a walk (this file); [x113_is_cycle c] - c is a genuine simple cycle, a
      uniform closed adjacency-walk on at least three vertices, encoded as in the girth
      vocabulary of GTBase by [ucycle (--) c] together with [2 < size c] (this file);
      [x113_pairwise_distant_cycles d cs] - for distinct cycles of cs, the closed d-ball around
      one avoids the other, which for d >= 1 already forces vertex-disjointness (this file);
      [x113_has_k_distant_cycles G d k] - k distinct such cycles exist (this file);
      [x113_is_forest_after A] - no genuine cycle of G avoids A, i.e. G minus A is acyclic
      (this file).
    Notes: the two Erdos-Posa functions are quantified before k, d and G, which is the intended
      uniform reading.  "Distance greater than d" is rendered as "the closed d-ball around one
      cycle misses the other", and "G minus the ball is a forest" as "every cycle of G meets the
      ball"; because adjacency is inherited by induced subgraphs, the latter is equivalent to
      acyclicity of the induced subgraph on the complement. *)
Definition coarse_erdos_posa_cycles_forest_statement : Prop :=
  exists f g : nat -> nat,
    forall (k d : nat) (G : sgraph),
      1 <= k -> 1 <= d ->
      x113_has_k_distant_cycles G d k \/
      exists X : {set G},
        #|X| <= f k /\
        x113_is_forest_after (x113_set_ball (g d) X).
