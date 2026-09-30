(** * Chromatic.conjectures.X177 -- v2 forests of lanterns pervasive row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X177 vocabulary ***********************************************)

Definition x177_induced_path_between
    (G : sgraph) (x y : G) (p : seq G) : Prop :=
  path (--) x p /\
  last x p = y /\
  uniq (x :: p) /\
  forall u v : G,
    u \in x :: p -> v \in x :: p -> u -- v ->
    exists z : G, (u == z /\ v \in p /\ last u [:: v] = v) \/
      (v == z /\ u \in p /\ last v [:: u] = u).

Definition x177_lantern (H : sgraph) : Prop :=
  exists a b : H,
    a != b /\
    forall i : 'I_3,
      exists p : seq H,
        x177_induced_path_between a b p /\ 2 <= size p.

Definition x177_forest_of_lanterns (H : sgraph) : Prop :=
  exists (T : sgraph) (piece : T -> {set H}),
    is_tree [set: T] /\
    (forall v : H, exists t : T, v \in piece t) /\
    (forall t : T, is_forest (piece t) \/ x177_lantern (induced (piece t))) /\
    (forall t u : T, t != u -> #|piece t :&: piece u| <= 1).

Definition x177_contains_induced_long_subdivision
    (G H : sgraph) (ell : nat) : Prop :=
  exists branch : H -> G,
    injective branch /\
    forall x y : H,
      x -- y ->
      exists p : seq G,
        [/\ path (--) (branch x) p,
            last (branch x) p = branch y,
            ell <= size p,
            uniq (branch x :: p) &
            forall z : G,
              z \in p -> z != branch y -> forall u : H, z != branch u].

(** ** X177 statements *****************************************************)

(** Corpus row: arxiv:1609.00314#00
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/1609.00314__00/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/1609.00314__00.json
    English statement: (Chudnovsky, Scott and Seymour 2021, informal conjecture, arXiv:1609.00314)
      For every finite simple graph H that is a forest of lanterns and all nu and ell there is a c
      such that every graph G with clique number at most nu and chromatic number greater than c
      contains an induced subgraph isomorphic to a subdivision of H in which every edge is
      subdivided at least ell times; that is, every forest of lanterns is pervasive.
    Definitions: [x177_lantern H] - two distinct vertices joined by three internally disjoint
      paths of length at least two (this file); [x177_forest_of_lanterns H] - H is covered by pieces
      indexed by a tree, each piece a forest or a lantern, any two pieces sharing at most one vertex
      (this file); [x177_contains_induced_long_subdivision G H ell] - an injective branch map from
      the vertices of H into G together with, for each edge of H, a path of at least ell internal
      vertices avoiding the other branch vertices (this file); [x177_induced_path_between] (this
      file).
    Notes: KNOWN UNFAITHFUL ENCODING, corpus leg blocked. The faithfulness audit of 2026-07-17,
      meta/BLOCKED_RETARGETING_AUDIT.md and the row's verification_note, found that the word
      INDUCED, which is the crux of the Chudnovsky-Scott-Seymour programme, is missing from both the
      antecedent and the consequent: the helper [x177_induced_path_between] has a fourth clause that
      is machine-confirmed to be a tautology, so it only says "path" and not "induced path", and
      [x177_contains_induced_long_subdivision] likewise constrains only the branch paths and not the
      absence of extra edges between them. The body is left untouched here, WP4 changes comments
      only. *)
Definition forest_of_lanterns_pervasive_statement : Prop :=
  forall (H : sgraph) (nu ell : nat),
    x177_forest_of_lanterns H ->
    exists c : nat,
      forall G : sgraph,
        ω([set: G]) <= nu ->
        c < χ([set: G]) ->
        x177_contains_induced_long_subdivision G H ell.
