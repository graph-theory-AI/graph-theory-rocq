(** * Infinite.conjectures.D4inf4 — two sibling carriers.

    - strong_matchings_and_covers (done): a possibly-infinite HYPERGRAPH
      [iHypergraph] (vertices, edges, incidence); "strongly maximal / minimal"
      uses [card_le] (the choice-free injection form of the symmetric-difference
      cardinal comparison).
    - universal_highly_arc_transitive_digraphs (done): a DIGRAPH [iDigraph]
      (irreflexive, NON-symmetric arc relation).  "Highly arc transitive" is the
      transitive automorphism ACTION written out (an adjacency-preserving
      bijection sending any directed path to any equal-length one) — never a
      constructed automorphism GROUP object.  "Universal" is the source's
      alternating-walk condition. *)

From GTBase Require Export base.
From Infinite Require Import foundations.igraph.
From mathcomp Require Import all_boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ================================================================= *)
(** ** strong_matchings_and_covers  (Conjecture, OPEN) *)

Record iHypergraph := Build_iHypergraph {
  hV : Type;
  hE : Type;
  hinc : hE -> hV -> Prop }.

(** Edge [e] has size ≤ [k]: its vertices are covered by ['I_k]. *)
Definition hedge_le (H : iHypergraph) (k : nat) (e : hE H) : Prop :=
  exists g : 'I_k -> hV H, forall v, hinc e v -> exists i, g i = v.

(** A MATCHING: pairwise vertex-disjoint edges. *)
Definition hmatching (H : iHypergraph) (F : hE H -> Prop) : Prop :=
  forall e1 e2, F e1 -> F e2 -> (exists v, hinc e1 v /\ hinc e2 v) -> e1 = e2.

(** A (vertex) COVER: every edge contains a chosen vertex. *)
Definition hcover (H : iHypergraph) (X : hV H -> Prop) : Prop :=
  forall e : hE H, exists v, X v /\ hinc e v.

(** [F] is STRONGLY MAXIMAL: |F' \ F| ≤ |F \ F'| for every matching [F']. *)
Definition strongly_maximal_matching (H : iHypergraph) (F : hE H -> Prop) : Prop :=
  hmatching F /\
  forall F' : hE H -> Prop, hmatching F' ->
    card_le (fun e => F' e /\ ~ F e) (fun e => F e /\ ~ F' e).

(** [X] is STRONGLY MINIMAL: |X \ X'| ≤ |X' \ X| for every cover [X']. *)
Definition strongly_minimal_cover (H : iHypergraph) (X : hV H -> Prop) : Prop :=
  hcover X /\
  forall X' : hV H -> Prop, hcover X' ->
    card_le (fun v => X v /\ ~ X' v) (fun v => X' v /\ ~ X v).

(** Corpus row: opg:strong_matchings_and_covers
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/strong_matchings_and_covers/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/strong_matchings_and_covers.json
    English statement: (Open Problem Garden, "Strong matchings and covers") For
      every (possibly infinite) hypergraph H and every k such that every edge of
      H has at most k vertices, H has a strongly maximal matching and a strongly
      minimal cover.  A matching is a set F of pairwise vertex-disjoint edges,
      and it is strongly maximal when for every matching F' the edges of F' not
      in F inject into the edges of F not in F'.  A cover is a set X of vertices
      meeting every edge, and it is strongly minimal when for every cover X' the
      vertices of X not in X' inject into the vertices of X' not in X.
    Definitions: [iHypergraph] - a record of a vertex Type, an edge Type and a
      Prop-valued incidence (this file, D4inf4.v); [hedge_le k e] - the vertices
      of e are covered by a map from 'I_k, i.e. e has at most k vertices
      (D4inf4.v); [hmatching F], [hcover X], [strongly_maximal_matching F],
      [strongly_minimal_cover X] (D4inf4.v); [card_le P Q] - an injection from
      the subtype of P into the subtype of Q, the choice-free reading of "at
      most as many" (infinite-graph-theory/theories/foundations/igraph.v).
    Notes: the cardinal comparisons use [card_le], the injection form, so no
      choice or cardinal arithmetic is needed.  CAVEAT (recorded in
      meta/STATEMENT_IMPROVEMENTS.md): nothing forbids an EMPTY edge.  With
      k = 0, [hedge_le 0 e] forces every edge to have no vertices, and then
      [hcover X] is unsatisfiable as soon as one edge exists, so the statement
      is refutable by the one-edge hypergraph with empty incidence; the source
      implicitly assumes nonempty edges. *)
Definition strong_matchings_and_covers_statement : Prop :=
  forall (H : iHypergraph) (k : nat),
    (forall e : hE H, hedge_le k e) ->
    (exists F : hE H -> Prop, strongly_maximal_matching F) /\
    (exists X : hV H -> Prop, strongly_minimal_cover X).

(** ================================================================= *)
(** ** universal_highly_arc_transitive_digraphs  (Question, OPEN) *)

Record iDigraph := Build_iDigraph {
  dV : Type;
  darc : dV -> dV -> Prop;
  darc_irr : forall x, ~ darc x x }.

(** An automorphism: an adjacency-preserving bijection (the group ACTION, unfolded). *)
Definition dautomorphism (G : iDigraph) (f : dV G -> dV G) : Prop :=
  bijective f /\ forall x y, darc x y <-> darc (f x) (f y).

(** A directed path (all consecutive pairs are arcs). *)
Fixpoint darc_path (G : iDigraph) (p : seq (dV G)) : Prop :=
  match p with
  | [::] => True
  | x :: p' => match p' with
               | [::] => True
               | y :: _ => darc x y /\ darc_path p'
               end
  end.

(** HIGHLY ARC TRANSITIVE: the automorphism action is transitive on directed
    paths of every fixed length. *)
Definition highly_arc_transitive (G : iDigraph) : Prop :=
  forall p q : seq (dV G),
    darc_path p -> darc_path q -> size p = size q ->
    exists f : dV G -> dV G, dautomorphism f /\ map f p = q.

(** An ALTERNATING WALK [x :: p] with starting polarity [b] (each step's arc
    direction flips): [b] forward = [darc x y], backward = [darc y x]. *)
Fixpoint alt_walk_from (G : iDigraph) (b : bool) (x : dV G) (p : seq (dV G)) : Prop :=
  match p with
  | [::] => True
  | y :: p' => (if b then darc x y else darc y x) /\ alt_walk_from (~~ b) y p'
  end.

(** The alternating walk [x :: p] (polarity [b]) USES the arc [a → c]. *)
Fixpoint walk_uses (G : iDigraph) (b : bool) (x : dV G) (p : seq (dV G)) (a c : dV G) : Prop :=
  match p with
  | [::] => False
  | y :: p' =>
      ((b = true /\ x = a /\ y = c) \/ (b = false /\ y = a /\ x = c))
      \/ walk_uses (~~ b) y p' a c
  end.

(** UNIVERSAL: every pair of arcs lies on a common alternating walk. *)
Definition universal (G : iDigraph) : Prop :=
  forall a1 c1 a2 c2 : dV G, darc a1 c1 -> darc a2 c2 ->
    exists (b : bool) (x : dV G) (p : seq (dV G)),
      alt_walk_from b x p /\ walk_uses b x p a1 c1 /\ walk_uses b x p a2 c2.

(** LOCALLY FINITE: every vertex has finite out- and in-neighbourhoods. *)
Definition d_locally_finite (G : iDigraph) : Prop :=
  forall x : dV G,
    (exists ko (go : 'I_ko -> dV G), forall y, darc x y -> exists i, go i = y) /\
    (exists ki (gi : 'I_ki -> dV G), forall y, darc y x -> exists i, gi i = y).

(** Non-vacuity guards (preflight): a genuine arc exists; infinitely many
    vertices; and no sinks/sources (out- and in-degree ≥ 1) so the finite
    directed cycle and the edgeless digraph cannot satisfy the row vacuously. *)
Definition d_has_arc (G : iDigraph) : Prop := exists a b : dV G, darc a b.
Definition d_infinite (G : iDigraph) : Prop := exists f : nat -> dV G, injective f.
Definition d_no_sink_source (G : iDigraph) : Prop :=
  forall x : dV G, (exists y, darc x y) /\ (exists y, darc y x).

(** Corpus row: opg:universal_highly_arc_transitive_digraphs
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/universal_highly_arc_transitive_digraphs/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/universal_highly_arc_transitive_digraphs.json
    English statement: (Open Problem Garden, "Universal highly arc transitive
      digraphs") There exists a digraph G that is locally finite (finite in- and
      out-neighbourhoods at every vertex), highly arc transitive (for any two
      directed paths of the same length some automorphism maps the first onto
      the second) and universal (any two arcs lie on a common alternating walk,
      a walk whose successive steps alternate in direction), and that moreover
      is nondegenerate: it has at least one arc, infinitely many vertices, and
      neither sinks nor sources.
    Definitions: [iDigraph] - a record of a vertex Type and an irreflexive
      Prop-valued arc relation (this file, D4inf4.v); [dautomorphism f] - an
      arc-preserving and arc-reflecting bijection (D4inf4.v); [darc_path p] -
      all consecutive pairs of p are arcs (D4inf4.v);
      [highly_arc_transitive G], [alt_walk_from b x p], [walk_uses b x p a c],
      [universal G], [d_locally_finite G] (D4inf4.v); [d_has_arc G],
      [d_infinite G], [d_no_sink_source G] - the nondegeneracy guards
      (D4inf4.v).
    Notes: "highly arc transitive" is the automorphism ACTION written out,
      never a constructed automorphism group object.  The source is a Question
      and the body asserts existence.  The three nondegeneracy guards are
      MODELLING ADDITIONS, added so that the finite directed cycle and the
      edgeless digraph cannot answer the question vacuously; they make the
      formal statement STRICTLY STRONGER than the literal source. *)
Definition universal_highly_arc_transitive_digraphs_statement : Prop :=
  exists G : iDigraph,
    [/\ d_locally_finite G, highly_arc_transitive G, universal G
      & [/\ d_has_arc G, d_infinite G & d_no_sink_source G] ].
