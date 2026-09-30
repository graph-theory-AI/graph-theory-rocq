(** * Topological.conjectures.X228 -- random-embeddings rows (wave X228, 2026-09-23) *)

From GTBase Require Export base.
From mathcomp Require Import fingroup perm.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local x228 vocabulary ***********************************************

    [GTBase.surface] already owns the ROTATION-SYSTEM vocabulary of this wave:
    the dart type [surface_dart G] ({(x,y) | x -- y}), the arc-reversing
    involution [surface_edge_perm G], the record [surface_embedding] (a
    permutation of the darts whose orbits are exactly the dart sets of the
    vertices), its face permutation [surface_face_perm] and face count
    [surface_embedding_faces].

    What is missing there, and is added here, is the FINITE ENUMERATION of the
    rotation systems of a graph: [surface_embedding] is a record whose two
    fields are [Prop]-valued equations, so it is not a [finType] and cannot be
    summed over.  [x228_rotation_system G] is the same notion as a decidable
    SUBSET of the finite group [{perm surface_dart G}] — the two boolean
    conjuncts transcribe [surface_erot_src] and [surface_erot_vertex] verbatim —
    so the finitely many orientable embeddings of [G] can be averaged over.
    [grounding_X228.v] proves the bridge [x228_rotation_embedding]: every
    element of [x228_rotation_system G] yields a [surface_embedding] with the
    same face count. *)

Section RotationSystems.
Variable G : sgraph.

(** A permutation of the darts is a ROTATION SYSTEM when it fixes the source of
    every dart and its orbit through a dart [d] is exactly the set of darts
    leaving the same vertex (so it restricts to a cyclic permutation of the
    darts at each vertex): the boolean form of [surface_erot_src] and
    [surface_erot_vertex] (base/theories/surface.v). *)
Definition x228_rotationb (p : {perm surface_dart G}) : bool :=
  [forall d, (sval (p d)).1 == (sval d).1] &&
  [forall d, porbit p d == [set d' | (sval d').1 == (sval d).1]].

Definition x228_rotation_system : {set {perm surface_dart G}} :=
  [set p | x228_rotationb p].

(** The face permutation of a rotation system is [rotation * edge-reversal]
    ([surface_face_perm] of base/theories/surface.v, read off a raw
    permutation), and its orbits are the faces of the embedding. *)
Definition x228_faces (p : {perm surface_dart G}) : nat :=
  #|porbits (p * @surface_edge_perm G)%g|.

(** The number of orientable embeddings of [G] (the denominator of the finite
    average): the number of rotation systems, i.e. the product over the vertices
    of [(deg(v) - 1)!]. *)
Definition x228_nrot : nat := #|x228_rotation_system|.

(** The numerator of the finite average: the total face count over all rotation
    systems.  The expectation E[F] of the source, for the uniform distribution
    on the orientable embeddings of [G], is exactly
    [x228_total_faces G / x228_nrot G]; every statement below keeps it in
    cleared (division-free) form. *)
Definition x228_total_faces : nat :=
  \sum_(p in x228_rotation_system) x228_faces p.

End RotationSystems.

(** ** X228 statements *****************************************************)

(** Corpus row: arxiv:2202.07746#00
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/2202.07746__00/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/2202.07746__00.json
    English statement: (Campion Loth, Mohar, arXiv:2202.07746, Conjecture 4)
      Pick an orientable embedding of a finite CONNECTED simple graph G on n
      vertices uniformly at random among the finitely many rotation systems of G.
      Then
      the average number of faces of the embedding is at most n/3 + 1: three
      times the total number of faces summed over all rotation systems of G is
      at most (n + 3) times the number of rotation systems of G.
    Definitions: [x228_rotation_system G] - the set of rotation systems of G,
      the permutations of the darts that fix every dart's source and whose orbits
      are exactly the vertex dart sets (this file, X228.v; boolean form of
      base/theories/surface.v's [surface_embedding]); [x228_faces p] - the number
      of faces of the rotation system p, the number of orbits of
      p * [surface_edge_perm] (this file, X228.v; same formula as
      [surface_embedding_faces], base/theories/surface.v); [x228_nrot G],
      [x228_total_faces G] - the number of rotation systems of G and the sum of
      their face counts (this file, X228.v).
    Notes: MODELLING of the expectation.  A finite graph has only finitely many
      rotation systems (one cyclic ordering of the darts at each vertex), and the
      source's random embedding is the UNIFORM distribution on them, so E[F] is
      the finite average [x228_total_faces G / x228_nrot G] and NO probability
      layer is needed.  The inequality E[F] <= n/3 + 1 is cleared of both
      divisions into [3 * total <= (n + 3) * nrot]; this is equivalent to the
      source for every graph, since [x228_nrot G >= 1] always (the empty product
      of cyclic orderings). Orientable embeddings only, as in the source.
      CONNECTEDNESS GUARD [connected [set: G]] (added 2026-09-23 after the second
      reader's readback): the source's E[F] is the average over 2-CELL embeddings,
      which exist only for a connected graph (its extremal example, a chain of
      triangles joined by cut edges, is connected), and the additive "+ 1" is per
      connected component.  Without the guard the body is refutable: four disjoint
      edges have n = 8, exactly one rotation system and four faces, i.e. 12 <= 11.
      That witness is kept in meta/probe_hints/random_embedding_expected_faces_third_statement.v
      as a regression check (it must no longer compile against this body). *)
Definition random_embedding_expected_faces_third_statement : Prop :=
  forall G : sgraph, connected [set: G] ->
    3 * x228_total_faces G <= (#|G| + 3) * x228_nrot G.

(** Corpus row: arxiv:2103.05036#00
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/2103.05036__00/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/2103.05036__00.json
    English statement: (Campion Loth, Halasz, Masarik, Mohar, Samal,
      arXiv:2103.05036, Conjecture 1)
      There is a constant c such that for every finite simple graph G on n
      vertices, the average number of faces of a uniformly random orientable
      embedding of G is at most c times n: the total face count summed over all
      rotation systems of G is at most c * n times the number of rotation systems
      of G.
    Definitions: [x228_rotation_system G], [x228_faces p], [x228_nrot G],
      [x228_total_faces G] - as for the previous row (this file, X228.v).
    Notes: MODELLING.  Same finite-average reading of E[F] as the companion row
      (no probability layer).  The source's O(n) is rendered as an EXISTENTIAL
      CONSTANT quantified OUTSIDE the graph quantifier, [exists c, forall G,
      total <= c * n * nrot]: this is the standard meaning of "E[F] = O(n) for
      every n-vertex simple graph" (one constant, uniform in G).  No positivity
      guard is put on c because none is needed: c = 0 is already refuted by any
      graph with an edge (see [grounding_X228.v]), so the constant is forced to
      be positive by the statement itself.  This row is SOLVED (Campion Loth and
      Mohar 2023 prove E[F] <= pi^2/6 * n); it is authored as a statement only.
      Second reader, 2026-09-23: unlike the companion row, the absence of a
      connectedness guard is harmless here.  The source averages over 2-cell
      embeddings (hence over connected graphs), but rotation systems multiply and
      face counts add over connected components, so the disconnected instances of
      this body follow from the connected ones with the SAME constant c; the
      universal form is equivalent to the source's.  It is the companion row's
      additive "+ 1", which is per component, that does not survive the
      extension. *)
Definition random_embedding_expected_faces_linear_statement : Prop :=
  exists c : nat,
    forall G : sgraph, x228_total_faces G <= c * #|G| * x228_nrot G.
