(** * Chromatic.conjectures.X185 -- v2 widespread multigraph row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X185 vocabulary ***********************************************)

Definition x185_contains_induced_long_subdivision
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

Definition x185_widespread (H : mgraph) : Prop :=
  forall nu ell : nat,
    exists c : nat,
      forall G : sgraph,
        ω([set: G]) <= nu ->
        c < χ([set: G]) ->
        x185_contains_induced_long_subdivision G (line_graph H) ell.

(** ** X185 statements *****************************************************)

(** Corpus row: arxiv:1701.05597#00
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/1701.05597__00/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/1701.05597__00.json
    English statement: (Scott and Seymour 2019, Conjecture 1.8, arXiv:1701.05597)
      Every loopless multigraph H is widespread: for all nu and ell there is a c such that every
      finite simple graph G with clique number at most nu and chromatic number greater than c
      contains a long subdivision of H, realised here as a branch map on the vertices of the LINE
      GRAPH of H with all edges subdivided at least ell times.
    Definitions: [x185_widespread H] - the forcing property just described (this file);
      [x185_contains_induced_long_subdivision G H ell] - an injective branch map from the vertices
      of H into G together with, for each edge of H, a path with at least ell internal vertices
      avoiding the other branch vertices (this file); [line_graph H] (GTBase base/theories/base.v);
      [loopless] (base.v).
    Notes: KNOWN UNFAITHFUL ENCODING, corpus leg blocked. The faithfulness audit of 2026-07-17,
      meta/BLOCKED_RETARGETING_AUDIT.md and the row's verification_note, found the WRONG TARGET
      OBJECT: widespreadness of a multigraph H is about induced subdivisions of H itself, whose
      edges become internally disjoint paths, whereas the encoding subdivides the LINE GRAPH of H, a
      different graph. The "induced" requirement is also absent, since the branch paths are not
      required to be chordless nor internally disjoint from each other. The body is left untouched
      here, WP4 changes comments only. *)
Definition every_multigraph_widespread_statement : Prop :=
  forall H : mgraph, loopless H -> x185_widespread H.
