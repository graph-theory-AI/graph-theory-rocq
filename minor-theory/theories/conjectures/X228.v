(** * Minor.conjectures.X228 -- queue-number and poset-unavoidability rows (wave X228, 2026-09-23) *)

From GTBase Require Export base.
From GraphTheory Require Import minor.
From Minor.foundations Require Import containment width_params.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local x228 vocabulary ***********************************************

    Reused: [layered_tw_le] and [queue_number_le]
    (Minor.foundations.width_params), [tw_le] (same file), [wagner_planar] and
    [minor] (GTBase / coq-graph-theory), [poset_cover_graph] and
    [poset_dimension_at_most] (GTBase.posets).  One new notion. *)

(** A graph [H] is UNAVOIDABLE when the cover graph of every finite poset of
    large enough dimension contains [H] as a minor: some threshold [d] is such
    that every poset whose dimension is NOT at most [d] has [H] as a minor of its
    cover graph. *)
Definition x228_unavoidable (H : sgraph) : Prop :=
  exists d : nat,
    forall P : finite_poset,
      ~ poset_dimension_at_most P d -> minor (poset_cover_graph P) H.

(** ** X228 statements *****************************************************)

(** Corpus row: arxiv:1810.08314#00
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/1810.08314__00/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/1810.08314__00.json
    English statement: (Dujmovic, Eppstein, Joret, Morin and Wood 2018, open problem on the
      queue-number of graphs of bounded layered treewidth)
      There is a function f from the naturals to the naturals such that every finite simple
      graph of layered treewidth at most k has queue number at most f(k).
    Definitions: [layering L] - a map from vertices to naturals sending adjacent vertices to
      the same or to consecutive layers, and [layered_tw_le G k] - layered treewidth at most
      k: such a layering together with a tree decomposition each of whose bags contains at most
      k vertices of each layer (minor-theory/theories/foundations/width_params.v);
      [queue_number_le G m] - queue number at most m: an injective vertex order and an
      assignment of the edges to m queues such that no queue contains two NESTED edges, i.e.
      edges ab and cd with ord a < ord c < ord d < ord b (same file); [sdecomp] - tree
      decomposition (coq-graph-theory).
    Notes: "bounded layered treewidth implies bounded queue-number" is read as one function f
      valid for every k and every graph, so the existential quantifier on f precedes the
      universal quantifiers, which is the finite form of "bounded implies bounded".  The
      layering condition is stated over the naturals without subtraction, as the conjunction
      [L u <= L v + 1] and [L v <= L u + 1].  Both queues and layers are indexed from 0. *)
Definition bounded_layered_treewidth_bounded_queue_number_statement : Prop :=
  exists f : nat -> nat,
    forall (k : nat) (G : sgraph), layered_tw_le G k -> queue_number_le G (f k).

(** Corpus row: arxiv:2002.00496#02
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/2002.00496__02/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/2002.00496__02.json
    English statement: (Huynh, Joret, Micek, Seweryn and Wollan 2020, "Excluding a ladder",
      Conjecture 6 -- PLACEHOLDER, see Notes)
      Every unavoidable graph is planar and has treewidth at most three, where a graph H is
      unavoidable when some dimension threshold d is such that the cover graph of every finite
      poset whose dimension exceeds d has H as a minor.
    Definitions: [x228_unavoidable H] - some threshold d is such that every finite poset whose
      dimension is not at most d has H as a minor of its cover graph (this file);
      [poset_cover_graph P] and [poset_dimension_at_most P d] - the cover graph of a finite
      poset and the "dimension at most d" predicate, d linear extensions realising the order
      (base/theories/posets.v); [wagner_planar H] - H has neither a K5 nor a K3,3 minor, which
      by Wagner's theorem is planarity (base/theories/base.v); [tw_le H 3] - treewidth at most
      three (minor-theory/theories/foundations/width_params.v); [minor G H] - H is a minor of G
      (coq-graph-theory).
    Notes: BLOCKED.  The row's actual content is "a graph H is unavoidable if and only if H is
      a minor of some graph from Kelly's construction".  Kelly's construction is NOT defined at
      the element level in the source: the paper gives it by a figure and says explicitly that
      "its definition for an arbitrary order k can be inferred from the figure" (Figure 2).
      The equivalent reformulation the paper offers -- "H is a minor of some graph obtained by
      gluing copies of K4 along edges in a path-like way, and subdividing all horizontal edges
      of the K4s once" -- is likewise given by a figure (Figure 3) and leaves undetermined both
      the gluing pattern ("path-like") and which edges of each K4 are the "horizontal" ones, so
      no faithful element-level encoding of the right-hand side is available.  Rather than
      approximate it, this Definition is a PLACEHOLDER: it states the strongest consequence of
      Conjecture 6 that IS expressible with the available vocabulary, namely the necessary
      condition obtained from the two properties the source itself records for Kelly's
      construction (its cover graphs are planar and have pathwidth 3, hence treewidth at most
      3, and both properties are minor-closed).  It is NOT the conjecture, and it is strictly
      weaker: unblocking the row requires an element-level definition of Kelly's construction,
      taken from the poset-dimension literature rather than from this paper.  The [unavoidable]
      side, by contrast, is faithful and complete.
      Second reader (2026-09-23): the BLOCKED verdict is confirmed, and the placeholder is even
      weaker than "strictly weaker" suggests.  Of the two directions of Conjecture 6 only the
      "if" direction is conjectural: the "only if" direction is already known, since Kelly's
      construction supplies posets of unbounded dimension whose cover graphs are planar of
      pathwidth 3, so every unavoidable graph is a minor of one of them.  The committed
      Definition is a consequence of that KNOWN direction alone, hence carries none of the open
      content of the row; it must never be read as the conjecture.  This also diverges from the
      modelling choice recorded in meta/v2_classification.json, which asked for the paper's
      K_4-gluing reformulation to be encoded; that reformulation is given by Figure 3 and leaves
      the gluing pattern and the "horizontal" edges undetermined, so blocking is the right call.
      The [x228_unavoidable] side was re-read and is faithful: one threshold d, then all finite
      posets whose dimension is not at most d, with H a minor of the cover graph. *)
Definition unavoidable_minor_kelly_construction_statement : Prop :=
  forall H : sgraph, x228_unavoidable H -> wagner_planar H /\ tw_le H 3.
