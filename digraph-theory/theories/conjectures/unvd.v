(** * Digraph.conjectures.unvd — P5: unavoidability of digraphs in tournaments

    The unavoidability corpus of Aboulker, Bang-Jensen, Bousquet, Charbit, Havet,
    Hörsch, Maffray, Zamora, "Unavoidability of digraphs" (arXiv:2410.23566).

    The central invariant is the UNAVOIDABILITY NUMBER [unvd]: a digraph [D] is
    [N]-unavoidable when every tournament on [N] vertices contains [D] as a
    (homomorphic, arc-preserving) subdigraph, and [unvd D = N] is the LEAST such [N].
    Because making the least-[N] framing of a [nat -> Prop] invariant into a total
    function is awkward, [unvd] here is stated as a RELATION [unvd D N : Prop]: the
    defining property of "the unavoidability number of [D] is [N]" (least [N] that is
    unavoidable while [N-1] is not), exactly as the assignment requests.

    Statements (classification 'unvd_vertex_deletion', arXiv:2410.23566):
      - [conj_9] : ∃ absolute C, unvd(D) ≤ C·unvd(D−v) for every ACYCLIC digraph D
                   and every vertex v.
      - [prob_6] : for every rational α, ∃ a polynomial bound such that unvd(D) is at
                   most that polynomial in |V(D)| whenever the maximum average degree
                   mad(D) ≤ α.

    The maximum average degree mad(D) = max over non-empty induced subdigraphs H of
    2|A(H)|/|V(H)| is built here as a genuine rational-valued function [mad]; Problem 6
    uses a rational bound α (NOT reals), per the assignment.
    See docs/CONJECTURES_FORMALIZATION_PLAN.md §4 (P5). *)

From HB Require Import structures.
From mathcomp Require Import all_boot.
From mathcomp Require Import all_algebra.
From Digraph Require Import prelude digraph oriented tournament.
From Digraph Require Import dichromatic heroes.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Tournament target and (homomorphic) subdigraph containment *)

(** [is_tournament] (reused from heroes.v): irreflexive + semicomplete + asymmetric. *)

(** [H] is contained in [D] as a subdigraph: an INJECTIVE arc-PRESERVING map
    (a homomorphism onto a subset, NOT an induced embedding — every arc of [H] maps
    to an arc of [D], but non-arcs of [H] may map anywhere). This is the containment
    notion of arXiv:2410.23566. *)
Definition contains_subdigraph (H D : diGraphType) : Prop :=
  exists f : H -> D, injective f /\ forall u v : H, u --> v -> f u --> f v.

(** ** The unavoidability number (as a relation)

    [D] is [N]-unavoidable: every tournament on [N] vertices contains [D]. *)
Definition unavoidable (D : diGraphType) (N : nat) : Prop :=
  forall T : diGraphType, is_tournament T -> #|T| = N -> contains_subdigraph D T.

(** Monotone fact recorded for faithfulness of the "least" framing below: being
    [N]-unavoidable is intended to be upward closed in [N] (larger tournaments still
    contain [D]); we do not assume it here but state [unvd] as least via an explicit
    not-[(N-1)]-unavoidable clause so the value is pinned down regardless. *)

(** [unvd D N] : the unavoidability number of [D] equals [N] — the least [N] for which
    [D] is [N]-unavoidable. Stated as the relation [D is N-unavoidable AND no value
    below N is unavoidable]. We GUARD the degenerate empty digraph: for [#|D| = 0] the
    invariant is uninteresting (every tournament, even the empty one, contains it), so
    callers pass [(0 < #|D|)%N]; the relation itself stays meaningful for all [N ≥ 1]
    via the "[N] minimal" clause. *)
Definition unvd (D : diGraphType) (N : nat) : Prop :=
  unavoidable D N /\ (forall M : nat, M < N -> ~ unavoidable D M).

(** ** Maximum average degree mad(D) (rational-valued)

    For a vertex subset [S], [narcs_in S] counts the arcs of [D] with both endpoints
    in [S] (the arcs of the induced subdigraph on [S]); its density is
    2·[narcs_in S] / |S|. mad(D) is the maximum density over all NON-EMPTY [S]. *)
Local Open Scope ring_scope.

Definition narcs_in (D : diGraphType) (S : {set D}) : nat :=
  #|[set xy : D * D | [&& xy.1 \in S, xy.2 \in S & xy.1 --> xy.2]]|.

(** Density 2|A(H)|/|V(H)| of the induced subdigraph on [S], as a rational. *)
Definition density (D : diGraphType) (S : {set D}) : rat :=
  (2 * (narcs_in S))%:Q / (#|S|)%:Q.

(** [mad D] : the maximum, over all non-empty vertex subsets [S], of [density S].
    A genuine rational-valued function via a big-max with neutral element 0 (attained
    only at the — excluded — empty set, so it never inflates the value). *)
Definition mad (D : diGraphType) : rat :=
  \big[Num.max/0]_(S in [set S : {set D} | S != set0]) density S.

(** ** The conjectures *)

(** Corpus row: arxiv:2410.23566#03
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/2410.23566__03/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/2410.23566__03.json
    English statement: (Aboulker, Havet, Lochet, Lopes, Picasarri-Arrieta, Rambaud 2024, Blow-ups and extensions of trees in tournaments, arXiv:2410.23566, Conjecture 9)
      There is a constant C such that for every acyclic finite digraph D with more than one
      vertex and every vertex v of D, if the unavoidability number of D is nD and that of D
      minus v is nDv, then nD <= C * nDv. The unavoidability number of a digraph is the least N
      such that every tournament on N vertices contains it as a subdigraph.
    Definitions: [unavoidable D N] - every tournament on exactly N vertices contains D via an
      injective arc-preserving map (this file); [unvd D N] - D is N-unavoidable and no smaller
      value is (this file); [contains_subdigraph] (this file); [is_tournament]
      (conjectures/heroes.v); [del_vertex v] (core/digraph.v); [acyclicb]
      (conjectures/dichromatic.v).
    Notes: The unavoidability number is a RELATION rather than a total function, so the bound is
      quantified over the values nD and nDv it pins down; this is vacuous for digraphs whose
      unavoidability number is not pinned. The guard 1 < #|D| keeps both sides meaningful,
      deleting a vertex from a one-vertex digraph leaving the empty digraph. *)
Definition conj_9 : Prop :=
  exists C : nat,
    forall (D : diGraphType) (v : D),
      acyclicb D -> (1 < #|D|)%N ->
      forall nD nDv : nat,
        unvd D nD -> unvd (del_vertex v) nDv ->
        (nD <= C * nDv)%N.

(** Corpus row: arxiv:2410.23566#00
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/2410.23566__00/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/2410.23566__00.json
    English statement: (Aboulker, Havet, Lochet, Lopes, Picasarri-Arrieta, Rambaud 2024, Blow-ups and extensions of trees in tournaments, arXiv:2410.23566, Problem 6)
      For every rational alpha there are naturals a, d and b such that every nonempty finite
      digraph D whose maximum average degree is at most alpha has unavoidability number at most
      a * #|D| ^ d + b.
    Definitions: [unvd D N] and [unavoidable D N] (this file); [mad D] - the maximum over
      nonempty vertex sets of twice the number of arcs inside the set divided by its size, as a
      rational (this file); [density] and [narcs_in] (this file).
    Notes: The polynomial of the source is encoded concretely by coefficients a, d, b giving the
      bound a * n ^ d + b, which is a genuine polynomial bound and avoids an abstract polynomial
      type. The bound alpha is a rational, not a real; the source says positive real alpha, and
      every real bound can be replaced by a rational one above it, so the two readings agree.
      The unavoidability number appears relationally, as in [conj_9]. *)
Definition prob_6 : Prop :=
  forall alpha : rat,
    exists a d b : nat,
      forall (D : diGraphType),
        (0 < #|D|)%N -> (mad D <= alpha) ->
        forall nD : nat, unvd D nD ->
          (nD <= a * #|D| ^ d + b)%N.
