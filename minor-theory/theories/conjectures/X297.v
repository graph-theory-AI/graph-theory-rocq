(** * Minor.conjectures.X297 -- v2 row: bounded expansion and the Hall ratio of shallow minors (arXiv:1812.07327,
      Problem 8) *)

From GTBase Require Import base common.
From Minor.foundations Require Import shallow_minors.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** X297 statement ******************************************************)

(** Reused vocabulary: Minor.foundations.shallow_minors [internal_shallow_minor], GTBase common.v [has_subgraph]
    and coq-graph-theory's edge set E(G) and independence number α(A).  X297 declares no helper of its own. *)

(** Corpus row: arxiv:1812.07327#02
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/1812.07327__02/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/1812.07327__02.json
    English statement: (Dvorak, Ossona de Mendez and Wu, Problem 8 of arXiv:1812.07327v2)
      Is it true that a class C has bounded expansion if and only if there exists a function f_6 : N -> N such
      that for every r in N and every G in C shm r we have rho(G) <= f_6(r)?
    Definitions: a class of graphs is a predicate [C : sgraph -> Prop]; [internal_shallow_minor G H r] - H is a
      shallow minor of G at depth r: one branch set of G per vertex of H, pairwise disjoint, each holding a centre
      from which every vertex of the set is reached by a walk of at most r edges inside the set, with a host edge
      between the sets of adjacent vertices of H (Minor.foundations.shallow_minors); "C has bounded expansion" is
      "some f1 : nat -> nat gives 2 |E(H)| <= f1(r) |V(H)| for every shallow minor H at depth r of a member of C";
      [has_subgraph H K] - K is isomorphic to a (not necessarily induced) subgraph of H (GTBase common.v);
      "rho(H) <= f6(r)" is "|V(K)| <= f6(r) α(K) for every subgraph K of H"; α([set: K]) - the independence
      number of K, E(H) - the edge set (coq-graph-theory).
    Notes: The source (arXiv:1812.07327v2, 30 January 2020, no1sub.tex l.228-230) asks the question; it is
      encoded as its affirmative answer.  A shallow minor at depth r (l.174-177) is obtained by deleting vertices
      and edges and contracting pairwise vertex-disjoint subgraphs, each of radius at most r.
      [internal_shallow_minor] measures the radius inside the branch set, as a contracted subgraph does: a
      subgraph of radius at most r spans a set whose induced graph has radius at most r, and a breadth-first tree
      of such a set is a subgraph of radius at most r; unused host vertices and extra host edges are the
      deletions.  Bounded expansion (l.178-180): some f_1 : N -> R bounds the average degree 2 |E(H)| / |V(H)|
      of every shallow minor H at depth r of a member.  A real bound is replaced by its ceiling (at least 0), so
      some real f_1 works iff some nat f1 does; the cross-multiplied form holds for the empty graph, whose
      average degree the source leaves undefined.  Property (vi) (l.220-224) bounds the Hall ratio, the maximum
      of |V(K)| / alpha(K) over all subgraphs K (l.47, l.92-95), cross-multiplied as in X266's
      [x266_hall_ratio_le] (chromatic-theory, which minor-theory does not import); the empty subgraph gives
      0 <= 0.  C ranges over all predicates: both sides depend on the members only up to isomorphism, so a class
      need not be closed under isomorphism; the empty class satisfies both sides.  Every class of bounded
      expansion satisfies (vi) (l.225, "clearly"), so the open content is the converse.  Pinned status open; open
      at the pin: the one later record on the Hall ratio, arXiv:2411.16465, treats the paper's Problems 4 and 5. *)
Definition bounded_expansion_shallow_minor_hall_ratio_statement : Prop :=
  forall C : sgraph -> Prop,
    (exists f1 : nat -> nat, forall (r : nat) (G H : sgraph),
        C G -> internal_shallow_minor G H r -> 2 * #|E(H)| <= f1 r * #|H|) <->
    (exists f6 : nat -> nat, forall (r : nat) (G H K : sgraph),
        C G -> internal_shallow_minor G H r -> has_subgraph H K -> #|K| <= f6 r * α([set: K])).
