(** * Extremal.conjectures.X120 -- v2 Conlon-Fox-Sudakov sparse pair row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X120 vocabulary ***********************************************)

(** Erdos--Hajnal convention: [H]-free means no *induced* copy of [H].
    (Kept local so this file is self-contained and does not import X118.) *)
Definition x120_induced_free (G H : sgraph) : Prop :=
  forall S : {set G}, ~ inhabited (induced S ≃ H).

(** Cross edges between disjoint [A] and [B] in [G]: ordered pairs [(a, b)]
    with [a \in A], [b \in B], [a -- b] (each counted once as [A], [B] are
    disjoint). *)
Definition x120_edges_between (G : sgraph) (A B : {set G}) : nat :=
  #|[set p : G * G | [&& p.1 \in A, p.2 \in B & p.1 -- p.2]]|.

(** Cross edges between [A] and [B] in the complement [G-bar]: ordered pairs
    [(a, b)], [a \in A], [b \in B], with [a] and [b] *non*-adjacent in [G].
    As [A], [B] are disjoint we have [a <> b], so these are exactly the edges
    of [G-bar] between [A] and [B] (equal to [#|A|*#|B| - e_G(A,B)]). *)
Definition x120_nonedges_between (G : sgraph) (A B : {set G}) : nat :=
  #|[set p : G * G | [&& p.1 \in A, p.2 \in B & ~~ (p.1 -- p.2)]]|.

(** Corpus row: studies:std_conlon_fox_sudakov_sparse_pair_conjecture
    Site: none
    Review: none
    English statement: (Conlon, Fox and Sudakov, "Conlon-Fox-Sudakov sparse pair conjecture")
      For every graph H there are positive rationals c1 = a1/a2 and c2 = b1/b2 such that for
      every graph G on at least 2 vertices with no INDUCED copy of H and every rational
      x = xn/xd with 0 < x < 1/2, there are disjoint vertex sets A, B with
      |A|, |B| >= x^c1 * |V(G)|^c2 such that the density between A and B is at most x either in
      G or in the complement of G.
    Definitions: [x120_induced_free G H] - no vertex set of G induces a graph isomorphic to H (X120.v);
      [x120_edges_between G A B] - the ordered pairs (a,b) in A x B with a adjacent to b
      (X120.v); [x120_nonedges_between G A B] - the ordered pairs (a,b) in A x B with a and b
      NON-adjacent, which for disjoint A, B are exactly the complement's cross edges (X120.v).
    Notes: this row comes from the studies slice of the corpus, which has no site or review page.
      x = xn/xd with 0 < x < 1/2 is written 0 < xn and 2 * xn < xd; the exponents are ratios
      a1/a2 and b1/b2 of positive naturals, chosen per H before G. The double fractional-power
      size bound is cleared by raising to the power a2 * b2 and cross-multiplying. "B is
      x-sparse to A" is the density bound xd * e(A,B) <= xn * |A| * |B|, and "in one of G,
      G-bar" is the disjunction with the non-edge count. *)
Definition conlon_fox_sudakov_sparse_pair_statement : Prop :=
  forall H : sgraph,
    exists a1 a2 b1 b2 : nat,
      [/\ 0 < a1, 0 < a2, 0 < b1 & 0 < b2] /\
      forall G : sgraph,
        2 <= #|G| ->
        x120_induced_free G H ->
        forall xn xd : nat,
          0 < xn -> 2 * xn < xd ->
          exists A B : {set G},
            [/\ [disjoint A & B],
                xn ^ (a1 * b2) * #|G| ^ (b1 * a2)
                  <= xd ^ (a1 * b2) * #|A| ^ (a2 * b2),
                xn ^ (a1 * b2) * #|G| ^ (b1 * a2)
                  <= xd ^ (a1 * b2) * #|B| ^ (a2 * b2)
              & (xd * x120_edges_between A B <= xn * (#|A| * #|B|) \/
                 xd * x120_nonedges_between A B <= xn * (#|A| * #|B|))].
