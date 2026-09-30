(** * Extremal.conjectures.X118 -- v2 Conlon-Fox-Sudakov dense pair row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X118 vocabulary ***********************************************)

(** Erdos--Hajnal convention: [H]-free means [G] has no *induced* copy of [H]. *)
Definition x118_induced_free (G H : sgraph) : Prop :=
  forall S : {set G}, ~ inhabited (induced S ≃ H).

(** Number of edges between disjoint sets [A] and [B]: the ordered pairs
    [(a, b)] with [a \in A], [b \in B] and [a -- b].  As [A] and [B] are
    disjoint each cross edge is counted exactly once, and the total number of
    ordered pairs is [#|A| * #|B|]; so the edge-density between [A] and [B] is
    [x118_edges_between A B / (#|A| * #|B|)]. *)
Definition x118_edges_between (G : sgraph) (A B : {set G}) : nat :=
  #|[set p : G * G | [&& p.1 \in A, p.2 \in B & p.1 -- p.2]]|.

(** Corpus row: studies:std_conlon_fox_sudakov_conjecture_dense_pair
    Site: none
    Review: none
    English statement: (Conlon, Fox and Sudakov, "Conlon-Fox-Sudakov conjecture (dense pair)")
      For every graph H there are positive rationals eps = e1/e2 and sigma = s1/s2 such that
      for every graph G on more than one vertex with no INDUCED copy of H and every rational
      c = c1/c2 with 0 <= c <= 1/2, there are disjoint vertex sets A, B with
      |A| >= eps * c^sigma * |V(G)| and |B| >= eps * |V(G)| whose edge density is at most c or
      at least 1 - c.
    Definitions: [x118_induced_free G H] - no vertex set of G induces a graph isomorphic to H, the
      Erdos-Hajnal convention (X118.v); [x118_edges_between G A B] - the number of ordered
      pairs (a,b) with a in A, b in B and a adjacent to b; since A and B are disjoint each
      cross edge is counted once, so the density is that count divided by |A| * |B| (X118.v).
    Notes: this row comes from the studies slice of the corpus, which has no site or review page.
      All reals are ratios of naturals: eps = e1/e2, sigma = s1/s2 (all four positive), and
      c = c1/c2 with c <= 1/2 written 2 * c1 <= c2. The fractional-power size bound is cleared
      by raising to the power s2 and cross-multiplying, so c^sigma = c1^s1 / c2^s1. Density at
      most c is c2 * e(A,B) <= c1 * |A| * |B|; density at least 1 - c is
      (c2 - c1) * |A| * |B| <= c2 * e(A,B), where the nat subtraction is safe since
      2 * c1 <= c2. eps and sigma are chosen before G, as the source requires. *)
Definition conlon_fox_sudakov_dense_pair_statement : Prop :=
  forall H : sgraph,
    exists e1 e2 s1 s2 : nat,
      [/\ 0 < e1, 0 < e2, 0 < s1 & 0 < s2] /\
      forall G : sgraph,
        1 < #|G| ->
        x118_induced_free G H ->
        forall c1 c2 : nat,
          0 < c2 -> 2 * c1 <= c2 ->
          exists A B : {set G},
            [/\ [disjoint A & B],
                e1 ^ s2 * c1 ^ s1 * #|G| ^ s2 <= e2 ^ s2 * c2 ^ s1 * #|A| ^ s2,
                e1 * #|G| <= e2 * #|B|
              & (c2 * x118_edges_between A B <= c1 * (#|A| * #|B|) \/
                 (c2 - c1) * (#|A| * #|B|) <= c2 * x118_edges_between A B)].
