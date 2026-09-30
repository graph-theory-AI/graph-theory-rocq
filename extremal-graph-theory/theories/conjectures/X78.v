(** * Extremal.conjectures.X78 -- v2 H-free max-cut row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X78 vocabulary ************************************************)

Definition x78_edge_set (G : sgraph) : {set {set G}} :=
  [set e : {set G} |
      [exists x : G, [exists y : G, (x -- y) && (e == [set x; y])]]].

Definition x78_edge_count (G : sgraph) : nat := #|x78_edge_set G|.

Definition x78_cut_size (G : sgraph) (A : {set G}) : nat :=
  #|[set e in x78_edge_set G | ~~ [disjoint e & A] && ~~ (e \subset A)]|.

Definition x78_subgraph_of (H G : sgraph) : Prop :=
  exists f : H -> G,
    injective f /\
    forall x y : H, x -- y -> f x -- f y.

Definition x78_three_fourths_surplus (cnum cden m s : nat) : Prop :=
  (cnum ^ 4) * (m ^ 3) <= (cden ^ 4) * (s ^ 4).

(** Corpus row: studies:std_alon_krivelevich_sudakov_max_cut_exponent_conjec
    Site: none
    Review: none
    English statement: (Alon, Krivelevich and Sudakov, "Alon-Krivelevich-Sudakov Max-Cut Exponent Conjecture")
      For every graph H there are positive naturals cnum, cden and a threshold N such that every
      graph G with m >= N edges containing no copy of H as a subgraph has a vertex set A whose
      cut has size at least m/2 + s for some s with (cnum/cden) * m^(3/4) <= s.
    Definitions: [x78_edge_set G], [x78_edge_count G] - the edges as 2-element sets and their number
      (X78.v); [x78_cut_size G A] - the number of edges with exactly one end in A (X78.v);
      [x78_subgraph_of H G] - an injective adjacency-preserving map H -> G, so its negation is
      H-freeness (X78.v); [x78_three_fourths_surplus cnum cden m s] - the cross-multiplied form
      cnum^4 * m^3 <= cden^4 * s^4 of s >= (cnum/cden) * m^(3/4) (X78.v).
    Notes: this row comes from the studies slice of the corpus, which has no site or review page.
      H-freeness is subgraph-freeness, not induced-subgraph-freeness, matching the source. The
      constant depending on H is the ratio cnum/cden, chosen after H and before G; the
      threshold N renders "m sufficiently large". *)
Definition h_free_max_cut_three_fourths_surplus_statement : Prop :=
  forall H : sgraph,
    exists cnum cden N : nat,
      [/\ 0 < cnum, 0 < cden
        & forall (G : sgraph) (m : nat),
            N <= m ->
            x78_edge_count G = m ->
            ~ x78_subgraph_of H G ->
            exists (A : {set G}) (s : nat),
              x78_three_fourths_surplus cnum cden m s /\
              m + 2 * s <= 2 * x78_cut_size A].
