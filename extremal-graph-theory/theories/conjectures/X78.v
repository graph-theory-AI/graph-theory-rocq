(** * Extremal.conjectures.X78 -- v2 H-free max-cut row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X78 vocabulary ************************************************)

Definition x78_edge_set (G : sgraph) : {set {set G}} :=
  simple_edge_set G.

Definition x78_edge_count (G : sgraph) : nat := #|x78_edge_set G|.

Definition x78_cut_size (G : sgraph) (A : {set G}) : nat :=
  #|[set e in x78_edge_set G | ~~ [disjoint e & A] && ~~ (e \subset A)]|.

Definition x78_subgraph_of (H G : sgraph) : Prop :=
  exists f : H -> G,
    injective f /\
    forall x y : H, x -- y -> f x -- f y.

Definition x78_three_fourths_surplus (cnum cden m s : nat) : Prop :=
  (cnum ^ 4) * (m ^ 3) <= (cden ^ 4) * (s ^ 4).

(** ** X78 statements ******************************************************)

(** Studies slice: Alon-Krivelevich-Sudakov max-cut surplus conjecture for
    fixed H-free graphs. *)
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
