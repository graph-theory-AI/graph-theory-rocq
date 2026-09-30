(** * Extremal.conjectures.X88 -- v2 pentagonal Turan row *)

From GTBase Require Export base.
From Extremal.conjectures Require Import X4.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X88 vocabulary ************************************************)

Definition x88_clique_count (G : sgraph) (r : nat) : nat :=
  #|[set S : {set G} | (#|S| == r) && cliqueb S]|.

Definition x88_c5_part_adj (a b : nat) : bool :=
  (a != b) && (((a.+1 %% 5) == b) || ((b.+1 %% 5) == a)).

Definition x88_pentagonal_part_adj (a b : nat) : bool :=
  if (a < 5) && (b < 5) then x88_c5_part_adj a b else a != b.

Definition x88_pentagonal_turan_graph (G : sgraph) (r n : nat) : Prop :=
  2 <= r /\
  #|G| = n /\
  exists part : G -> 'I_(r + 3),
    forall x y : G,
      (x -- y) =
        ((x != y) && x88_pentagonal_part_adj (val (part x)) (val (part y))).

(** [x88_within_part_edges c] = number of edges of [G] monochromatic under the
    r-colouring [c] (each undirected edge counted once, as in [x4_edge_count]);
    [x88_edit_to_r_partite G r] = D_r(G) = the minimum over all r-colourings of
    that count = the least number of edges whose deletion makes [G] r-partite
    (Balogh-Clemen-Lavrov-Lidicky-Pfender, arXiv:1910.00028).  The neutral
    [#|G| * #|G|] bounds every summand, so the fold is the genuine minimum. *)
Definition x88_within_part_edges (G : sgraph) (r : nat) (c : {ffun G -> 'I_r}) : nat :=
  #|[set p : G * G |
      [&& (p.1 -- p.2), ((enum_rank p.1) < (enum_rank p.2))%N & c p.1 == c p.2]]|.

Definition x88_edit_to_r_partite (G : sgraph) (r : nat) : nat :=
  \big[minn/(#|G| * #|G|)]_(c : {ffun G -> 'I_r}) x88_within_part_edges c.

(** Corpus row: studies:std_balogh_clemen_lavrov_lidick_pfender_conjecture
    Site: none
    Review: none
    English statement: (Balogh, Clemen, Lavrov, Lidicky and Pfender, "Balogh-Clemen-Lavrov-Lidicky-Pfender Conjecture")
      For every r >= 2 there is a positive rational delta_r such that every K_{r+1}-free graph G
      on n vertices with e(G) >= t_r(n) - delta_r * n^2 edges is dominated by some pentagonal
      Turan graph Gstar on n vertices: e(G) <= e(Gstar) and D_r(G) <= D_r(Gstar), where D_r
      is the
      minimum number of edges whose deletion makes the graph r-partite.
    Definitions: [x88_clique_count G r] - the number of r-element cliques (X88.v); [x88_c5_part_adj],
      [x88_pentagonal_part_adj] - the adjacency template of the blow-up with one C_5 part class
      and r-2 complete Turan part classes (X88.v); [x88_pentagonal_turan_graph G r n] - G is a
      blow-up of that template on n vertices (X88.v); [x88_within_part_edges G r c] - the number
      of edges monochromatic under the r-colouring c, counted once each (X88.v);
      [x88_edit_to_r_partite G r] - D_r(G), the minimum of that count over all r-colourings
      (X88.v); [x4_turan_number r n tr] - tr is the Turan number t_r(n) (X4.v);
      [x4_K_free G t], [x4_edge_count] (X4.v).
    Notes: this row comes from the studies slice of the corpus, which has no site or review page.
      The dominated quantity is D_r (the edit distance to r-partiteness), NOT the r-clique
      count: the Turan graph T(n,r) maximises both e(G) and the number of K_r yet is itself
      r-partite (D_r = 0), so an r-clique target would be dominated by T(n,r) for every G and
      hence vacuous. The neutral element |V(G)|^2 of the minimum fold bounds every summand, so
      the fold is the genuine minimum. The edge condition is cross-multiplied and the
      subtraction moved to the other side, so no nat subtraction occurs. *)
Definition pentagonal_turan_stability_dominates_clique_count_statement : Prop :=
  forall r : nat,
    2 <= r ->
    exists delta_num delta_den : nat,
      [/\ 0 < delta_num, 0 < delta_den
        & forall (n tr : nat) (G : sgraph),
            x4_turan_number r n tr ->
            x4_K_free G r.+1 ->
            #|G| = n ->
            delta_den * tr <= delta_den * x4_edge_count G + delta_num * n ^ 2 ->
            exists Gstar : sgraph,
              [/\ x88_pentagonal_turan_graph Gstar r n,
                  x4_edge_count G <= x4_edge_count Gstar
                & x88_edit_to_r_partite G r <= x88_edit_to_r_partite Gstar r]].
