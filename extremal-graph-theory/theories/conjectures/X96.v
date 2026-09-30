(** * Extremal.conjectures.X96 -- v2 large C4-free subgraph row *)

From GTBase Require Export base.
From Extremal.conjectures Require Import X4 X59.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X96 vocabulary ************************************************)

Definition x96_c4_free (G : sgraph) : Prop :=
  ~ x59_has_cycle_length G 4.

Definition x96_m_three_fourths_lower
    (cnum cden m e : nat) : Prop :=
  (cnum ^ 4) * (m ^ 3) <= (cden ^ 4) * (e ^ 4).

(** Corpus row: studies:std_bollob_s_erd_s_problem_on_large_c_free_subgraphs
    Site: none
    Review: none
    English statement: (Bollobas and Erdos, "Bollobas-Erdos problem on large C4-free subgraphs")
      There are positive naturals cnum, cden such that every graph G with m edges has a
      subgraph H containing no 4-cycle and with (cnum/cden) * m^(3/4) <= e(H); that is, every
      m-edge graph has a C_4-free subgraph with Omega(m^(3/4)) edges.
    Definitions: [x96_c4_free H] - H has no uniform cycle on exactly 4 vertices, via
      [x59_has_cycle_length] (X59.v) (X96.v); [x96_m_three_fourths_lower cnum cden m e] - the
      cross-multiplied form cnum^4 * m^3 <= cden^4 * e^4 of e >= (cnum/cden) * m^(3/4)
      (X96.v); [x59_subgraph_of H G] - an injective adjacency-preserving map (X59.v);
      [x4_edge_count] - the number of edges (X4.v).
    Notes: this row comes from the studies slice of the corpus, which has no site or review page.
      Only the first (Omega) half of the source question is formalised; "determine f(m, C_4)"
      has no Prop form. The constants are quantified outermost, so they are absolute. No
      threshold on m is imposed, which is harmless because the inequality holds trivially at
      m = 0. *)
Definition bollobas_erdos_large_c4_free_subgraph_statement : Prop :=
  exists cnum cden : nat,
    [/\ 0 < cnum, 0 < cden
      & forall (m : nat) (G : sgraph),
          x4_edge_count G = m ->
          exists H : sgraph,
            [/\ x59_subgraph_of H G,
                x96_c4_free H
              & x96_m_three_fourths_lower cnum cden m (x4_edge_count H)]].
