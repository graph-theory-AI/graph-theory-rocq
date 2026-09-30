(** * GTMisc.conjectures.X208 -- v2 MIS on P_t-free graphs row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X208 vocabulary ***********************************************)

Definition x208_induced_path_order (G : sgraph) (t : nat) : Prop :=
  exists (x : G) (p : seq G),
    [/\ size (x :: p) = t,
        path (--) x p,
        uniq (x :: p) &
        forall i j : nat,
          i.+1 < j -> j < size (x :: p) ->
          ~~ (nth x (x :: p) i -- nth x (x :: p) j)].

Definition x208_Pt_free (G : sgraph) (t : nat) : Prop :=
  ~ x208_induced_path_order G t.

Definition x208_stable_set (G : sgraph) (S : {set G}) : Prop :=
  forall x y : G, x \in S -> y \in S -> x != y -> ~~ (x -- y).

Definition x208_maximum_independent_set_output (G : sgraph) (out : data) : Prop :=
  exists S : {set G},
    x208_stable_set S /\
    #|S| = data_nat_value out /\
    forall T : {set G}, x208_stable_set T -> #|T| <= #|S|.

Definition x208_polytime_mis_on (P : sgraph -> Prop) : Prop :=
  polytime_outputs_graph_on P x208_maximum_independent_set_output.

(** ** X208 statements *****************************************************)

(** Corpus row: arxiv:1803.05396#01
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/1803.05396__01/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/1803.05396__01.json
    English statement: (Groenland, Okrasa, Rzazewski, Scott, Seymour and Spirkl 2018,
      "H-colouring P_t-free graphs in subexponential time", open problem on maximum
      independent set)
      For every t >= 7 there is a program with polynomially bounded step count which, on the
      adjacency-matrix encoding of every graph containing no induced path on t vertices,
      outputs the maximum size of a stable set of that graph.
    Definitions: [x208_induced_path_order G t] - G contains an induced path on t vertices: a
      sequence of t distinct vertices, consecutive ones adjacent and non-consecutive ones
      non-adjacent (this file); [x208_Pt_free G t] - no such path exists (this file);
      [x208_stable_set S] - S is stable (this file);
      [x208_maximum_independent_set_output G out] - the output decodes to the size of a stable
      set that is at least as large as every stable set (this file); [x208_polytime_mis_on P] -
      [polytime_outputs_graph_on P ...] (this file); [polytime_outputs_graph_on Class Spec] -
      some [prog] with polynomially bounded step count meets Spec on the adjacency-matrix
      encoding of every graph in Class (GTBase complexity.v); [enc_graph], [poly_cost_on],
      [data_nat_value] - the adjacency-matrix encoding, the polynomial step-count bound and the
      numerical reading of an output (same file).
    Notes: retargeted on 2026-07-16 from a blocked placeholder to this axiom-free finite-witness
      formulation, see meta/BLOCKED_RETARGETING_FOUNDATIONS.md.  The source asks to "determine
      whether" the problem is polynomial-time solvable; the Rocq body is the positive answer.
      The specification is the VALUE form - the program outputs the maximum stable-set size,
      not a maximum stable set itself - which is the decision/optimization value version of the
      problem. *)
Definition Pt_free_maximum_independent_set_polytime_statement : Prop :=
  forall t : nat, 7 <= t -> x208_polytime_mis_on (fun G => x208_Pt_free G t).
