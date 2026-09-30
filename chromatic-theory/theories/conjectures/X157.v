(** * Chromatic.conjectures.X157 -- v2 local-connectivity colouring algorithm row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X157 vocabulary ***********************************************)

Definition x157_path_internal (G : sgraph) (x y : G) (p : seq G) : {set G} :=
  [set z : G | z \in p] :\: [set x; y].

Definition x157_simple_xy_path (G : sgraph) (x y : G) (p : seq G) : Prop :=
  path (--) x p /\ last x p = y /\ uniq (x :: p).

Definition x157_internally_disjoint_xy_paths
    (G : sgraph) (x y : G) (m : nat) : Prop :=
  exists route : 'I_m -> seq G,
    (forall i : 'I_m, x157_simple_xy_path x y (route i)) /\
    forall i j : 'I_m,
      i != j ->
      [disjoint x157_path_internal x y (route i)
       & x157_path_internal x y (route j)].

Definition x157_max_local_connectivity_at_most (G : sgraph) (k : nat) : Prop :=
  forall (x y : G) (m : nat),
    x != y -> x157_internally_disjoint_xy_paths x y m -> m <= k.

Fixpoint x157_data_nth_nat (d : data) (i : nat) : nat :=
  match d, i with
  | Dcons (Dnat n) _, 0 => n
  | Dcons _ rest, j.+1 => x157_data_nth_nat rest j
  | Dnat n, 0 => n
  | _, _ => 0
  end.

Definition x157_output_colour (G : sgraph) (k : nat) (out : data) (v : G) : nat :=
  x157_data_nth_nat out (enum_rank v) %% k.

Definition x157_output_k_colouring_or_none
    (k : nat) (G : sgraph) (out : data) : Prop :=
  (out = Dnat 0 /\ ~ χ([set: G]) <= k) \/
  (0 < k /\ forall x y : G, x -- y ->
      x157_output_colour k out x != x157_output_colour k out y).

Definition x157_polytime_colouring_or_none (k : nat) : Prop :=
  polytime_outputs_graph_on
    (fun G : sgraph => k_connected G k /\ x157_max_local_connectivity_at_most G k)
    (x157_output_k_colouring_or_none k).

(** ** X157 statements *****************************************************)

(** Corpus row: arxiv:1505.01616#00
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/1505.01616__00/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/1505.01616__00.json
    English statement: (Aboulker, Brettell, Havet, Marx and Trotignon 2016, Question 1.7, arXiv:1505.01616)
      For every fixed k >= 4 there is a polynomial-time algorithm that, given a k-connected graph
      whose maximal local connectivity is at most k, outputs either a proper k-colouring of it or
      the answer that none exists.
    Definitions: [x157_max_local_connectivity_at_most G k] - for any two distinct vertices, any
      family of internally disjoint paths between them has at most k members (this file);
      [x157_internally_disjoint_xy_paths x y m] - m paths from x to y whose internal vertex sets are
      pairwise disjoint (this file); [x157_simple_xy_path] (this file);
      [x157_output_k_colouring_or_none k G out] - the output is either the number 0 together with
      the fact that chi(G) > k, or a list of naturals read modulo k that is a proper colouring (this
      file); [x157_output_colour] and [x157_data_nth_nat] - decoding of the output data (this file);
      [polytime_outputs_graph_on] (GTBase base/theories/complexity.v); [k_connected] (base.v).
    Notes: The corpus row is a QUESTION; the Rocq body asserts the affirmative answer. The
      algorithmic output is specified by a decoding relation on the program's output data, colours
      being read modulo k, so the specification is axiom-free and finite. The row was retargeted in
      2026-07-16 from a blocked placeholder, see meta/BLOCKED_RETARGETING_FOUNDATIONS.md. *)
Definition local_connectivity_k_colouring_polytime_statement : Prop :=
  forall k : nat, 4 <= k -> x157_polytime_colouring_or_none k.
