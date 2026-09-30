(** * Digraph.conjectures.long_dipath — Cheng–Keevash / Thomassé long-directed-path conjecture

    Statement-only formalization of Cheng–Keevash Conjecture 1 (Thomassé's directed-path
    conjecture), arXiv:2402.16776: every oriented graph with minimum out-degree ≥ d
    contains a directed simple path of length 2d, i.e. ℓ(D) ≥ 2d.
    See docs/CONJECTURES_FORMALIZATION_PLAN.md §1, §5 (P1), §7.

    [outdeg v] is the out-degree and [ell D] the length of a longest directed simple path,
    both reused from the core. The δ = 3 instance is already PROVED unconditionally in
    applications/ck3 ([ck_conj1_at_3]); recorded here as [conj1_delta3_proved]. The δ = 4
    cases (n ∈ {10, 11}) are the project's computer-aided results and appear as the general
    conjecture instantiated at d = 4 under the extra side-condition #|D| ∈ {10, 11}. *)

From HB Require Import structures.
From mathcomp Require Import all_boot.
From Digraph Require Import prelude digraph oriented dipath ck3_main.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Corpus row: opg:directed_cycle_of_length_twice_the_minimum_outdegree
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/directed_cycle_of_length_twice_the_minimum_outdegree/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/directed_cycle_of_length_twice_the_minimum_outdegree.json
    English statement: (Open Problem Garden, Directed path of length twice the minimum outdegree (Thomasse; Cheng-Keevash Conjecture 1, arXiv:2402.16776))
      Every nonempty finite oriented graph in which every vertex has out-degree at least d has a
      directed path with at least 2d arcs, that is the length of a longest directed path
      satisfies 2 * d <= ell(D).
    Definitions: [orientedDigraph] - irreflexive asymmetric arc relation (core/oriented.v);
      [outdeg v] (core/oriented.v); [ell D] - the maximum number of arcs of a directed path,
      paths being duplicate-free (core/dipath.v).
    Notes: Path length is counted in ARCS, as in the source. The d = 3 instance is proved
      unconditionally in this package (applications ck3, recorded here as [conj1_delta3_proved])
      and the d = 4 cases on 10 and 11 vertices are the project's computer-aided results, so the
      remaining content is the general d. *)
Definition cheng_keevash_conj1_statement : Prop :=
  forall (D : orientedDigraph) (d : nat),
    0 < #|D| -> (forall v : D, d <= outdeg v) -> 2 * d <= ell D.

(** ** Edges (specializations) *)

(** General ⟹ the δ = 3 instance (exactly the shape of [ck_conj1_at_3]). *)
Theorem conj1_implies_delta3 :
  cheng_keevash_conj1_statement ->
  forall D : orientedDigraph, 0 < #|D| -> (forall v : D, 3 <= outdeg v) -> 2 * 3 <= ell D.
Proof. by move=> H D *; apply: H. Qed.

(** General ⟹ the δ = 4 instance (the project's n ∈ {10,11} results add #|D| = n). *)
Theorem conj1_implies_delta4 :
  cheng_keevash_conj1_statement ->
  forall D : orientedDigraph, 0 < #|D| -> (forall v : D, 4 <= outdeg v) -> 2 * 4 <= ell D.
Proof. by move=> H D *; apply: H. Qed.

(** ** The δ = 3 node is unconditionally PROVED (applications/ck3). *)
Remark conj1_delta3_proved :
  forall D : orientedDigraph, 0 < #|D| -> (forall v : D, 3 <= outdeg v) -> 2 * 3 <= ell D.
Proof. exact: ck_conj1_at_3. Qed.
