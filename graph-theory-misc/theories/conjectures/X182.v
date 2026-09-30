(** * GTMisc.conjectures.X182 -- v2 planar-cover poset dimension row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** X182 statements *****************************************************)

(** Corpus row: arxiv:1612.07540#00
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/1612.07540__00/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/1612.07540__00.json
    English statement: (Joret, Micek and Wiechert 2016, "Planar posets have dimension at most
      linear in their height", open problem on posets with planar cover graphs)
      There are constants C and d such that every finite poset P whose cover graph is planar
      and whose chains all have at most h elements has dimension at most C * (h+1)^d, i.e. the
      dimension of a poset with a planar cover graph is bounded by a polynomial in its height.
    Definitions: [finite_poset] - a finite type with a reflexive, antisymmetric, transitive
      relation (GTBase posets.v); [poset_height_at_most P h] - every chain of P has at most h
      elements (same file); [poset_cover_rel] / [poset_cover_graph P] - the cover relation and
      the simple graph it induces (same file); [poset_dimension_at_most P d] - there is a
      realizer of at most d linear extensions whose intersection is the poset order (same
      file); [wagner_planar] - combinatorial Wagner planarity (GTBase).
    Notes: retargeted after GTBase posets.v became available.  The source asks about a linear
      bound "or any polynomial function for that matter"; the Rocq body states the POLYNOMIAL
      version, which is the weaker of the two.  Since the row was authored, the polynomial part
      has been settled affirmatively (Kozik, Micek and Trotter 2019, O(h^6); Gorsky and Seweryn
      2021, O(h^3)), so the statement as written is now a theorem and only the linear version
      remains open; the corpus status is partial.  Height is rendered as an upper bound on the
      size of every chain, so h is any bound and not necessarily the exact height. *)
Definition planar_cover_poset_dimension_polynomial_bound_statement : Prop :=
  exists C d : nat,
    forall (P : finite_poset) (h : nat),
      wagner_planar (poset_cover_graph P) ->
      poset_height_at_most P h ->
      poset_dimension_at_most P (C * h.+1 ^ d).
