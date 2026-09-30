(** * Chromatic.conjectures.X12 -- v2 Woodall list-colouring row *)

From GraphTheory Require Import minor.
From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** X12 statements ******************************************************)

(** Corpus row: studies:std_woodall_s_list_colouring_conjecture_for_k_minor
    Site: none
    Review: none
    English statement: (Woodall, studies slice of the corpus)
      For all s, t >= 1 and every finite simple graph G having no complete bipartite graph K_{s,t}
      as a minor, the choice number of G is at most s + t - 1.
    Definitions: [minor G H] - H is a minor of G (coq-graph-theory minor.v); [KB s t] - the
      complete bipartite graph with parts of sizes s and t (coq-graph-theory sgraph.v);
      [is_choice_number G ch] - ch is the least k such that G is k-choosable (GTBase
      base/theories/base.v).
    Notes: This row has no site or review page in the corpus, hence the literal "none" above. The
      guards 1 <= s and 1 <= t make the truncated nat subtraction s + t - 1 harmless; the source
      quantifies over all s, t in the naturals. *)
Definition woodall_ks_t_minor_free_list_colouring_statement : Prop :=
  forall (s t ch : nat) (G : sgraph),
    1 <= s -> 1 <= t ->
    ~ minor G (KB s t) ->
    is_choice_number G ch ->
    ch <= s + t - 1.
