(** * C12: perfection with complete original row contracts
    Frozen at de78ea9. Subset-relative and induced-carrier equalities remain
    distinguished in the legacy bodies and bridge to the upstream predicate.
    Bicliques and nonempty pure pairs are not identified by this migration. *)
From GTBase Require Import base perfect_graphs.
From Extremal.conjectures Require Import D2ram.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Legacy.

Definition perfect_graph (G : sgraph) : Prop := forall A : {set G}, χ(A) = ω(A).

Definition complete_bipartite_subgraphs_of_perfect_graphs_statement : Prop :=
  forall a b : nat, (0 < a)%N -> (a < b)%N ->
    exists N : nat, forall (G : sgraph) (n : nat),
      #|G| = n -> (N <= n)%N -> Legacy.perfect_graph G ->
      exists A B : {set G},
        (complete_bipartite_sub A B
           /\ (n ^ (b - a) <= #|A| ^ b)%N /\ (n ^ (b - a) <= #|B| ^ b)%N)
        \/
        (@complete_bipartite_sub (compl G) A B
           /\ (n ^ (b - a) <= #|A| ^ b)%N /\ (n ^ (b - a) <= #|B| ^ b)%N).

End Legacy.

Lemma perfect_graph_compat (G : sgraph) :
  Legacy.perfect_graph G <-> perfect_graph G.
Proof. symmetry; exact: is_perfect_graph_subsets. Qed.

Lemma complete_bipartite_subgraphs_of_perfect_graphs_statement_compat :
  Legacy.complete_bipartite_subgraphs_of_perfect_graphs_statement <->
  complete_bipartite_subgraphs_of_perfect_graphs_statement.
Proof.
split=> claim a b positive ordered.
- have [N bound] := claim a b positive ordered.
  exists N => G n size large perf.
  exact (bound G n size large ((perfect_graph_compat G).2 perf)).
- have [N bound] := claim a b positive ordered.
  exists N => G n size large perf.
  exact (bound G n size large ((perfect_graph_compat G).1 perf)).
Qed.
