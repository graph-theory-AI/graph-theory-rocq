(** * C12: perfection with complete original row contracts
    Frozen at de78ea9. Subset-relative and induced-carrier equalities remain
    distinguished in the legacy bodies and bridge to the upstream predicate.
    Bicliques and nonempty pure pairs are not identified by this migration. *)
From GTBase Require Import base perfect_graphs.
From GTMisc.conjectures Require Import X144.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Legacy.

Definition x144_perfect_graph (G : sgraph) : Prop :=
  forall S : {set G}, χ([set: induced S]) = ω([set: induced S]).

Definition fox_pure_pair_perfect_graphs_statement : Prop :=
  forall e1 e2 : nat,
    0 < e1 ->
    e1 < e2 ->
    exists N : nat,
      forall (n : nat) (G : sgraph),
        N <= n ->
        #|G| = n ->
        Legacy.x144_perfect_graph G ->
        exists A B : {set G},
          x144_pure_pair A B /\
          n ^ (e2 - e1) <= #|A| ^ e2 /\
          n ^ (e2 - e1) <= #|B| ^ e2.

End Legacy.

Lemma x144_perfect_graph_compat (G : sgraph) :
  Legacy.x144_perfect_graph G <-> x144_perfect_graph G.
Proof. symmetry; exact: is_perfect_graph_induced_subsets. Qed.

Lemma fox_pure_pair_perfect_graphs_statement_compat :
  Legacy.fox_pure_pair_perfect_graphs_statement <->
  fox_pure_pair_perfect_graphs_statement.
Proof.
split=> claim a b positive ordered.
- have [N bound] := claim a b positive ordered.
  exists N => n G large size perf.
  exact (bound n G large size ((x144_perfect_graph_compat G).2 perf)).
- have [N bound] := claim a b positive ordered.
  exists N => n G large size perf.
  exact (bound n G large size ((x144_perfect_graph_compat G).1 perf)).
Qed.
