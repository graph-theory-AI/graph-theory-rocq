(** * GTMisc.conjectures.X41 -- v2 sparse pure-pair row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X41 vocabulary ************************************************)

Definition x41_induced_H_free (H G : sgraph) : Prop :=
  forall S : {set G}, ~ inhabited (induced S ≃ H).

Definition x41_complete_between (G : sgraph) (A B : {set G}) : Prop :=
  forall a b : G, a \in A -> b \in B -> a -- b.

Definition x41_anticomplete_between (G : sgraph) (A B : {set G}) : Prop :=
  forall a b : G, a \in A -> b \in B -> ~~ (a -- b).

Definition x41_pure_pair (G : sgraph) (A B : {set G}) : Prop :=
  [disjoint A & B] /\
  A != set0 /\
  B != set0 /\
  (x41_complete_between A B \/ x41_anticomplete_between A B).

(** ** X41 statements ******************************************************)

(** Corpus row: studies:std_conlon_fox_sudakov_sparse_linear_conjecture
    Site: none
    Review: none
    English statement: (Conlon, Fox and Sudakov, sparse linear pure-pair conjecture)
      For every finite simple graph H there is a rational eps = eps_num / eps_den with
      0 < eps_num <= eps_den such that every graph G on more than one vertex with no induced
      copy of H contains two disjoint non-empty vertex sets A and B that are either completely
      adjacent or completely non-adjacent and satisfy
      (eps_den * |A|)^eps_den >= eps_num^eps_den * |V(G)|^eps_num and
      eps_den * |B| >= eps_num * |V(G)|.
    Definitions: [x41_induced_H_free H G] - no induced subgraph of G is isomorphic to H (this
      file); [x41_complete_between A B] / [x41_anticomplete_between A B] - every vertex of A is
      adjacent to / non-adjacent to every vertex of B (this file); [x41_pure_pair A B] - A and
      B are disjoint, non-empty, and one of the two previous conditions holds (this file);
      [induced] - coq-graph-theory induced subgraphs.
    Notes: DISCREPANCY WITH THE CORPUS TEXT.  The source asks for a pure (eps|G|, eps|G|)-pair,
      i.e. both sides of LINEAR size.  The B-side clause is exactly that, but the A-side clause
      is the near-linear form: taking eps_den-th roots it reads
      eps_den * |A| >= eps_num * |V(G)|^(eps_num/eps_den), a sublinear lower bound whenever
      eps_num < eps_den, so it is strictly weaker than the required |A| >= eps * |V(G)|.  The
      statement as written is therefore weaker than the conjecture on the A side.  Recorded in
      meta/STATEMENT_IMPROVEMENTS.md. *)
Definition sparse_linear_pure_pair_statement : Prop :=
  forall H : sgraph, exists eps_num eps_den : nat,
    0 < eps_num /\
    eps_num <= eps_den /\
    forall G : sgraph,
      1 < #|G| ->
      x41_induced_H_free H G ->
      exists A B : {set G},
        x41_pure_pair A B /\
        eps_den ^ eps_den * #|A| ^ eps_den >= eps_num ^ eps_den * #|G| ^ eps_num /\
        eps_den * #|B| >= eps_num * #|G|.
