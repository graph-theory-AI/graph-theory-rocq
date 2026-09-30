(** * Extremal.conjectures.X30 -- v2 triangle-free induced-bipartite row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X30 vocabulary ************************************************)

Definition x30_min_degree_at_least (G : sgraph) (d : nat) : Prop :=
  forall v : G, d <= #|N(v)|.

Definition x30_induced_min_degree_log_at_least
    (G : sgraph) (S : {set G}) (cnum cden d : nat) : Prop :=
  forall v : induced S, cden * #|N(v)| >= cnum * trunc_log 2 d.

Definition x30_bipartite_induced_log_min_degree
    (G : sgraph) (cnum cden d : nat) : Prop :=
  exists S : {set G},
    S != set0 /\
    bipartite (induced S) /\
    x30_induced_min_degree_log_at_least S cnum cden d.

(** Corpus row: arxiv:1802.03727#02
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/1802.03727__02/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/1802.03727__02.json
    English statement: (Esperet, Kang, Thomasse 2018, arXiv:1802.03727 Conjecture 1.5)
      There is a positive rational constant C = cnum/cden such that for every d >= 2 and every
      non-empty triangle-free graph G of minimum degree at least d, some non-empty vertex set
      induces a bipartite subgraph in which every vertex has degree at least C * floor(log_2 d).
    Definitions: [x30_min_degree_at_least G d] - every vertex has at least d neighbours (X30.v);
      [x30_induced_min_degree_log_at_least G S cnum cden d] - every vertex of the subgraph
      induced on S satisfies cden * deg >= cnum * floor(log_2 d) (X30.v);
      [x30_bipartite_induced_log_min_degree] - existence of such a non-empty S inducing a
      bipartite graph (X30.v); [triangle_free], [bipartite], [induced] - GTBase /
      coq-graph-theory; [trunc_log 2] - MathComp floor-log2.
    Notes: the corpus records this row as SOLVED (by Kwan, Sudakov and Tran). The constant is a
      ratio of positive naturals and the logarithm is [trunc_log 2]; the guard 2 <= d keeps
      floor(log_2 d) positive, and S != set0 keeps the conclusion from holding vacuously. *)
Definition triangle_free_min_degree_log_bipartite_induced_statement : Prop :=
  exists cnum cden : nat,
    0 < cnum /\ 0 < cden /\
    forall (d : nat) (G : sgraph),
      2 <= d ->
      0 < #|G| ->
      triangle_free G ->
      x30_min_degree_at_least G d ->
      x30_bipartite_induced_log_min_degree G cnum cden d.
