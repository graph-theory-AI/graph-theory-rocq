(** * GTMisc.conjectures.X163 -- v2 random graph normality row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X163 vocabulary ***********************************************)

Definition x163_stableb (G : sgraph) (S : {set G}) : bool :=
  [forall x in S, [forall y in S, (x == y) || ~~ (x -- y)]].

Definition x163_normal_graphb (G : sgraph) : bool :=
  [exists K : {set {set G}},
    [exists A : {set {set G}},
      [forall C in K, cliqueb C] &&
      [forall S in A, x163_stableb S] &&
      [forall v : G, [exists C in K, v \in C]] &&
      [forall v : G, [exists S in A, v \in S]] &&
      [forall C in K, [forall S in A, C :&: S != set0]]]].

Definition x163_random_graph_whp
    (p q : nat) (P : forall n : nat, pred {set {set 'I_n}}) : Prop :=
  @fg_whp (fun n : nat => {set {set 'I_n}}) (fun n => @fg_gnp_weight p q n) P.

(** ** X163 statements *****************************************************)

(** Corpus row: arxiv:1601.01129#01
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/1601.01129__01/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/1601.01129__01.json
    English statement: (Gajser and Mohar 2016, "Minimal normal graph covers", open question on
      the normality of random graphs)
      For every rational edge probability p/q with 0 < p < q, the labelled random graph G(n,
      p/q) is normal with high probability, normality meaning that there are a family of
      cliques and a family of stable sets, each covering all vertices, such that every chosen
      clique meets every chosen stable set.
    Definitions: [x163_stableb S] - S is a stable set, in boolean form (this file);
      [x163_normal_graphb G] - the boolean clique-cover / stable-cover characterization of
      normality above (this file); [x163_random_graph_whp p q P] - P holds with high
      probability for labelled edge sets on n vertices weighted by the G(n, p/q) weight (this
      file); [fg_whp] - exact finite "with high probability", cross-multiplied natural weights
      eventually covering all but a ratio a/b of the total weight (GTBase finite_graph.v);
      [fg_gnp_weight p q n E] - the integer weight p^|E| * (q-p)^(N-|E|) of a labelled edge set
      (GTBase finite_graph.v); [fg_labelled_sgraph E] - the simple graph of a set of
      two-element vertex sets (GTBase finite_graph.v); [cliqueb] - coq-graph-theory.
    Notes: retargeted on 2026-07-16 from a blocked placeholder to this axiom-free finite-witness
      formulation, see meta/BLOCKED_RETARGETING_FOUNDATIONS.md.  Probabilities are rational,
      given by a numerator and a denominator, and the probability space is the exact finite
      counting measure on labelled edge sets given by [fg_gnp_weight]; no measure theory is
      involved.  The source says "random graphs G(n,p)" without fixing p, and the Rocq body
      quantifies over every fixed rational p strictly between 0 and 1. *)
Definition random_graphs_normal_whp_statement : Prop :=
  forall p q : nat,
    0 < p ->
    p < q ->
    x163_random_graph_whp p q
      (fun n E => x163_normal_graphb (fg_labelled_sgraph E)).
