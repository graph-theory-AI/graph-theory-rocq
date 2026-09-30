(** * Packing.conjectures.X18 -- v2 fair representation continuation rows *)

From GTBase Require Export base.
From Packing.conjectures Require Import X15.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X18 vocabulary ************************************************)

Definition x18_path_rel (n : nat) : rel 'I_n :=
  fun i j => (i != j) && (((val i).+1 == val j) || ((val j).+1 == val i)).

Lemma x18_path_sym (n : nat) : symmetric (@x18_path_rel n).
Proof.
by move=> i j; rewrite /x18_path_rel eq_sym orbC.
Qed.

Lemma x18_path_irrefl (n : nat) : irreflexive (@x18_path_rel n).
Proof. by move=> i; rewrite /x18_path_rel eqxx. Qed.

Definition x18_path_graph (n : nat) : sgraph :=
  SGraph (@x18_path_sym n) (@x18_path_irrefl n).

Definition x18_vertex_partition
    (G : sgraph) (m : nat) (V : 'I_m -> {set G}) : Prop :=
  (forall v : G, [exists i : 'I_m, v \in V i]) /\
  forall i j : 'I_m, i != j -> [disjoint V i & V j].

Definition x18_independent_set (G : sgraph) (S : {set G}) : Prop :=
  forall u v : G, u \in S -> v \in S -> u -- v -> False.

Definition x18_perfect_matching (G : sgraph) (M : {set {set G}}) : Prop :=
  x15_matching M /\
  forall v : G, #|[set e in M | v \in e]| = 1.

(** ** X18 statements ******************************************************)

(** Corpus row: arxiv:1611.03196#00
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/1611.03196__00/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/1611.03196__00.json
    English statement: (Aharoni, Alon, Berger, Chudnovsky, Kotlar, Loebl, Ziv 2016,
      "Conjecture 1.6")
      For all n and m and every partition V_0, ..., V_{m-1} of the vertex set of the
      path on n vertices, there are an independent set S and natural numbers
      b_0, ..., b_{m-1} such that |V_i| <= 2 * (|S intersect V_i| + b_i) for every i
      (that is, |S intersect V_i| >= |V_i|/2 - b_i), the sum of the b_i is at most m/2
      (written 2 * sum b_i <= m), and b_i <= 1 for every i.
    Definitions: [x18_path_graph n] — the path graph on 'I_n, where two indices are
      adjacent exactly when they are distinct and consecutive (this file);
      [x18_vertex_partition V] — every vertex lies in some part and distinct parts are
      disjoint (this file); [x18_independent_set S] — no two members of S are adjacent
      (this file).
    Notes: the fractional bounds |S intersect V_i| >= |V_i|/2 - b_i and
      sum b_i <= m/2 are cross-multiplied into natural-number inequalities, avoiding
      both rationals and MathComp's truncated subtraction. Both conditions (1) and (2)
      of the source are asserted simultaneously, which is the point of the
      conjecture. *)
Definition path_partition_independent_set_balance_statement : Prop :=
  forall (n m : nat) (V : 'I_m -> {set x18_path_graph n}),
    x18_vertex_partition V ->
    exists (S : {set x18_path_graph n}) (b : 'I_m -> nat),
      x18_independent_set S /\
      (forall i : 'I_m, 2 * (#|S :&: V i| + b i) >= #|V i|)%N /\
      (2 * \sum_(i : 'I_m) b i <= m)%N /\
      forall i : 'I_m, b i <= 1.

(** Corpus row: arxiv:1611.03196#01
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/1611.03196__01/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/1611.03196__01.json
    English statement: (Aharoni, Alon, Berger, Chudnovsky, Kotlar, Loebl, Ziv 2016,
      "Conjecture 1.9")
      For all n >= 1 and m, every partition E_0, ..., E_{m-1} of the edge set of the
      complete bipartite graph K_{n,n} and every distinguished index j, there is a
      perfect matching F of K_{n,n} such that |F intersect E_i| >= floor(|E_i|/n) for
      every i different from j, and |F intersect E_j| >= floor(|E_j|/n) - 1.
    Definitions: [x18_perfect_matching F] — a matching in which every vertex lies in
      exactly one edge (this file, on top of [x15_matching]); [x15_matching],
      [x15_edge_partition], [x15_edge_set] — X15.v; [KB n n] — the complete bipartite
      graph (GTBase base).
    Notes: floor(|E_j|/n) - 1 is MathComp natural subtraction, which truncates at 0;
      this is harmless because it occurs as a lower bound. Guard 0 < n excludes the
      empty graph. The corpus row is partial: proved for m = 2 and m = 3 in the source
      paper. *)
Definition knn_fair_perfect_matching_statement : Prop :=
  forall (n m : nat) (E : 'I_m -> {set {set KB n n}}) (j : 'I_m),
    0 < n ->
    x15_edge_partition E ->
    exists F : {set {set KB n n}},
      x18_perfect_matching F /\
      (forall i : 'I_m, i != j -> (#|E i| %/ n <= #|F :&: E i|)%N) /\
      (#|E j| %/ n - 1 <= #|F :&: E j|)%N.

(** Corpus row: studies:std_brualdi_stein_conjecture
    Site: none
    Review: none
    English statement: (Brualdi and Stein, "Brualdi-Stein conjecture")
      For every n >= 1, if the edge set of the complete bipartite graph K_{n,n} is
      partitioned into n parts E_0, ..., E_{n-1} each of exactly n edges, then there is
      a matching M of K_{n,n} with at least n-1 edges that uses at most one edge from
      each part.
    Definitions: [x15_matching], [x15_edge_partition], [x15_edge_set] — X15.v;
      [KB n n] — the complete bipartite graph (GTBase base).
    Notes: "a matching consisting of one edge from all but possibly one E_i" is
      rendered as the conjunction of |M| >= n-1 and |M intersect E_i| <= 1 for every i;
      n.-1 is MathComp's predecessor. Guard 0 < n excludes the empty graph. *)
Definition brualdi_stein_partial_transversal_statement : Prop :=
  forall (n : nat) (E : 'I_n -> {set {set KB n n}}),
    0 < n ->
    x15_edge_partition E ->
    (forall i : 'I_n, #|E i| = n) ->
    exists M : {set {set KB n n}},
      x15_matching M /\
      (n.-1 <= #|M|)%N /\
      forall i : 'I_n, #|M :&: E i| <= 1.
