(** * Extremal.conjectures.X180 -- v2 logarithmic-degree multitasker row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X180 vocabulary ***********************************************)

Definition x180_matching (G : sgraph) (M : {set {set G}}) : Prop :=
  M \subset fg_edges G /\
  forall e f : {set G}, e \in M -> f \in M -> e != f -> e :&: f = set0.

Definition x180_induced_matching (G : sgraph) (M : {set {set G}}) : Prop :=
  x180_matching M /\
  forall e f : {set G}, e \in M -> f \in M -> e != f ->
    forall x y : G, x \in e -> y \in f -> ~~ (x -- y).

Definition x180_multitasker_capacity_at_least (G : sgraph) (a b : nat) : Prop :=
  0 < b /\
  forall M : {set {set G}},
    x180_matching M ->
    exists I : {set {set G}},
      I \subset M /\ x180_induced_matching I /\ b * #|I| >= a * #|M|.

Definition x180_multitasker_capacity_positive (G : sgraph) : Prop :=
  exists a b : nat, 0 < a /\ x180_multitasker_capacity_at_least G a b.

Definition x180_average_degree_logarithmic (G : sgraph) : Prop :=
  exists c C : nat,
    0 < c /\ 0 < C /\
    c * #|G| * (trunc_log 2 #|G|).+1 <= 2 * fg_edge_count G /\
    2 * fg_edge_count G <= C * #|G| * (trunc_log 2 #|G|).+1.

(** Corpus row: arxiv:1611.02400#01
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/1611.02400__01/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/1611.02400__01.json
    English statement: (Alon, Cohen, Dey, Griffiths, Musslick, Ozcimder, Reichman, Shinkar, Wagner 2016, arXiv:1611.02400, Open Problem on multitaskers at average degree Theta(log n))
      For every n0 there is a graph G with at least n0 vertices whose average degree is of
      order log |V(G)| (bounded above and below by constant multiples of
      |V(G)| * (floor(log_2 |V(G)|) + 1)) and whose multitasking capacity is positive: there
      are a > 0 and b > 0 such that every matching M of G contains an induced submatching I
      with b * |I| >= a * |M|.
    Definitions: [x180_matching G M] - M is a set of edges (2-element vertex sets from [fg_edges G]) that
      are pairwise disjoint (X180.v); [x180_induced_matching G M] - a matching with no edge of
      G between two of its edges (X180.v); [x180_multitasker_capacity_at_least G a b] - every
      matching has an induced submatching of relative size at least a/b (X180.v);
      [x180_multitasker_capacity_positive G] - such a positive ratio exists (X180.v);
      [x180_average_degree_logarithmic G] - the degree sum is between c and C times
      |V(G)| * (floor(log_2 |V(G)|) + 1) for some positive c, C (X180.v); [fg_edges],
      [fg_edge_count] - GTBase; [trunc_log 2] - MathComp floor-log2.
    Notes: this row is recorded as BLOCKED. The 2026-07-17 faithfulness audit
      (meta/BLOCKED_RETARGETING_AUDIT.md) found a mis-quantification: the source asks for a
      multitasker family whose capacity alpha > 0 is INDEPENDENT of n, but in the body the
      capacity ratio a/b is chosen INSIDE [x180_multitasker_capacity_positive G], i.e. per
      graph, so a family whose capacity tends to 0 still satisfies it. Likewise the constants c,
      C of the average-degree condition are chosen per graph. The statement is therefore too
      weak (ledger). The same collapse family as X125. *)
Definition log_degree_multitasker_exists_statement : Prop :=
  forall n0 : nat,
    exists G : sgraph,
      n0 <= #|G| /\
      x180_average_degree_logarithmic G /\
      x180_multitasker_capacity_positive G.
