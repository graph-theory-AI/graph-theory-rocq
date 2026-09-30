(** * Extremal.conjectures.X57 -- v2 sparse strong EH row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X57 vocabulary ************************************************)

Definition x57_anticomplete (G : sgraph) (A B : {set G}) : Prop :=
  [disjoint A & B] /\
  forall a b : G, a \in A -> b \in B -> a -- b -> False.

Definition x57_induced_free (G H : sgraph) : Prop :=
  forall S : {set G}, ~ inhabited (induced S ≃ H).

Definition x57_sparse_strong_eh_property (H : sgraph) : Prop :=
  exists eps_num eps_den : nat,
    0 < eps_num /\ eps_num <= eps_den /\
    forall G : sgraph,
      2 <= #|G| ->
      x57_induced_free G H ->
      (exists v : G, eps_num * #|G| <= eps_den * #|N(v)|) \/
      (exists A B : {set G},
        x57_anticomplete A B /\
        eps_num * #|G| <= eps_den * #|A| /\
        eps_num * #|G| <= eps_den * #|B|).

(** Corpus row: arxiv:1810.00811#00
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/1810.00811__00/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/1810.00811__00.json
    English statement: (Liebenau, Pilipczuk, Seymour, Spirkl 2018, arXiv:1810.00811 Conjecture 1.5)
      A graph H has the sparse strong Erdos-Hajnal property if and only if H is a forest, where
      H has that property when there is a positive rational eps <= 1 such that every graph G on
      at least 2 vertices with no induced copy of H either has a vertex of degree at least
      eps * |V(G)| or has two anticomplete vertex sets A, B each of size at least eps * |V(G)|.
    Definitions: [x57_anticomplete G A B] - A and B are disjoint with no edge between them (X57.v);
      [x57_induced_free G H] - no vertex set of G induces a copy of H (X57.v);
      [x57_sparse_strong_eh_property H] - the dichotomy above (X57.v); [is_forest] -
      coq-graph-theory.
    Notes: eps is the ratio eps_num/eps_den with 0 < eps_num <= eps_den, and both size bounds are
      cleared of the division. The corpus records this row as SOLVED. *)
Definition sparse_strong_eh_iff_forest_statement : Prop :=
  forall H : sgraph,
    x57_sparse_strong_eh_property H <-> is_forest [set: H].
