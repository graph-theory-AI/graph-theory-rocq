(** * Minor.conjectures.X42 -- v2 bounded treewidth forbidden-subgraph row *)

From GTBase Require Export base.
From Minor.conjectures Require Import X27.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X42 vocabulary ************************************************)

Definition x42_diamond_rel (u v : bool + bool) : bool :=
  match u, v with
  | inl a, inl b => a != b
  | inl _, inr _ => true
  | inr _, inl _ => true
  | inr _, inr _ => false
  end.

Lemma x42_diamond_sym : symmetric x42_diamond_rel.
Proof. by move=> [a|a] [b|b] //=; rewrite eq_sym. Qed.

Lemma x42_diamond_irrefl : irreflexive x42_diamond_rel.
Proof. by move=> [a|a] //=; rewrite eqxx. Qed.

Definition x42_diamond : sgraph := SGraph x42_diamond_sym x42_diamond_irrefl.

Definition x42_induced_free (G H : sgraph) : Prop :=
  forall S : {set G}, ~ inhabited (induced S ≃ H).

(** ** X42 statements ******************************************************)

(** Corpus row: arxiv:2001.01607#00
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/2001.01607__00/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/2001.01607__00.json
    English statement: (Pilipczuk, Sintiari, Thomasse and Trotignon 2020, open question in
      "(Theta, triangle)-free and (even hole, K_4)-free graphs. Part 2: bounds on treewidth")
      There is a constant c such that every finite simple graph that contains no even hole, no
      induced K_4 and no induced diamond has treewidth at most c.
    Definitions: [x42_diamond_rel], [x42_diamond] - the diamond, i.e. K_4 minus one edge, built
      on the sum type bool + bool with the two right-hand vertices non-adjacent and all other
      pairs adjacent (minor-theory/theories/conjectures/X42.v); [x42_induced_free G H] - no
      subgraph of G induced on a vertex set is isomorphic to H (same file);
      [x27_even_hole_free G] - G has no induced cycle of even length on more than three vertices
      (minor-theory/theories/conjectures/X27.v); [x27_treewidth_at_most G c] - G admits a
      tree-decomposition all of whose bags have at most c+1 vertices (same file).
    Notes: the single constant c is quantified before G, which is what "bounded treewidth" for
      the whole class means.  The source asks for bounded treewidth OR bounded cliquewidth;
      only the treewidth half is formalised here, which is the stronger of the two (bounded
      treewidth implies bounded cliquewidth).  The corpus records this row as partial. *)
Definition even_hole_k4_diamond_free_bounded_treewidth_statement : Prop :=
  exists c : nat,
    forall G : sgraph,
      x27_even_hole_free G ->
      x42_induced_free G 'K_4 ->
      x42_induced_free G x42_diamond ->
      x27_treewidth_at_most G c.
