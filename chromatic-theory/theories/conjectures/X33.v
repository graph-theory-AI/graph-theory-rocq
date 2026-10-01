(** * Chromatic.conjectures.X33 -- v2 total list-colouring row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X33 vocabulary ************************************************)

Definition x33_edge_set (G : sgraph) : {set {set G}} :=
  simple_edge_set G.

Definition x33_total_vertex (G : sgraph) : Type :=
  (G + {e : {set G} | e \in x33_edge_set G})%type.

Definition x33_total_rel (G : sgraph) : rel (x33_total_vertex G) :=
  fun a b =>
    match a, b with
    | inl x, inl y => x -- y
    | inr e, inr f => (val e != val f) && (val e :&: val f != set0)
    | inl x, inr e => x \in val e
    | inr e, inl x => x \in val e
    end.

Lemma x33_total_rel_sym (G : sgraph) : symmetric (@x33_total_rel G).
Proof.
move=> [x|e] [y|f] //=.
- by rewrite sg_sym.
- by rewrite eq_sym setIC.
Qed.

Lemma x33_total_rel_irrefl (G : sgraph) : irreflexive (@x33_total_rel G).
Proof. by move=> [x|e] //=; rewrite ?sg_irrefl ?eqxx. Qed.

Definition x33_total_graph (G : sgraph) : sgraph :=
  SGraph (@x33_total_rel_sym G) (@x33_total_rel_irrefl G).

(** ** X33 statements ******************************************************)

(** arXiv:1904.12060, total list-colouring conjecture. *)
Definition total_list_colouring_delta_plus_two_statement : Prop :=
  forall G : sgraph,
    choosable (x33_total_graph G) (Delta G + 2).
