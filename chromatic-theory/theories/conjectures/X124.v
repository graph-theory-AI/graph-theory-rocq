(** * Chromatic.conjectures.X124 -- v2 merge-width polynomial chi-boundedness row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X124 vocabulary ***********************************************)

Fixpoint x124_poly_eval (p : seq nat) (x : nat) : nat :=
  if p is a :: q then a + x * x124_poly_eval q x else 0.

(** Clique number omega(G). *)
Definition x124_omega (G : sgraph) : nat := \max_(S : {set G} | cliqueb S) #|S|.

(** Polynomially chi-bounded class: one polynomial bounds chi in terms of omega
    across every member.  This CONCLUSION is faithful. *)
Definition x124_poly_chi_bounded (C : sgraph -> Prop) : Prop :=
  exists p : seq nat,
    forall G : sgraph, C G -> χ([set: G]) <= x124_poly_eval p (x124_omega G).

Inductive x124_merge_expr (k : nat) : Type :=
| x124_vertex of 'I_k
| x124_disjoint of x124_merge_expr k & x124_merge_expr k
| x124_join_labels of 'I_k & 'I_k & x124_merge_expr k
| x124_relabel of ('I_k -> 'I_k) & x124_merge_expr k
| x124_merge_label of 'I_k & x124_merge_expr k.

Fixpoint x124_expr_leaves k (e : x124_merge_expr k) : nat :=
  match e with
  | x124_vertex _ => 1
  | x124_disjoint e1 e2 => x124_expr_leaves e1 + x124_expr_leaves e2
  | x124_join_labels _ _ e1 => x124_expr_leaves e1
  | x124_relabel _ e1 => x124_expr_leaves e1
  | x124_merge_label _ e1 => x124_expr_leaves e1
  end.

Record x124_merge_realisation (G : sgraph) (k : nat) (e : x124_merge_expr k) := {
  x124_premerge_vertices : finType;
  x124_premerge_label : x124_premerge_vertices -> 'I_k;
  x124_premerge_edge : rel x124_premerge_vertices;
  x124_premerge_map : x124_premerge_vertices -> G;
  x124_premerge_surj : forall v : G, exists x, x124_premerge_map x = v;
  x124_premerge_edge_sound :
    forall x y, x124_premerge_edge x y -> x124_premerge_map x -- x124_premerge_map y;
  x124_premerge_edge_complete :
    forall u v : G, u -- v ->
      exists x y, [/\ x124_premerge_map x = u,
                    x124_premerge_map y = v & x124_premerge_edge x y];
  x124_premerge_width_used : #|{: x124_premerge_vertices}| <= x124_expr_leaves e
}.

Definition x124_merge_width_le (C : sgraph -> Prop) (w : nat) : Prop :=
  forall G : sgraph,
    C G ->
    exists (k : nat) (e : x124_merge_expr k),
      k <= w /\ exists _ : x124_merge_realisation G e, True.

Definition x124_bounded_merge_width (C : sgraph -> Prop) : Prop :=
  exists w : nat, x124_merge_width_le C w.

(** ** X124 statements *****************************************************)

(** Corpus row: studies:std_dreier_toru_czyk_conjecture_merge_width_polynomi
    Site: none
    Review: none
    English statement: (Dreier and Torunczyk, studies slice of the corpus)
      For every class C of finite simple graphs, if C has bounded merge-width then C is polynomially
      chi-bounded, that is, some polynomial with natural coefficients p satisfies chi(G) <=
      p(omega(G)) for every G in C.
    Definitions: [x124_poly_chi_bounded C] - one coefficient list bounds chi by its Horner
      evaluation at omega, uniformly over the class (this file); [x124_merge_expr k] - the syntax of
      labelled merge expressions with vertex, disjoint union, join-labels, relabel and merge-label
      constructors (this file); [x124_merge_realisation G e] - a record presenting G as the image of
      a labelled pre-merge structure whose vertex count is bounded by the number of leaves of e
      (this file); [x124_merge_width_le C w] and [x124_bounded_merge_width C] - every member has
      such a realisation from an expression with at most w labels (this file).
    Notes: KNOWN UNFAITHFUL ANTECEDENT, corpus leg blocked. The faithfulness audit of 2026-07-17,
      recorded in meta/BLOCKED_RETARGETING_AUDIT.md and in the row's verification_note, found that
      the merge expression e is consumed only through [x124_expr_leaves e], a single natural
      bounding the size of the pre-merge vertex type, while the join-labels, relabel and merge-label
      constructors impose nothing on the edge relation. The antecedent is therefore satisfiable by
      every class and the implication degenerates to the false claim that every class of graphs is
      polynomially chi-bounded. The CONCLUSION [x124_poly_chi_bounded] is faithful. The body is left
      untouched here, WP4 changes comments only. *)
Definition dreier_torunczyk_merge_width_poly_chi_bounded_statement : Prop :=
  forall C : sgraph -> Prop,
    x124_bounded_merge_width C -> x124_poly_chi_bounded C.
