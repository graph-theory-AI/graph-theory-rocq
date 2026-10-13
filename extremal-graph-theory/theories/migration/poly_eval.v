(** A31: natural Horner evaluation, frozen at the reviewed candidate parent db16a76376d1a9c29142b38f97d5109d6dd942fa.
    - [X59Legacy] / [X60Legacy]: the raw [Fixpoint]s [x59_poly_eval] / [x60_poly_eval] and the WHOLE current X59 / X60
      rows, verbatim; [X98Legacy]: X98's whole row, which uses X59's evaluator across modules.
    - [X59Original], [X60Original], [X98Original]: the complete deepest rows.  Each is the deepest existing Original
      ([Extremal.migration.cycle_lengths.X59Original], [delete_edge.X60Original], [model_support.X98Original], whose
      closures reach no live helper of any migrated family) with its one remaining live provider, the evaluator, replaced
      by the raw [Fixpoint] frozen here.  Each whole-row iff composes the evaluator equality with that Original's own
      registered certificate.
    The live evaluators are transparent aliases of [GTBase.poly_nat.horner_nat]; every evaluator certificate is an
    UNCONDITIONAL pointwise equality (by induction, no conversion), so every row is equivalent in every polarity.  Quantifier
    order, the [1 <= s] and [3 <= t] guards and every other conjunct are unchanged. *)
From GTBase Require Import base.
From GTBase Require poly_nat.
From Extremal.conjectures Require Import X59 X60 X98.
From Extremal.migration Require subgraph_of cycle_lengths delete_edge model_support simple_edges.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module A5 := Extremal.migration.subgraph_of.
Module CL := Extremal.migration.cycle_lengths.
Module DE := Extremal.migration.delete_edge.
Module MS := Extremal.migration.model_support.
Module SE := Extremal.migration.simple_edges.

Module X59Legacy.

Fixpoint x59_poly_eval (p : seq nat) (x : nat) : nat :=
  if p is a :: q then a + x * x59_poly_eval q x else 0.

Definition c4_free_subgraph_polynomial_average_degree_statement : Prop :=
  exists p : seq nat,
    forall (k : nat) (G : sgraph),
      average_degree_geq G (X59Legacy.x59_poly_eval p k) 1 ->
      exists H : sgraph,
        x59_subgraph_of H G /\
        ~ x59_has_cycle_length H 4 /\
        average_degree_geq H k 1.

End X59Legacy.

Module X60Legacy.

Fixpoint x60_poly_eval (p : seq nat) (x : nat) : nat :=
  if p is a :: q then a + x * x60_poly_eval q x else 0.

Definition induced_saturation_even_cycle_polynomial_size_statement : Prop :=
  exists p : seq nat,
    forall t : nat,
      3 <= t ->
      exists G : sgraph,
        #|G| <= X60Legacy.x60_poly_eval p t /\
        0 < #|x60_edge_set G| /\
        ~ x60_has_induced_cycle G (2 * t - 2) /\
        forall e : {set G},
          e \in x60_edge_set G ->
          x60_has_induced_cycle (@x60_delete_edge_graph G e) (2 * t - 2).

End X60Legacy.

Module X98Legacy.

Definition polynomial_kuhn_osthus_induced_subdivision_statement : Prop :=
  forall H : sgraph,
    exists p : seq nat,
      forall (s : nat) (G : sgraph),
        1 <= s ->
        ~ x59_subgraph_of (KB s s) G ->
        average_degree_geq G (X59Legacy.x59_poly_eval p s) 1 ->
        x98_induced_subdivision H G.

End X98Legacy.

Module X59Original.

Definition c4_free_subgraph_polynomial_average_degree_statement : Prop :=
  exists p : seq nat,
    forall (k : nat) (G : sgraph),
      average_degree_geq G (X59Legacy.x59_poly_eval p k) 1 ->
      exists H : sgraph,
        A5.Legacy.x59_subgraph_of H G /\
        ~ CL.Legacy.x59_has_cycle_length H 4 /\
        average_degree_geq H k 1.

End X59Original.

Module X60Original.

Definition induced_saturation_even_cycle_polynomial_size_statement : Prop :=
  exists p : seq nat,
    forall t : nat,
      3 <= t ->
      exists G : sgraph,
        #|G| <= X60Legacy.x60_poly_eval p t /\
        0 < #|SE.Legacy.edge_set G| /\
        ~ x60_has_induced_cycle G (2 * t - 2) /\
        forall e : {set G},
          e \in SE.Legacy.edge_set G ->
          x60_has_induced_cycle (@DE.Legacy.x60_delete_edge_graph G e) (2 * t - 2).

End X60Original.

Module X98Original.

Definition polynomial_kuhn_osthus_induced_subdivision_statement : Prop :=
  forall H : sgraph,
    exists p : seq nat,
      forall (s : nat) (G : sgraph),
        1 <= s ->
        ~ A5.Legacy.x59_subgraph_of (KB s s) G ->
        average_degree_geq G (X59Legacy.x59_poly_eval p s) 1 ->
        MS.X98Original.x98_induced_subdivision H G.

End X98Original.

(** The raw evaluators equal the live ones (the canonical [horner_nat]) at every list and point. *)
Lemma x59_poly_eval_compat (p : seq nat) (x : nat) : X59Legacy.x59_poly_eval p x = x59_poly_eval p x.
Proof.
rewrite /x59_poly_eval; elim: p => [|a p IH]; first by rewrite GTBase.poly_nat.horner_nat_nil.
have -> : X59Legacy.x59_poly_eval (a :: p) x = a + x * X59Legacy.x59_poly_eval p x by [].
by rewrite IH GTBase.poly_nat.horner_nat_cons.
Qed.

Lemma x60_poly_eval_compat (p : seq nat) (x : nat) : X60Legacy.x60_poly_eval p x = x60_poly_eval p x.
Proof.
rewrite /x60_poly_eval; elim: p => [|a p IH]; first by rewrite GTBase.poly_nat.horner_nat_nil.
have -> : X60Legacy.x60_poly_eval (a :: p) x = a + x * X60Legacy.x60_poly_eval p x by [].
by rewrite IH GTBase.poly_nat.horner_nat_cons.
Qed.

Lemma c4_free_subgraph_polynomial_average_degree_statement_compat :
  X59Legacy.c4_free_subgraph_polynomial_average_degree_statement <->
  c4_free_subgraph_polynomial_average_degree_statement.
Proof.
split=> -[p h]; exists p => k G avg; apply: h.
- by rewrite x59_poly_eval_compat.
- by rewrite -x59_poly_eval_compat.
Qed.

Lemma induced_saturation_even_cycle_polynomial_size_statement_compat :
  X60Legacy.induced_saturation_even_cycle_polynomial_size_statement <->
  induced_saturation_even_cycle_polynomial_size_statement.
Proof.
split=> -[p h]; exists p => t t3; have [G hG] := h t t3; exists G.
- by rewrite -x60_poly_eval_compat.
- by rewrite x60_poly_eval_compat.
Qed.

Lemma polynomial_kuhn_osthus_induced_subdivision_statement_compat :
  X98Legacy.polynomial_kuhn_osthus_induced_subdivision_statement <->
  polynomial_kuhn_osthus_induced_subdivision_statement.
Proof.
split=> st H; have [p h] := st H; exists p => s G s1 nKB avg.
- by apply: (h s G s1 nKB); rewrite x59_poly_eval_compat.
- by apply: (h s G s1 nKB); rewrite -x59_poly_eval_compat.
Qed.

(** The deepest rows: the evaluator equality, then the earlier Original's own whole-row certificate. *)
Lemma c4_free_subgraph_polynomial_average_degree_statement_original_compat :
  X59Original.c4_free_subgraph_polynomial_average_degree_statement <->
  c4_free_subgraph_polynomial_average_degree_statement.
Proof.
rewrite -CL.c4_free_subgraph_polynomial_average_degree_statement_original_compat.
split=> -[p h]; exists p => k G avg; apply: h.
- by rewrite x59_poly_eval_compat.
- by rewrite -x59_poly_eval_compat.
Qed.

Lemma induced_saturation_even_cycle_polynomial_size_statement_original_compat :
  X60Original.induced_saturation_even_cycle_polynomial_size_statement <->
  induced_saturation_even_cycle_polynomial_size_statement.
Proof.
rewrite -DE.induced_saturation_even_cycle_polynomial_size_statement_original_compat.
split=> -[p h]; exists p => t t3; have [G hG] := h t t3; exists G.
- by rewrite -x60_poly_eval_compat.
- by rewrite x60_poly_eval_compat.
Qed.

Lemma polynomial_kuhn_osthus_induced_subdivision_statement_original_compat :
  X98Original.polynomial_kuhn_osthus_induced_subdivision_statement <->
  polynomial_kuhn_osthus_induced_subdivision_statement.
Proof.
rewrite -MS.polynomial_kuhn_osthus_induced_subdivision_statement_original_compat.
split=> st H; have [p h] := st H; exists p => s G s1 nKB avg.
- by apply: (h s G s1 nKB); rewrite x59_poly_eval_compat.
- by apply: (h s G s1 nKB); rewrite -x59_poly_eval_compat.
Qed.
