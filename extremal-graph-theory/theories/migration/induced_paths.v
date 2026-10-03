(** * Extremal.migration.induced_paths — B22 certificates: the X98 induced path, model wrapper and row

    Frozen verbatim at the private baseline (byte-identical at B21 66279eb and C20 97605dd): the
    full-endpoint induced path [x98_induced_path_between], the C20 wrapper chain
    [x98_induced_subdivision] over the frozen public wrapper of GTBase.migration.induced_paths, and the
    complete row [polynomial_kuhn_osthus_induced_subdivision_statement] (studies slug).  Since B22 the
    live [x98_induced_path_between] is a transparent alias of
    [GTBase.induced_paths.induced_path_between], the same body by conversion (its consecutive-pair
    test was already B3's alias of [seq_consecutive]); the live [x98_induced_subdivision] still
    unfolds to the public [induced_subdivision], whose Record field now goes through the canonical
    helper.  The row copy keeps the live [x59_subgraph_of] / [x59_poly_eval] (A5 and local
    vocabulary); the complete pre-B3/A5/C19/C20/B22 row is C19's
    [X98Original.polynomial_kuhn_osthus_induced_subdivision_statement] (B3 path bodies, A5 subgraph
    relation, raw support over a fully frozen Record), reused with its own certificate.  The local
    constructor [X98Model] and its seven projections stay live with unchanged types and Arguments. *)

From GTBase Require Import base model_support induced_paths induced_subdivisions.
From GTBase.migration Require induced_paths.
From Extremal.conjectures Require Import X59 X98.
From Extremal.migration Require model_support.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module B22 := GTBase.migration.induced_paths.
Module C19 := Extremal.migration.model_support.

Module Legacy.

Definition x98_induced_path_between (G : sgraph) (a b : G) (p : seq G) : Prop :=
  match p with
  | [::] => False
  | x :: q =>
      x = a /\
      last x q = b /\
      uniq p /\
      path (--) x q /\
      forall u v : G,
        u \in p -> v \in p -> u -- v -> u != v ->
        x98_consecutive_in_path p u v
  end.

End Legacy.

Module X98Legacy.

Definition x98_induced_subdivision (H G : sgraph) : Prop := B22.Legacy.induced_subdivision H G.

Definition polynomial_kuhn_osthus_induced_subdivision_statement : Prop :=
  forall H : sgraph,
    exists p : seq nat,
      forall (s : nat) (G : sgraph),
        1 <= s ->
        ~ x59_subgraph_of (KB s s) G ->
        average_degree_geq G (x59_poly_eval p s) 1 ->
        X98Legacy.x98_induced_subdivision H G.

End X98Legacy.

(** ** Certificates *)

Lemma x98_induced_path_between_compat (G : sgraph) (a b : G) (p : seq G) :
  Legacy.x98_induced_path_between a b p <-> x98_induced_path_between a b p.
Proof. by []. Qed.

Lemma x98_induced_subdivision_compat (H G : sgraph) :
  X98Legacy.x98_induced_subdivision H G <-> x98_induced_subdivision H G.
Proof. exact: B22.induced_subdivision_compat. Qed.

Lemma polynomial_kuhn_osthus_induced_subdivision_statement_compat :
  X98Legacy.polynomial_kuhn_osthus_induced_subdivision_statement <->
  polynomial_kuhn_osthus_induced_subdivision_statement.
Proof.
split=> st H; have [p hp] := st H; exists p => s G s1 free avg.
- exact/x98_induced_subdivision_compat/(hp s G s1 free avg).
- exact/x98_induced_subdivision_compat/(hp s G s1 free avg).
Qed.

(** ** The complete Original, reused from C19 *)

Lemma polynomial_kuhn_osthus_induced_subdivision_statement_original_compat :
  Extremal.migration.model_support.X98Original.polynomial_kuhn_osthus_induced_subdivision_statement <->
  polynomial_kuhn_osthus_induced_subdivision_statement.
Proof. exact: C19.polynomial_kuhn_osthus_induced_subdivision_statement_original_compat. Qed.

Print Assumptions x98_induced_path_between_compat.
Print Assumptions x98_induced_subdivision_compat.
Print Assumptions polynomial_kuhn_osthus_induced_subdivision_statement_compat.
Print Assumptions polynomial_kuhn_osthus_induced_subdivision_statement_original_compat.
