(** * Digraph.conjectures.X90 -- v2 F-subdivision complexity row *)

From HB Require Import structures.
From mathcomp Require Import all_boot.
From Digraph Require Import prelude digraph oriented.
From Digraph.conjectures Require Import X2.
From GTBase Require Import base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X90 vocabulary ************************************************)

Definition x90_problem := diGraphType -> Prop.

Definition x90_enc_digraph (D : diGraphType) : data :=
  enc_list [seq enc_list [seq enc_bool (i --> j) | j <- enum D] | i <- enum D].

Definition x90_polynomial_time_decidable (P : x90_problem) : Prop :=
  polytime_decides_on_class x90_enc_digraph (fun _ : diGraphType => True) P.

Definition x90_many_one_poly_reduces (P Q : x90_problem) : Prop :=
  exists (red : diGraphType -> diGraphType) (p : prog),
    [/\ poly_cost_on x90_enc_digraph p,
        (forall D : diGraphType,
            prun p (x90_enc_digraph D) = x90_enc_digraph (red D)) &
        forall D : diGraphType, P D <-> Q (red D)].

Definition x90_cert_input : Type := (diGraphType * data)%type.

Definition x90_enc_cert_input (I : x90_cert_input) : data :=
  Dpair (x90_enc_digraph I.1) I.2.

Definition x90_in_np (P : x90_problem) : Prop :=
  exists (verifier : prog) (c k : nat),
    poly_cost_on x90_enc_cert_input verifier /\
    forall D : diGraphType,
      P D <->
      exists cert : data,
        dsize cert <= c * (dsize (x90_enc_digraph D)) ^ k + c /\
        prun verifier (x90_enc_cert_input (D, cert)) = Dnat 1.

Definition x90_np_complete (P : x90_problem) : Prop :=
  x90_in_np P /\
  forall Q : x90_problem, x90_in_np Q -> x90_many_one_poly_reduces Q P.

Definition x90_f_subdivision_problem (F : diGraphType) : x90_problem :=
  fun D : diGraphType => contains_subdivision F D.

(** ** X90 statements ******************************************************)

(** Corpus row: studies:std_bang_jensen_et_al_conjecture_f_subdivision_compl
    Site: none
    Review: none
    English statement: (Bang-Jensen et al., F-Subdivision complexity dichotomy)
      For every finite digraph F, the problem of deciding whether an input digraph contains a
      subdivision of F is either decidable in polynomial time or NP-complete.
    Definitions: [x90_f_subdivision_problem F] - the decision problem given by
      [contains_subdivision F] (this file, using conjectures/X2.v);
      [x90_polynomial_time_decidable] / [x90_in_np] / [x90_np_complete] /
      [x90_many_one_poly_reduces] - the complexity notions over the shared cost-coupled
      interpreter [prog], [prun], [poly_cost_on], [polytime_decides_on_class] of GTBase
      complexity.v (this file); [x90_enc_digraph] - the adjacency-matrix encoding (this file).
    Notes: Statement and cost live in the same syntax, which avoids the decoupled-cost vacuity
      of an earlier model; faithfulness is relative to that computation model. Problems are
      predicates on [diGraphType] and instances are encoded by adjacency matrices. *)
Definition f_subdivision_complexity_dichotomy_statement : Prop :=
  forall F : diGraphType,
    x90_polynomial_time_decidable (x90_f_subdivision_problem F) \/
    x90_np_complete (x90_f_subdivision_problem F).
