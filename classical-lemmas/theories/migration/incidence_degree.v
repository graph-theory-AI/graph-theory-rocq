(** A10 incidence degree (classical): the frozen [edeg] of König's line-colouring module, the
    number of members of a supplied family [F : {set {set G}}] containing [v].  It has no
    [F \subset E(G)] premise; the lemmas of [konig/line_colouring.v] that need one state it.
    Baseline, hashes and exact substitutions are recorded in
    meta/migration_reports/incidence_degree.spec.json.  [edeg_compat] is a conversion to
    [GTBase.incidence.incidence_degree]. *)
From mathcomp Require Import all_boot.
From GraphTheory Require Import preliminaries digraph sgraph connectivity.
From GTBase Require Import incidence.
From ClassicalLemmas Require Import konig.line_colouring.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Legacy.

Definition edeg (G : sgraph) (F : {set {set G}}) (v : G) : nat :=
  #|[set e in F | v \in e]|.

End Legacy.

Lemma edeg_compat (G : sgraph) (F : {set {set G}}) (v : G) : Legacy.edeg F v = edeg F v.
Proof. by []. Qed.
