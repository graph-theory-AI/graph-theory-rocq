(** * D1: uniform finite hypergraphs, Extremal certificate

    Frozen at the C25 mathematical baseline 3be65eed7084abfae36dee74f7117b598325bc4c:
    [Legacy.uniform_hypergraph] (raw set-family uniformity; the live D2str helper now unfolds
    to [GTBase.hypergraph_uniformity.uniform_family]) and the complete current D2str row with
    one partition for both families, N chosen after r, a, b and before the families, and both
    inequalities. *)
From GTBase Require Import base.
From mathcomp Require Import all_algebra.
Import GRing.Theory Num.Theory.
Require Extremal.conjectures.D2str.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Legacy.

Definition uniform_hypergraph (T : finType) (E : {set {set T}}) (r : nat) : Prop :=
  forall e : {set T}, e \in E -> #|e| = r.

End Legacy.

Module D2strUniformLegacy.
Import Extremal.conjectures.D2str.

Definition simultaneous_partition_of_hypergraphs_statement : Prop :=
  forall (r a b : nat), 0 < r -> 0 < a -> 0 < b ->
    exists N : nat,
      forall (T : finType) (E1 E2 : {set {set T}}),
        Legacy.uniform_hypergraph E1 r -> Legacy.uniform_hypergraph E2 r ->
        N <= #|E1| -> N <= #|E2| ->
        exists part : T -> 'I_r,
          (b * (r ^ r) * #|[set e in E1 | rainbow part e]| + a * (r ^ r) * #|E1|
             >= b * (factorial r) * #|E1|)%N /\
          (b * (r ^ r) * #|[set e in E2 | rainbow part e]| + a * (r ^ r) * #|E2|
             >= b * (factorial r) * #|E2|)%N.

End D2strUniformLegacy.

Lemma uniform_hypergraph_compat (T : finType) (E : {set {set T}}) (r : nat) :
  @Legacy.uniform_hypergraph T E r <->
  @Extremal.conjectures.D2str.uniform_hypergraph T E r.
Proof.
exact: iff_refl.
Qed.

Lemma simultaneous_partition_of_hypergraphs_statement_compat :
  D2strUniformLegacy.simultaneous_partition_of_hypergraphs_statement <->
  Extremal.conjectures.D2str.simultaneous_partition_of_hypergraphs_statement.
Proof.
exact: iff_refl.
Qed.

Print Assumptions uniform_hypergraph_compat.
Print Assumptions simultaneous_partition_of_hypergraphs_statement_compat.
