(** * D1: uniform finite hypergraphs, Chromatic certificate

    Frozen at the C25 mathematical baseline 3be65eed7084abfae36dee74f7117b598325bc4c:
    [Legacy.uniform_hg] (the indexed "every label has d points" predicate over the unchanged
    U5 [hypergraph] Record; the live helper now unfolds to
    [GTBase.hypergraph_uniformity.uniform_incidence (@hinc H) d]) and the complete current U5
    row with d >= 1, [simple_hg], the codegree bound and the edge-label colouring kept. *)
From GraphTheory Require Import mgraph.
From GTBase Require Import base.
Require Chromatic.conjectures.U5.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Legacy.
Import Chromatic.conjectures.U5.

Definition uniform_hg (H : hypergraph) (d : nat) : Prop :=
  forall e : he H, #|hinc e| = d.

End Legacy.

Module U5UniformLegacy.
Import Chromatic.conjectures.U5.

Definition a_generalization_of_vizings_theorem_statement : Prop :=
  forall (H : hypergraph) (d r : nat),
    1 <= d -> Legacy.uniform_hg H d -> simple_hg H -> hg_codegree_le H d r ->
    exists c : he H -> 'I_(r + d - 1),
      forall e e' : he H,
        e != e' -> #|hinc e :&: hinc e'| = d.-1 -> c e != c e'.

End U5UniformLegacy.

Lemma uniform_hg_compat (H : Chromatic.conjectures.U5.hypergraph) (d : nat) :
  @Legacy.uniform_hg H d <->
  @Chromatic.conjectures.U5.uniform_hg H d.
Proof.
exact: iff_refl.
Qed.

Lemma a_generalization_of_vizings_theorem_statement_compat :
  U5UniformLegacy.a_generalization_of_vizings_theorem_statement <->
  Chromatic.conjectures.U5.a_generalization_of_vizings_theorem_statement.
Proof.
exact: iff_refl.
Qed.

Print Assumptions uniform_hg_compat.
Print Assumptions a_generalization_of_vizings_theorem_statement_compat.
