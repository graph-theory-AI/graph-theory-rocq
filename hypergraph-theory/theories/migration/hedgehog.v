(** * D7: the finite hedgehog hypergraph, Hypergraph certificate

    Frozen at the D6 pin eaa6564c3788f6e3e2db7a7bddbe9adba157c334, the family baseline of
    meta/migration_reports/hedgehog.spec.json.
    - [HedgehogLegacy]: X117's [x117_spike], [x117_vertex], [x117_edge] and [x117_edges], verbatim, calling
      one another only through this module.  The four sources now unfold to the public
      [Hypergraph.foundations.hedgehog] constructors, with the same ordered-pair subtype, sum carrier,
      tagged triple and image family.
    - [X117HedgehogLegacy]: the Ramsey-number chain (forcing at [R] and minimality) and the complete
      current row.  These current copies keep the live D5 forcing alias [x117_forces_mono].
    - [X117HedgehogOriginal]: the complete D3+D4+D5+D7 Original chain and row, over the raw constructors
      and D3's actual frozen [IM.X117ImageLegacy.x117_forces_mono] (raw copy and image), reached through
      the alias [IM] (no Import).
    The six older partial snapshots (D3 X117ImageLegacy, D4 X117CopyLegacy and D5 X117ForcingLegacy, each
    with its Ramsey chain and row) stay as they are; the spec records them and points to these rows. *)
From GTBase Require Import base.
Require Hypergraph.foundations.hedgehog.
Require Hypergraph.conjectures.X117.
Require Hypergraph.migration.image_edge.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module IM := Hypergraph.migration.image_edge.

Module HedgehogLegacy.

Definition x117_spike (t : nat) : Type := {p : 'I_t * 'I_t | p.1 < p.2}.

Definition x117_vertex (t : nat) : Type := ('I_t + HedgehogLegacy.x117_spike t)%type.

Definition x117_edge (t : nat) (s : HedgehogLegacy.x117_spike t) : {set HedgehogLegacy.x117_vertex t} :=
  [set inl (sval s).1; inl (sval s).2; inr s].

Definition x117_edges (t : nat) : {set {set HedgehogLegacy.x117_vertex t}} :=
  [set HedgehogLegacy.x117_edge s | s : HedgehogLegacy.x117_spike t].

End HedgehogLegacy.

Module X117HedgehogLegacy.
Import Hypergraph.conjectures.X117.

Definition x117_ramsey_number (t R : nat) : Prop :=
  x117_forces_mono (HedgehogLegacy.x117_edges t) R /\
  forall N : nat, x117_forces_mono (HedgehogLegacy.x117_edges t) N -> R <= N.

Definition conlon_fox_rodl_hedgehog_ramsey_statement : Prop :=
  forall e1 e2 : nat,
    0 < e1 -> 0 < e2 ->
    exists t0 : nat,
      forall t R : nat,
        t0 <= t ->
        X117HedgehogLegacy.x117_ramsey_number t R ->
        t ^ (2 * e2 - e1) <= R ^ e2 /\ R ^ e2 <= t ^ (2 * e2 + e1).

End X117HedgehogLegacy.

Module X117HedgehogOriginal.

Definition x117_ramsey_number (t R : nat) : Prop :=
  IM.X117ImageLegacy.x117_forces_mono (HedgehogLegacy.x117_edges t) R /\
  forall N : nat, IM.X117ImageLegacy.x117_forces_mono (HedgehogLegacy.x117_edges t) N -> R <= N.

Definition conlon_fox_rodl_hedgehog_ramsey_statement : Prop :=
  forall e1 e2 : nat,
    0 < e1 -> 0 < e2 ->
    exists t0 : nat,
      forall t R : nat,
        t0 <= t ->
        X117HedgehogOriginal.x117_ramsey_number t R ->
        t ^ (2 * e2 - e1) <= R ^ e2 /\ R ^ e2 <= t ^ (2 * e2 + e1).

End X117HedgehogOriginal.

(** The four constructors and the current chain and row are conversions; the two complete Originals
    transport through D3's actual forcing bridge [IM.x117_forces_mono_compat], as D3's own X117 proofs do. *)

Lemma x117_spike_compat (t : nat) :
  @HedgehogLegacy.x117_spike t =
  @Hypergraph.conjectures.X117.x117_spike t.
Proof. by []. Qed.

Lemma x117_vertex_compat (t : nat) :
  @HedgehogLegacy.x117_vertex t =
  @Hypergraph.conjectures.X117.x117_vertex t.
Proof. by []. Qed.

Lemma x117_edge_compat (t : nat) (s : HedgehogLegacy.x117_spike t) :
  @HedgehogLegacy.x117_edge t s =
  @Hypergraph.conjectures.X117.x117_edge t s.
Proof. by []. Qed.

Lemma x117_edges_compat (t : nat) :
  @HedgehogLegacy.x117_edges t =
  @Hypergraph.conjectures.X117.x117_edges t.
Proof. by []. Qed.

Lemma x117_ramsey_number_compat (t R : nat) :
  X117HedgehogLegacy.x117_ramsey_number t R <->
  Hypergraph.conjectures.X117.x117_ramsey_number t R.
Proof. exact: iff_refl. Qed.

Lemma conlon_fox_rodl_hedgehog_ramsey_statement_compat :
  X117HedgehogLegacy.conlon_fox_rodl_hedgehog_ramsey_statement <->
  Hypergraph.conjectures.X117.conlon_fox_rodl_hedgehog_ramsey_statement.
Proof. exact: iff_refl. Qed.

Lemma x117_ramsey_number_original_compat (t R : nat) :
  X117HedgehogOriginal.x117_ramsey_number t R <->
  Hypergraph.conjectures.X117.x117_ramsey_number t R.
Proof.
split=> -[F M]; split=> [|N FN].
- by apply/IM.x117_forces_mono_compat.
- by apply: M; apply/IM.x117_forces_mono_compat.
- by apply/IM.x117_forces_mono_compat.
- by apply: M; apply/IM.x117_forces_mono_compat.
Qed.

Lemma conlon_fox_rodl_hedgehog_ramsey_statement_original_compat :
  X117HedgehogOriginal.conlon_fox_rodl_hedgehog_ramsey_statement <->
  Hypergraph.conjectures.X117.conlon_fox_rodl_hedgehog_ramsey_statement.
Proof.
split=> h e1 e2 p1 p2; have [t0 ht0] := h e1 e2 p1 p2; exists t0 => t R tt rn.
  by apply: ht0 => //; apply/x117_ramsey_number_original_compat.
by apply: ht0 => //; apply/x117_ramsey_number_original_compat.
Qed.
