(** * D3: images of supplied hyperedges, Hypergraph certificate

    Frozen at the D2 pin aa1f6f38d309d50725f98b5e1b42dff6414af30b; bindings in
    meta/migration_reports/image_edge.spec.json.
    - [ImageLegacy]: the raw bounded-existential images of X108, X117 and X119, verbatim.  The
      live sources are now MathComp's [f @: e] ([imset], HB-locked), so each bridge is a proved
      set equality ([GTBase.set_images.imset_existsE]), not a conversion.
    - [<Phase>ImageLegacy]: the eight reached chains (copy with the same colour and injective map,
      two-colour/[q]-colour forcing, both Ramsey-number predicates with forcing and minimality)
      and the three complete current rows, each importing only its own conjecture file.  These
      current copies keep the live D1 uniformity, the A10 d-degeneracy and X119's ceiling square
      root with its opaque witness.
    - [X108ImageOriginal], [X119ImageOriginal]: the two complete A10+D1+D3 Originals, bound to the
      complete-history source 9e03072: D1's actual [UH.UniformLegacy] uniformity, A10's actual
      [ID.X108Legacy.d_degenerate] (X108), and the frozen image chain; no-isolated and the square
      root stay as they are.
    The four older snapshots (A10 X108Legacy, D1 X108UniformLegacy/X119UniformLegacy/
    X108UniformOriginal) stay as they are; the spec records them and points to these Originals. *)
From GTBase Require Import base set_images.
Require Hypergraph.conjectures.X108 Hypergraph.conjectures.X117 Hypergraph.conjectures.X119.
Require Hypergraph.migration.incidence_degree Hypergraph.migration.uniform_hypergraph.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module ID := Hypergraph.migration.incidence_degree.
Module UH := Hypergraph.migration.uniform_hypergraph.

Module ImageLegacy.

Definition x108_image_edge
    (T U : finType) (f : T -> U) (e : {set T}) : {set U} :=
  [set y : U | [exists x : T, (x \in e) && (y == f x)]].

Definition x117_image_edge
    (T : finType) (N : nat) (f : T -> 'I_N) (e : {set T}) : {set 'I_N} :=
  [set y : 'I_N | [exists x : T, (x \in e) && (y == f x)]].

Definition x119_image_edge
    (T : finType) (N : nat) (f : T -> 'I_N) (e : {set T}) : {set 'I_N} :=
  [set y : 'I_N | [exists x : T, (x \in e) && (y == f x)]].

End ImageLegacy.

Module X108ImageLegacy.
Import Hypergraph.conjectures.X108.

Definition x108_monochromatic_copy
    (T : finType) (E : {set {set T}}) (N : nat)
    (col : {set 'I_N} -> bool) : Prop :=
  exists (colour : bool) (f : T -> 'I_N),
    injective f /\
    forall e : {set T},
      e \in E -> col (ImageLegacy.x108_image_edge f e) = colour.

Definition x108_two_colour_ramsey_at_most
    (T : finType) (E : {set {set T}}) (N : nat) : Prop :=
  forall col : {set 'I_N} -> bool, X108ImageLegacy.x108_monochromatic_copy E col.

Definition three_uniform_degenerate_hypergraph_ramsey_linear_statement : Prop :=
  forall d : nat,
    exists c : nat,
      forall (T : finType) (E : {set {set T}}),
        x108_uniform E 3 ->
        x108_d_degenerate E d ->
        X108ImageLegacy.x108_two_colour_ramsey_at_most E (c * #|T|).

End X108ImageLegacy.

Module X117ImageLegacy.
Import Hypergraph.conjectures.X117.

Definition x117_monochromatic_copy
    (T : finType) (E : {set {set T}}) (N : nat)
    (col : {set 'I_N} -> bool) : Prop :=
  exists (colour : bool) (f : T -> 'I_N),
    injective f /\
    forall e : {set T},
      e \in E -> col (ImageLegacy.x117_image_edge f e) = colour.

Definition x117_forces_mono
    (T : finType) (E : {set {set T}}) (N : nat) : Prop :=
  forall col : {set 'I_N} -> bool, X117ImageLegacy.x117_monochromatic_copy E col.

Definition x117_ramsey_number (t R : nat) : Prop :=
  X117ImageLegacy.x117_forces_mono (x117_edges t) R /\
  forall N : nat, X117ImageLegacy.x117_forces_mono (x117_edges t) N -> R <= N.

Definition conlon_fox_rodl_hedgehog_ramsey_statement : Prop :=
  forall e1 e2 : nat,
    0 < e1 -> 0 < e2 ->
    exists t0 : nat,
      forall t R : nat,
        t0 <= t ->
        X117ImageLegacy.x117_ramsey_number t R ->
        t ^ (2 * e2 - e1) <= R ^ e2 /\ R ^ e2 <= t ^ (2 * e2 + e1).

End X117ImageLegacy.

Module X119ImageLegacy.
Import Hypergraph.conjectures.X119.

Definition x119_monochromatic_copy
    (T : finType) (E : {set {set T}}) (N q : nat)
    (col : {set 'I_N} -> 'I_q) : Prop :=
  exists (colour : 'I_q) (f : T -> 'I_N),
    injective f /\
    forall e : {set T},
      e \in E -> col (ImageLegacy.x119_image_edge f e) = colour.

Definition x119_forces_mono
    (T : finType) (E : {set {set T}}) (q N : nat) : Prop :=
  forall col : {set 'I_N} -> 'I_q, X119ImageLegacy.x119_monochromatic_copy E col.

Definition x119_ramsey_number
    (T : finType) (E : {set {set T}}) (q R : nat) : Prop :=
  X119ImageLegacy.x119_forces_mono E q R /\
  forall N : nat, X119ImageLegacy.x119_forces_mono E q N -> R <= N.

Definition conlon_fox_sudakov_three_uniform_ramsey_tower_statement : Prop :=
  forall q : nat,
    2 <= q ->
    exists cq : nat,
      forall (T : finType) (E : {set {set T}}),
        x119_uniform E 3 ->
        x119_no_isolated E ->
        forall R : nat,
          X119ImageLegacy.x119_ramsey_number E q R ->
          R <= 2 ^ (2 ^ (cq * x119_sqrt #|E|)).

End X119ImageLegacy.

Module X108ImageOriginal.
Import Hypergraph.conjectures.X108.

Definition three_uniform_degenerate_hypergraph_ramsey_linear_statement : Prop :=
  forall d : nat,
    exists c : nat,
      forall (T : finType) (E : {set {set T}}),
        UH.UniformLegacy.x108_uniform E 3 ->
        ID.X108Legacy.d_degenerate E d ->
        X108ImageLegacy.x108_two_colour_ramsey_at_most E (c * #|T|).

End X108ImageOriginal.

Module X119ImageOriginal.
Import Hypergraph.conjectures.X119.

Definition conlon_fox_sudakov_three_uniform_ramsey_tower_statement : Prop :=
  forall q : nat,
    2 <= q ->
    exists cq : nat,
      forall (T : finType) (E : {set {set T}}),
        UH.UniformLegacy.x119_uniform E 3 ->
        x119_no_isolated E ->
        forall R : nat,
          X119ImageLegacy.x119_ramsey_number E q R ->
          R <= 2 ^ (2 ^ (cq * x119_sqrt #|E|)).

End X119ImageOriginal.

(** ** Sources: the raw bounded-existential image equals the live [f @: e] (a proved set equality,
    since [imset] is locked) *)

Lemma x108_image_edge_compat (T U : finType) (f : T -> U) (e : {set T}) :
  @ImageLegacy.x108_image_edge T U f e =
  @Hypergraph.conjectures.X108.x108_image_edge T U f e.
Proof. exact: imset_existsE. Qed.

Lemma x117_image_edge_compat (T : finType) (N : nat) (f : T -> 'I_N) (e : {set T}) :
  @ImageLegacy.x117_image_edge T N f e =
  @Hypergraph.conjectures.X117.x117_image_edge T N f e.
Proof. exact: imset_existsE. Qed.

Lemma x119_image_edge_compat (T : finType) (N : nat) (f : T -> 'I_N) (e : {set T}) :
  @ImageLegacy.x119_image_edge T N f e =
  @Hypergraph.conjectures.X119.x119_image_edge T N f e.
Proof. exact: imset_existsE. Qed.

(** ** Chains: the same colour and injective copy, transported along the image equality *)

Lemma x108_monochromatic_copy_compat (T : finType) (E : {set {set T}}) (N : nat)
    (col : {set 'I_N} -> bool) :
  @X108ImageLegacy.x108_monochromatic_copy T E N col <->
  @Hypergraph.conjectures.X108.x108_monochromatic_copy T E N col.
Proof.
split=> -[c [f [fi H]]]; exists c, f; split=> // e eE.
  by move: (H e eE); rewrite x108_image_edge_compat.
by rewrite x108_image_edge_compat; exact: H.
Qed.

Lemma x117_monochromatic_copy_compat (T : finType) (E : {set {set T}}) (N : nat)
    (col : {set 'I_N} -> bool) :
  @X117ImageLegacy.x117_monochromatic_copy T E N col <->
  @Hypergraph.conjectures.X117.x117_monochromatic_copy T E N col.
Proof.
split=> -[c [f [fi H]]]; exists c, f; split=> // e eE.
  by move: (H e eE); rewrite x117_image_edge_compat.
by rewrite x117_image_edge_compat; exact: H.
Qed.

Lemma x119_monochromatic_copy_compat (T : finType) (E : {set {set T}}) (N q : nat)
    (col : {set 'I_N} -> 'I_q) :
  @X119ImageLegacy.x119_monochromatic_copy T E N q col <->
  @Hypergraph.conjectures.X119.x119_monochromatic_copy T E N q col.
Proof.
split=> -[c [f [fi H]]]; exists c, f; split=> // e eE.
  by move: (H e eE); rewrite x119_image_edge_compat.
by rewrite x119_image_edge_compat; exact: H.
Qed.

Lemma x108_two_colour_ramsey_at_most_compat (T : finType) (E : {set {set T}}) (N : nat) :
  @X108ImageLegacy.x108_two_colour_ramsey_at_most T E N <->
  @Hypergraph.conjectures.X108.x108_two_colour_ramsey_at_most T E N.
Proof.
split=> H col.
  by apply/x108_monochromatic_copy_compat; exact: H.
by apply/x108_monochromatic_copy_compat; exact: H.
Qed.

Lemma x117_forces_mono_compat (T : finType) (E : {set {set T}}) (N : nat) :
  @X117ImageLegacy.x117_forces_mono T E N <-> @Hypergraph.conjectures.X117.x117_forces_mono T E N.
Proof.
split=> H col.
  by apply/x117_monochromatic_copy_compat; exact: H.
by apply/x117_monochromatic_copy_compat; exact: H.
Qed.

Lemma x119_forces_mono_compat (T : finType) (E : {set {set T}}) (q N : nat) :
  @X119ImageLegacy.x119_forces_mono T E q N <->
  @Hypergraph.conjectures.X119.x119_forces_mono T E q N.
Proof.
split=> H col.
  by apply/x119_monochromatic_copy_compat; exact: H.
by apply/x119_monochromatic_copy_compat; exact: H.
Qed.

(** Both Ramsey-number predicates keep forcing at [R] and minimality against every forcing [N]. *)
Lemma x117_ramsey_number_compat (t R : nat) :
  X117ImageLegacy.x117_ramsey_number t R <-> Hypergraph.conjectures.X117.x117_ramsey_number t R.
Proof.
split=> -[F M]; split=> [|N FN].
- by apply/x117_forces_mono_compat.
- by apply: M; apply/x117_forces_mono_compat.
- by apply/x117_forces_mono_compat.
- by apply: M; apply/x117_forces_mono_compat.
Qed.

Lemma x119_ramsey_number_compat (T : finType) (E : {set {set T}}) (q R : nat) :
  @X119ImageLegacy.x119_ramsey_number T E q R <->
  @Hypergraph.conjectures.X119.x119_ramsey_number T E q R.
Proof.
split=> -[F M]; split=> [|N FN].
- by apply/x119_forces_mono_compat.
- by apply: M; apply/x119_forces_mono_compat.
- by apply/x119_forces_mono_compat.
- by apply: M; apply/x119_forces_mono_compat.
Qed.

(** ** The three complete current rows (live uniformity, degeneracy and sqrt kept) *)

Lemma three_uniform_degenerate_hypergraph_ramsey_linear_statement_compat :
  X108ImageLegacy.three_uniform_degenerate_hypergraph_ramsey_linear_statement <->
  Hypergraph.conjectures.X108.three_uniform_degenerate_hypergraph_ramsey_linear_statement.
Proof.
split=> h d; have [c hc] := h d; exists c => T E u dd.
  by apply/x108_two_colour_ramsey_at_most_compat; apply: hc.
by apply/x108_two_colour_ramsey_at_most_compat; apply: hc.
Qed.

Lemma conlon_fox_rodl_hedgehog_ramsey_statement_compat :
  X117ImageLegacy.conlon_fox_rodl_hedgehog_ramsey_statement <->
  Hypergraph.conjectures.X117.conlon_fox_rodl_hedgehog_ramsey_statement.
Proof.
split=> h e1 e2 p1 p2; have [t0 ht0] := h e1 e2 p1 p2; exists t0 => t R tt rn.
  by apply: ht0 => //; apply/x117_ramsey_number_compat.
by apply: ht0 => //; apply/x117_ramsey_number_compat.
Qed.

Lemma conlon_fox_sudakov_three_uniform_ramsey_tower_statement_compat :
  X119ImageLegacy.conlon_fox_sudakov_three_uniform_ramsey_tower_statement <->
  Hypergraph.conjectures.X119.conlon_fox_sudakov_three_uniform_ramsey_tower_statement.
Proof.
split=> h q q2; have [cq hq] := h q q2; exists cq => T E u ni R rn.
  by apply: hq => //; apply/x119_ramsey_number_compat.
by apply: hq => //; apply/x119_ramsey_number_compat.
Qed.

(** ** The two complete Originals.  Each is the corresponding earlier whole row with the image
    chain also frozen: X108 over D1's X108UniformOriginal (raw uniformity, A10's actual
    X108Legacy.d_degenerate), X119 over D1's X119UniformLegacy (raw uniformity); the earlier
    whole iff is reused unchanged and only the Ramsey predicate is transported. *)

Lemma three_uniform_degenerate_hypergraph_ramsey_linear_statement_original_compat :
  X108ImageOriginal.three_uniform_degenerate_hypergraph_ramsey_linear_statement <->
  Hypergraph.conjectures.X108.three_uniform_degenerate_hypergraph_ramsey_linear_statement.
Proof.
apply: (iff_trans _ UH.three_uniform_degenerate_hypergraph_ramsey_linear_statement_original_compat).
split=> h d; have [c hc] := h d; exists c => T E u dd.
  by apply/x108_two_colour_ramsey_at_most_compat; apply: hc.
by apply/x108_two_colour_ramsey_at_most_compat; apply: hc.
Qed.

Lemma conlon_fox_sudakov_three_uniform_ramsey_tower_statement_original_compat :
  X119ImageOriginal.conlon_fox_sudakov_three_uniform_ramsey_tower_statement <->
  Hypergraph.conjectures.X119.conlon_fox_sudakov_three_uniform_ramsey_tower_statement.
Proof.
apply: (iff_trans _ UH.conlon_fox_sudakov_three_uniform_ramsey_tower_statement_compat).
split=> h q q2; have [cq hq] := h q q2; exists cq => T E u ni R rn.
  by apply: hq => //; apply/x119_ramsey_number_compat.
by apply: hq => //; apply/x119_ramsey_number_compat.
Qed.
