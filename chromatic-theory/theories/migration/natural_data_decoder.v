(** * Chromatic.migration.natural_data_decoder — natural-data-decoder certificates: X157's and X164's output decoder

    Family [natural-data-decoder] (meta/library_primitives/natural-data-decoder.json).  [Legacy] freezes verbatim, at the
    baseline 3bdfdae (tree ade432af, the accepted D11 main's tree), the two conjecture-local decoders
    [x157_data_nth_nat] and [x164_data_nth_nat] (identical bodies, unchanged since their authoring 8800958) and every
    same-file declaration through which a row reaches them, references between frozen copies qualified [Legacy.]:
    X157's [x157_output_colour] (the entry at the vertex's enum rank, modulo [k]), [x157_output_k_colouring_or_none]
    (the [Dnat 0] answer with [~ chi <= k], or [0 < k] and a proper colouring) and [x157_polytime_colouring_or_none];
    X164's [x164_output_colour] (modulo 3), [x164_valid_output] (proper and agreeing with the precolouring on the
    boundary) and [x164_linear_time_outputs_three_colouring].  [X157Legacy] / [X164Legacy] freeze the two complete
    rows.  Declarations that do not reach the decoders (X157's local-connectivity chain, X164's instance, encoding and
    class) are the live, unchanged ones.

    [X157Original] composes the end-to-end pre-migration X157 row: the earlier family internal-vertices (B2, baseline
    9e03072) froze X157's internal-vertex chain and kept the output decoding live by design, and this family freezes
    the output decoding and keeps that chain live; over B2's frozen [internal_vertices.X157Legacy] chain and the frozen
    [Legacy] decoding here, [X157Original.statement] is the row with every migrated helper at its original body.
    X164 has no earlier snapshot, so [X164Legacy] is already its deepest original.

    Since this migration both decoders are aliases of GTBase.complexity's [data_nth_nat], whose body is the same
    fixpoint, so every certificate below is a kernel-checked conversion.  The X164 row stays exactly as it was,
    including its documented unfaithful encoding (no extension precondition; orientable surface only; the boundary
    parameter does not constrain the embedding); nothing here repairs or certifies that algorithmic claim. *)

From GTBase Require Import base.
From Chromatic.conjectures Require Import X157 X164.
Require Chromatic.migration.internal_vertices.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Legacy.

Fixpoint x157_data_nth_nat (d : data) (i : nat) : nat :=
  match d, i with
  | Dcons (Dnat n) _, 0 => n
  | Dcons _ rest, j.+1 => x157_data_nth_nat rest j
  | Dnat n, 0 => n
  | _, _ => 0
  end.

Definition x157_output_colour (G : sgraph) (k : nat) (out : data) (v : G) : nat :=
  Legacy.x157_data_nth_nat out (enum_rank v) %% k.

Definition x157_output_k_colouring_or_none
    (k : nat) (G : sgraph) (out : data) : Prop :=
  (out = Dnat 0 /\ ~ χ([set: G]) <= k) \/
  (0 < k /\ forall x y : G, x -- y ->
      Legacy.x157_output_colour k out x != Legacy.x157_output_colour k out y).

Definition x157_polytime_colouring_or_none (k : nat) : Prop :=
  polytime_outputs_graph_on
    (fun G : sgraph => k_connected G k /\ x157_max_local_connectivity_at_most G k)
    (Legacy.x157_output_k_colouring_or_none k).

Fixpoint x164_data_nth_nat (d : data) (i : nat) : nat :=
  match d, i with
  | Dcons (Dnat n) _, 0 => n
  | Dcons _ rest, j.+1 => x164_data_nth_nat rest j
  | Dnat n, 0 => n
  | _, _ => 0
  end.

Definition x164_output_colour (I : x164_instance) (out : data)
    (v : x164_graph I) : nat :=
  Legacy.x164_data_nth_nat out (enum_rank v) %% 3.

Definition x164_valid_output (I : x164_instance) (out : data) : Prop :=
  (forall x y : x164_graph I, x -- y ->
      @Legacy.x164_output_colour I out x != @Legacy.x164_output_colour I out y) /\
  (forall v : x164_graph I,
      v \in x164_boundary I ->
      @Legacy.x164_output_colour I out v = val (@x164_precolour I v)).

Definition x164_linear_time_outputs_three_colouring (surface boundary : nat) : Prop :=
  linear_time_outputs_on_class
    x164_enc_instance (x164_instance_class surface boundary) Legacy.x164_valid_output.

End Legacy.

Module X157Legacy.

Definition local_connectivity_k_colouring_polytime_statement : Prop :=
  forall k : nat, 4 <= k -> Legacy.x157_polytime_colouring_or_none k.

End X157Legacy.

Module X164Legacy.

Definition linear_time_surface_triangle_free_three_colouring_output_statement : Prop :=
  forall surface boundary : nat,
    Legacy.x164_linear_time_outputs_three_colouring surface boundary.

End X164Legacy.

Module X157Original.

Definition polytime_colouring_or_none (k : nat) : Prop :=
  polytime_outputs_graph_on
    (fun G : sgraph => k_connected G k /\ internal_vertices.X157Legacy.max_local_connectivity_at_most G k)
    (Legacy.x157_output_k_colouring_or_none k).

Definition statement : Prop :=
  forall k : nat, 4 <= k -> polytime_colouring_or_none k.

End X157Original.

(** ** Certificates *)

Lemma x157_data_nth_nat_compat (d : data) (i : nat) :
  Legacy.x157_data_nth_nat d i = x157_data_nth_nat d i.
Proof. by []. Qed.

Lemma x157_output_colour_compat (G : sgraph) (k : nat) (out : data) (v : G) :
  Legacy.x157_output_colour k out v = x157_output_colour k out v.
Proof. by []. Qed.

Lemma x157_output_k_colouring_or_none_compat (k : nat) (G : sgraph) (out : data) :
  Legacy.x157_output_k_colouring_or_none k G out <-> x157_output_k_colouring_or_none k G out.
Proof. exact: iff_refl. Qed.

Lemma x157_polytime_colouring_or_none_compat (k : nat) :
  Legacy.x157_polytime_colouring_or_none k <-> x157_polytime_colouring_or_none k.
Proof. exact: iff_refl. Qed.

Lemma local_connectivity_k_colouring_polytime_statement_compat :
  X157Legacy.local_connectivity_k_colouring_polytime_statement <->
  local_connectivity_k_colouring_polytime_statement.
Proof. exact: iff_refl. Qed.

Lemma x157_polytime_colouring_or_none_original_compat (k : nat) :
  X157Original.polytime_colouring_or_none k <-> x157_polytime_colouring_or_none k.
Proof. exact: iff_refl. Qed.

Lemma local_connectivity_k_colouring_polytime_statement_original_compat :
  X157Original.statement <-> local_connectivity_k_colouring_polytime_statement.
Proof. exact: iff_refl. Qed.

Lemma x164_data_nth_nat_compat (d : data) (i : nat) :
  Legacy.x164_data_nth_nat d i = x164_data_nth_nat d i.
Proof. by []. Qed.

Lemma x164_output_colour_compat (I : x164_instance) (out : data) (v : x164_graph I) :
  @Legacy.x164_output_colour I out v = @x164_output_colour I out v.
Proof. by []. Qed.

Lemma x164_valid_output_compat (I : x164_instance) (out : data) :
  Legacy.x164_valid_output I out <-> x164_valid_output I out.
Proof. exact: iff_refl. Qed.

Lemma x164_linear_time_outputs_three_colouring_compat (surface boundary : nat) :
  Legacy.x164_linear_time_outputs_three_colouring surface boundary <->
  x164_linear_time_outputs_three_colouring surface boundary.
Proof. exact: iff_refl. Qed.

Lemma linear_time_surface_triangle_free_three_colouring_output_statement_compat :
  X164Legacy.linear_time_surface_triangle_free_three_colouring_output_statement <->
  linear_time_surface_triangle_free_three_colouring_output_statement.
Proof. exact: iff_refl. Qed.

Print Assumptions x157_data_nth_nat_compat.
Print Assumptions x157_output_colour_compat.
Print Assumptions x157_output_k_colouring_or_none_compat.
Print Assumptions x157_polytime_colouring_or_none_compat.
Print Assumptions local_connectivity_k_colouring_polytime_statement_compat.
Print Assumptions x157_polytime_colouring_or_none_original_compat.
Print Assumptions local_connectivity_k_colouring_polytime_statement_original_compat.
Print Assumptions x164_data_nth_nat_compat.
Print Assumptions x164_output_colour_compat.
Print Assumptions x164_valid_output_compat.
Print Assumptions x164_linear_time_outputs_three_colouring_compat.
Print Assumptions linear_time_surface_triangle_free_three_colouring_output_statement_compat.
