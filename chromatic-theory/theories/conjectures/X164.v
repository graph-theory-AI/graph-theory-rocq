(** * Chromatic.conjectures.X164 -- v2 fixed-surface 3-colouring output row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X164 vocabulary ***********************************************)

Definition x164_embedded_in_fixed_surface_with_boundary
    (surface boundary : nat) (G : sgraph) : Prop :=
  surface_embeddable surface G.

Definition x164_instance : Type :=
  {G : sgraph & {B : {set G} & G -> 'I_3}}.

Definition x164_graph (I : x164_instance) : sgraph := projT1 I.
Definition x164_boundary (I : x164_instance) : {set x164_graph I} :=
  projT1 (projT2 I).
Definition x164_precolour (I : x164_instance) : x164_graph I -> 'I_3 :=
  projT2 (projT2 I).

Definition x164_enc_instance (I : x164_instance) : data :=
  Dpair (enc_graph (x164_graph I))
    (Dpair
      (enc_list [seq enc_bool (v \in x164_boundary I) | v <- enum (x164_graph I)])
      (enc_list [seq enc_nat (val (@x164_precolour I v)) | v <- enum (x164_graph I)])).

Fixpoint x164_data_nth_nat (d : data) (i : nat) : nat :=
  match d, i with
  | Dcons (Dnat n) _, 0 => n
  | Dcons _ rest, j.+1 => x164_data_nth_nat rest j
  | Dnat n, 0 => n
  | _, _ => 0
  end.

Definition x164_output_colour (I : x164_instance) (out : data)
    (v : x164_graph I) : nat :=
  x164_data_nth_nat out (enum_rank v) %% 3.

Definition x164_valid_output (I : x164_instance) (out : data) : Prop :=
  (forall x y : x164_graph I, x -- y ->
      @x164_output_colour I out x != @x164_output_colour I out y) /\
  (forall v : x164_graph I,
      v \in x164_boundary I ->
      @x164_output_colour I out v = val (@x164_precolour I v)).

Definition x164_instance_class (surface boundary : nat) (I : x164_instance) : Prop :=
  triangle_free (x164_graph I) /\
  x164_embedded_in_fixed_surface_with_boundary surface boundary (x164_graph I) /\
  #|x164_boundary I| <= boundary.

Definition x164_linear_time_outputs_three_colouring (surface boundary : nat) : Prop :=
  linear_time_outputs_on_class
    x164_enc_instance (x164_instance_class surface boundary) x164_valid_output.

(** ** X164 statements *****************************************************)

(** Corpus row: arxiv:1601.01197#00
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/1601.01197__00/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/1601.01197__00.json
    English statement: (Dvorak, Kral and Thomas 2020, open problem on linear-time 3-colouring output, arXiv:1601.01197)
      For every fixed surface and every bound on the number of precoloured boundary vertices there
      is a linear-time algorithm that, given a triangle-free graph embeddable in that surface
      together with a set of at most that many boundary vertices and a precolouring of them by three
      colours, outputs a proper 3-colouring of the graph extending the precolouring on the boundary.
    Definitions: [x164_instance] - a graph together with a boundary vertex set and a 3-colouring
      used as the precolouring (this file); [x164_enc_instance] - its encoding as complexity-model
      data (this file); [x164_valid_output I out] - the decoded output is a proper colouring
      agreeing with the precolouring on the boundary (this file); [x164_instance_class surface
      boundary] - triangle-free, embeddable in the surface, boundary of size at most the bound (this
      file); [linear_time_outputs_on_class] (GTBase base/theories/complexity.v);
      [surface_embeddable] (GTBase base/theories/surface.v).
    Notes: KNOWN UNFAITHFUL ENCODING, corpus leg blocked. The faithfulness audit of 2026-07-17,
      meta/BLOCKED_RETARGETING_AUDIT.md and the row's verification_note, found a missing
      precondition that over-strengthens the row into a provably FALSE claim: the source asks for a
      linear-time OUTPUT algorithm in the affirmative case, i.e. when the precolouring does extend,
      while [x164_instance_class] drops that precondition and therefore demands a valid output even
      for instances where no extension exists. The surface primitive is moreover orientable-genus
      only, and the boundary parameter does not constrain the embedding. The body is left untouched
      here, WP4 changes comments only.
      V counts every vertex including isolated ones (base fix 2026-09-23): the old count saw
      only the vertices carrying a dart, so the Euler count overstated the genus of every
      graph with an isolated vertex and this hypothesis admitted fewer graphs than intended. *)
Definition linear_time_surface_triangle_free_three_colouring_output_statement : Prop :=
  forall surface boundary : nat,
    x164_linear_time_outputs_three_colouring surface boundary.
