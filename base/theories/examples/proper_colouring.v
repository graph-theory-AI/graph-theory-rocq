(** * Public colouring API client: no conjecture imports. *)
From GTBase Require Import base colourings.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Example palette_fibres_are_upstream_coloring
    (G : sgraph) (C : finType) (col : G -> C) :
  proper_colouring col -> coloring (preim_partition col [set: G]) [set: G].
Proof. by []. Qed.

Example edges_receive_different_labels (G : sgraph) (C : finType) (col : G -> C) :
  proper_colouring col -> forall x y : G, x -- y -> col x != col y.
Proof. exact/proper_colouringP. Qed.

Example finite_function_boolean_view (G : sgraph) q (col : {ffun G -> 'I_q}) :
  proper_colouring col = [forall x, [forall y, (x -- y) ==> (col x != col y)]].
Proof. exact: proper_colouringE. Qed.

Example empty_graph_accepts_empty_palette : proper_colouring (fun x : 'K_0 => x).
Proof. exact: proper_colouring_K0. Qed.

Example complete_two_identity : proper_colouring (fun x : 'K_2 => x).
Proof. by apply: proper_colouring_injective. Qed.

Example complete_two_constant_is_improper :
  ~~ proper_colouring (fun _ : 'K_2 => (ord0 : 'I_1)).
Proof.
apply: (@not_proper_colouring_constant 'K_2 _ ord0 ord0 ord_max).
by [].
Qed.

Example singleton_accepts_unused_labels :
  proper_colouring (fun _ : 'K_1 => (ord0 : 'I_3)).
Proof. exact: proper_colouring_K1. Qed.

Example injective_palette_changes_preserve_properness
    (G : sgraph) (C D : finType) (col : G -> C) (f : C -> D) :
  injective f -> proper_colouring (f \o col) = proper_colouring col.
Proof. exact: proper_colouring_relabel. Qed.

Example unused_labels_still_bound_chi (G : sgraph) (C : finType) (col : G -> C) :
  proper_colouring col -> χ([set: G]) <= #|C|.
Proof. exact: proper_colouring_chi. Qed.

Print Assumptions empty_graph_accepts_empty_palette.
Print Assumptions singleton_accepts_unused_labels.
Print Assumptions complete_two_constant_is_improper.
