(** Public-only clients of strong induced-subdivision models.  They import only
    GTBase.  Covered: the empty pattern, a single pattern vertex, a graph's identity
    model, a nonempty pattern against the empty host, a host edge leaving the model
    support, and arbitrary sequences on non-edges. *)
From GTBase Require Import base model_support induced_subdivisions.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Example empty_pattern_in_any_host (G : sgraph) : induced_subdivision 'K_0 G.
Proof. exact: induced_subdivision_K0. Qed.

Example empty_pattern_in_empty_host : induced_subdivision 'K_0 'K_0.
Proof. exact: induced_subdivision_K0. Qed.

Example nonempty_pattern_not_in_empty_host : ~ induced_subdivision 'K_1 'K_0.
Proof. exact: (@not_induced_subdivision_empty_host 'K_1 ord0). Qed.

Example singleton_pattern_needs_a_host_vertex (G : sgraph) :
  induced_subdivision 'K_1 G <-> 0 < #|G|.
Proof. exact: induced_subdivision_K1. Qed.

(** The only host edge of ['K_2] leaves the single branch vertex for an unused
    vertex: global inducedness only constrains edges inside the model support. *)
Example host_edge_outside_support : induced_subdivision 'K_1 'K_2.
Proof. by apply/induced_subdivision_K1; rewrite card_ord. Qed.

Example identity_model (G : sgraph) : induced_subdivision G G.
Proof. exact: induced_subdivision_refl. Qed.

Example identity_model_edge_sequence (G : sgraph) (u v : G) :
  isd_edge_path (identity_induced_subdivision_model G) u v = [:: u; v].
Proof. by []. Qed.

Example pattern_no_larger_than_host (H G : sgraph) :
  induced_subdivision H G -> #|H| <= #|G|.
Proof. exact: induced_subdivision_card. Qed.

Example pattern_edges_have_nonempty_sequences (H G : sgraph)
    (m : induced_subdivision_model H G) (u v : H) :
  u -- v -> isd_edge_path m u v != [::].
Proof. exact: isd_edge_path_nil. Qed.

(** Arbitrary sequences on non-edges: in the identity model of ['K_2] put a
    repeated, non-path sequence on every non-edge; the result is still a model. *)
Example offedge_garbage_allowed :
  exists m : induced_subdivision_model 'K_2 ('K_2),
    forall u v : ('K_2), ~~ (u -- v) -> isd_edge_path m u v = [:: u; u; u].
Proof.
have same : forall u v : ('K_2), u -- v ->
    (fun u v : 'K_2 => if u -- v then [:: u; v] else [:: u; u; u]) u v =
    isd_edge_path (identity_induced_subdivision_model 'K_2) u v.
  by move=> u v uv; rewrite /= uv.
have [m [_ ep]] := isd_off_edge_free same.
by exists m => u v nuv; rewrite ep (negbTE nuv).
Qed.
