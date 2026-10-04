(** * GTBase.migration.induced_paths — B22 certificates for the public strong induced-subdivision model

    Frozen verbatim at the fixed C20 pin 97605ddae838bc6e84b0602240148246e9d065f2
    (base/theories/induced_subdivisions.v, blob 68bc34c8a7b08ee3fcad16e1ed4ab3fdbdcbaf0d, declaration hash
    d7585c474c7fcd5b3aa3cb3e1c8fd9929d939c030a60b02328ab0619c2bff8a5 for the wrapper): the complete
    seven-field Record [induced_subdivision_model] with its inline pattern-edge path formula, and the
    inhabited wrapper [induced_subdivision] over that frozen Record.  Since B22 the live Record's field
    [isd_edge_path_valid] states the same formula through the canonical
    [GTBase.induced_paths.induced_path_between], which unfolds to exactly that match/conjunction
    (definitional equality, no merely equivalent Prop and no proof irrelevance); the live wrapper body
    [inhabited (induced_subdivision_model H G)] is unchanged, as are the public constructor and the
    seven projections with their types and implicit arguments.

    Certificates.  [model_of_legacy] / [model_to_legacy] repackage a model field by field in both
    directions (every field is passed through; the path field is accepted by conversion), and
    [induced_subdivision_model_compat] states that they cancel in both directions; the frozen and live
    Record types are different types and are not identified.  [induced_subdivision_compat] is the
    wrapper iff.  Not re-exported; imported by the area certificates of the family. *)

From mathcomp Require Import all_boot.
From GraphTheory Require Import preliminaries digraph sgraph.
From GTBase Require Import base model_support induced_paths induced_subdivisions.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Legacy.

Record induced_subdivision_model (H G : sgraph) := InducedSubdivisionModel {
  isd_branch : H -> G;
  isd_branch_injective : injective isd_branch;
  isd_edge_path : H -> H -> seq G;
  isd_edge_path_valid :
    forall u v : H,
      u -- v ->
      match isd_edge_path u v with
      | [::] => False
      | x :: q =>
          x = isd_branch u /\
          last x q = isd_branch v /\
          uniq (isd_edge_path u v) /\
          path (--) x q /\
          forall a b : G,
            a \in isd_edge_path u v -> b \in isd_edge_path u v -> a -- b -> a != b ->
            seq_consecutive (isd_edge_path u v) a b
      end;
  isd_internal_avoids_branch :
    forall (u v w : H) (x : G),
      u -- v ->
      x \in isd_edge_path u v /\ x != isd_branch u /\ x != isd_branch v ->
      x != isd_branch w;
  isd_paths_internally_disjoint :
    forall (u v u' v' : H) (x : G),
      u -- v -> u' -- v' ->
      x \in isd_edge_path u v /\ x != isd_branch u /\ x != isd_branch v ->
      x \in isd_edge_path u' v' /\ x != isd_branch u' /\ x != isd_branch v' ->
      (u = u' /\ v = v') \/ (u = v' /\ v = u');
  isd_global_induced :
    forall x y : G,
      model_support isd_branch isd_edge_path x ->
      model_support isd_branch isd_edge_path y ->
      x -- y ->
      exists u v : H, u -- v /\ seq_consecutive (isd_edge_path u v) x y
}.

Definition induced_subdivision (H G : sgraph) : Prop :=
  inhabited (Legacy.induced_subdivision_model H G).

End Legacy.

(** ** Field-by-field transports *)

Definition model_of_legacy (H G : sgraph) (m : Legacy.induced_subdivision_model H G) :
    induced_subdivision_model H G :=
  @InducedSubdivisionModel H G (@Legacy.isd_branch H G m) (@Legacy.isd_branch_injective H G m)
    (@Legacy.isd_edge_path H G m) (@Legacy.isd_edge_path_valid H G m)
    (@Legacy.isd_internal_avoids_branch H G m) (@Legacy.isd_paths_internally_disjoint H G m)
    (@Legacy.isd_global_induced H G m).

Definition model_to_legacy (H G : sgraph) (m : induced_subdivision_model H G) :
    Legacy.induced_subdivision_model H G :=
  @Legacy.InducedSubdivisionModel H G (@isd_branch H G m) (@isd_branch_injective H G m)
    (@isd_edge_path H G m) (@isd_edge_path_valid H G m) (@isd_internal_avoids_branch H G m)
    (@isd_paths_internally_disjoint H G m) (@isd_global_induced H G m).

(** The transports cancel in both directions. *)
Lemma induced_subdivision_model_compat (H G : sgraph) :
  (forall m : Legacy.induced_subdivision_model H G, model_to_legacy (model_of_legacy m) = m) /\
  (forall m : induced_subdivision_model H G, model_of_legacy (model_to_legacy m) = m).
Proof. by split; case. Qed.

(** The wrapper iff. *)
Lemma induced_subdivision_compat (H G : sgraph) :
  Legacy.induced_subdivision H G <-> induced_subdivision H G.
Proof.
split=> -[m]; constructor; first exact: model_of_legacy m.
exact: model_to_legacy m.
Qed.

Print Assumptions induced_subdivision_model_compat.
Print Assumptions induced_subdivision_compat.
