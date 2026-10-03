(** C20 (GTMisc): the strong X114 induced-subdivision model, frozen at the fixed C19 pin
    952a89bdecf65bed9be3a1393eabc91ca091d26c.
    - [Legacy]: the whole seven-field Record [x114_induced_subdivision_model] (type,
      constructor [X114Model], fields), its [inhabited] wrapper and the decision problem
      built on it, verbatim.  The live Record is now an alias of
      [GTBase.induced_subdivisions.induced_subdivision_model], with constructor and
      projection wrappers of the same types and implicit arguments; its helpers stay live
      here (B3's path helpers, C19's raw support).
    - [X114Legacy]: the current row over the frozen problem; A14's [x114_subcubic] and
      the D7 [x114_np_complete] proxy stay live here.
    The complete row is C19's [GTMisc.migration.model_support.X114Original] (B3 path
    helpers, A14 maximum-degree bound and C19 raw support over a fully frozen Record and
    problem); its certificates stay valid through the wrappers and are reused.  The frozen
    and live problems have the same instances and sizes and equivalent memberships; the
    full in-NP verifier/cost witnesses and NP-hardness reductions transfer. *)
From GTBase Require Import base model_support induced_subdivisions.
From GTMisc.conjectures Require Import D7 X114.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Legacy.

Record x114_induced_subdivision_model (H G : sgraph) := X114Model {
  x114_branch : H -> G;
  x114_branch_injective : injective x114_branch;
  x114_edge_path : H -> H -> seq G;
  x114_edge_path_valid :
    forall u v : H,
      u -- v ->
      x114_induced_path_between
        (x114_branch u) (x114_branch v) (x114_edge_path u v);
  x114_internal_avoids_branch :
    forall (u v w : H) (x : G),
      u -- v ->
      x114_internal (x114_edge_path u v) (x114_branch u) (x114_branch v) x ->
      x != x114_branch w;
  x114_paths_internally_disjoint :
    forall (u v u' v' : H) (x : G),
      u -- v -> u' -- v' ->
      x114_internal (x114_edge_path u v) (x114_branch u) (x114_branch v) x ->
      x114_internal (x114_edge_path u' v') (x114_branch u') (x114_branch v') x ->
      (u = u' /\ v = v') \/ (u = v' /\ v = u');
  x114_global_induced :
    forall x y : G,
      x114_model_vertex x114_branch x114_edge_path x ->
      x114_model_vertex x114_branch x114_edge_path y ->
      x -- y ->
      exists u v : H, u -- v /\ x114_consecutive_in_path (x114_edge_path u v) x y
}.

Definition x114_induced_subdivision (H G : sgraph) : Prop :=
  inhabited (Legacy.x114_induced_subdivision_model H G).

(** The H-INDUCED-SUBDIVISION-CONTAINMENT decision problem ([H]-ISC), packaged
    as a [D7.problem]: input a graph G (size = #|G|), YES iff G contains an
    induced subdivision of H. *)
Definition x114_hisc_problem (H : sgraph) : problem :=
  {| pinput := sgraph;
     psize  := fun G : sgraph => #|G|;
     pmem   := fun G : sgraph => Legacy.x114_induced_subdivision H G |}.

End Legacy.

Module X114Legacy.

Definition subcubic_induced_subdivision_np_complete_statement : Prop :=
  exists H : sgraph,
    x114_subcubic H /\ x114_np_complete (Legacy.x114_hisc_problem H).

End X114Legacy.

(** ** Certificates *)

Definition x114_model_of_legacy (H G : sgraph)
    (m : Legacy.x114_induced_subdivision_model H G) : x114_induced_subdivision_model H G :=
  @X114Model H G (@Legacy.x114_branch H G m) (@Legacy.x114_branch_injective H G m)
    (@Legacy.x114_edge_path H G m) (@Legacy.x114_edge_path_valid H G m)
    (@Legacy.x114_internal_avoids_branch H G m)
    (@Legacy.x114_paths_internally_disjoint H G m)
    (@Legacy.x114_global_induced H G m).

Definition x114_model_to_legacy (H G : sgraph)
    (m : x114_induced_subdivision_model H G) : Legacy.x114_induced_subdivision_model H G :=
  @Legacy.X114Model H G (@x114_branch H G m) (@x114_branch_injective H G m)
    (@x114_edge_path H G m) (@x114_edge_path_valid H G m)
    (@x114_internal_avoids_branch H G m) (@x114_paths_internally_disjoint H G m)
    (@x114_global_induced H G m).

Lemma x114_induced_subdivision_model_compat (H G : sgraph) :
  {f : Legacy.x114_induced_subdivision_model H G -> x114_induced_subdivision_model H G &
   {g : x114_induced_subdivision_model H G -> Legacy.x114_induced_subdivision_model H G |
    cancel f g /\ cancel g f}}.
Proof. by exists (@x114_model_of_legacy H G), (@x114_model_to_legacy H G); split; case. Qed.

Lemma x114_induced_subdivision_compat (H G : sgraph) :
  Legacy.x114_induced_subdivision H G <-> x114_induced_subdivision H G.
Proof.
split=> -[m]; constructor; first exact: x114_model_of_legacy m.
exact: x114_model_to_legacy m.
Qed.

Lemma x114_hisc_problem_compat (H : sgraph) :
  [/\ forall G : sgraph,
        @pmem (Legacy.x114_hisc_problem H) G <-> @pmem (x114_hisc_problem H) G,
      in_NP (Legacy.x114_hisc_problem H) <-> in_NP (x114_hisc_problem H) &
      NP_hard (Legacy.x114_hisc_problem H) <-> NP_hard (x114_hisc_problem H)].
Proof.
have mem G : @pmem (Legacy.x114_hisc_problem H) G <-> @pmem (x114_hisc_problem H) G.
  exact: x114_induced_subdivision_compat.
split=> //.
- split=> -[verify [vcost [a [d [b [vmem vbound]]]]]];
    exists verify, vcost, a, d, b; split=> // G.
  + exact: iff_trans (iff_sym (mem G)) (vmem G).
  + exact: iff_trans (mem G) (vmem G).
- split=> hard A /hard[f [cost [a [d [b [fmem fcost fsize]]]]]];
    exists f, cost, a, d, b; split=> // x.
  + exact: iff_trans (fmem x) (mem (f x)).
  + exact: iff_trans (fmem x) (iff_sym (mem (f x))).
Qed.

Lemma subcubic_induced_subdivision_np_complete_statement_compat :
  X114Legacy.subcubic_induced_subdivision_np_complete_statement <->
  subcubic_induced_subdivision_np_complete_statement.
Proof.
have np H : x114_np_complete (Legacy.x114_hisc_problem H) <->
            x114_np_complete (x114_hisc_problem H).
  have [_ inNP hard] := x114_hisc_problem_compat H.
  by split=> -[a b]; split; [exact/inNP | exact/hard | exact/inNP | exact/hard].
by split=> -[H [sub hnp]]; exists H; split=> //; apply/np.
Qed.
