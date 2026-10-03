(** C19 (GTMisc): X114 raw model support, frozen at the private union
    bb0bf3cd7c1d14e014704ebd5e24b03e4c475cb8 (exact C18 15a5a5c + reviewed A14
    f52251a).
    - [Legacy]: the raw support [x114_model_vertex] verbatim; the live helper now
      unfolds to [GTBase.model_support.model_support br ep x], the same disjunction.
    - [X114Legacy]: the current chain over the frozen support: the whole
      seven-field Record, its [inhabited] wrapper, the decision problem built on it
      and the row.  Every other helper stays live here (B3's path helpers, A14's
      [x114_subcubic], [x114_np_complete]).
    - [X114Original]: the complete row.  Its Record combines B3's frozen
      [induced_path_between] and consecutive-entry helper with this family's frozen
      support; its row uses A14's frozen [x114_subcubic] (the original
      [Delta H <= 3]).  The older B3 Record and the A14 rows remain unchanged as
      documented snapshots.
    Frozen and live Records are different inductive types; the transports below
    repackage a model field by field and are mutually inverse.  The frozen and
    live problems have the same instances and sizes and equivalent memberships, so
    [in_NP] and [NP_hard] transfer.  Earlier certificate modules are aliased, not
    imported. *)
From GTBase Require Import base model_support.
From GTMisc.conjectures Require Import D7 X114.
From GTMisc.migration Require consecutive_in_path subcubic.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module B3 := GTMisc.migration.consecutive_in_path.
Module A14 := GTMisc.migration.subcubic.

Module Legacy.

Definition x114_model_vertex (H G : sgraph)
    (br : H -> G) (ep : H -> H -> seq G) (x : G) : Prop :=
  (exists h : H, br h = x) \/ (exists u v : H, u -- v /\ x \in ep u v).

End Legacy.

Module X114Legacy.

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
      Legacy.x114_model_vertex x114_branch x114_edge_path x ->
      Legacy.x114_model_vertex x114_branch x114_edge_path y ->
      x -- y ->
      exists u v : H, u -- v /\ x114_consecutive_in_path (x114_edge_path u v) x y
}.

Definition x114_induced_subdivision (H G : sgraph) : Prop :=
  inhabited (X114Legacy.x114_induced_subdivision_model H G).

Definition x114_hisc_problem (H : sgraph) : problem :=
  {| pinput := sgraph;
     psize  := fun G : sgraph => #|G|;
     pmem   := fun G : sgraph => X114Legacy.x114_induced_subdivision H G |}.

Definition subcubic_induced_subdivision_np_complete_statement : Prop :=
  exists H : sgraph,
    x114_subcubic H /\ x114_np_complete (X114Legacy.x114_hisc_problem H).

End X114Legacy.

Module X114Original.

Record x114_induced_subdivision_model (H G : sgraph) := X114Model {
  x114_branch : H -> G;
  x114_branch_injective : injective x114_branch;
  x114_edge_path : H -> H -> seq G;
  x114_edge_path_valid :
    forall u v : H,
      u -- v ->
      B3.X114Legacy.induced_path_between
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
      Legacy.x114_model_vertex x114_branch x114_edge_path x ->
      Legacy.x114_model_vertex x114_branch x114_edge_path y ->
      x -- y ->
      exists u v : H, u -- v /\ B3.Legacy.x114_consecutive_in_path (x114_edge_path u v) x y
}.

Definition x114_induced_subdivision (H G : sgraph) : Prop :=
  inhabited (X114Original.x114_induced_subdivision_model H G).

Definition x114_hisc_problem (H : sgraph) : problem :=
  {| pinput := sgraph;
     psize  := fun G : sgraph => #|G|;
     pmem   := fun G : sgraph => X114Original.x114_induced_subdivision H G |}.

Definition subcubic_induced_subdivision_np_complete_statement : Prop :=
  exists H : sgraph,
    A14.Legacy.x114_subcubic H /\ x114_np_complete (X114Original.x114_hisc_problem H).

End X114Original.

(** ** Certificates *)

Lemma x114_model_vertex_compat (H G : sgraph) (br : H -> G) (ep : H -> H -> seq G) (x : G) :
  Legacy.x114_model_vertex br ep x <-> x114_model_vertex br ep x.
Proof. exact: iff_refl. Qed.

Definition x114_model_of_legacy (H G : sgraph)
    (m : X114Legacy.x114_induced_subdivision_model H G) : x114_induced_subdivision_model H G :=
  @X114Model H G (@X114Legacy.x114_branch H G m) (@X114Legacy.x114_branch_injective H G m)
    (@X114Legacy.x114_edge_path H G m) (@X114Legacy.x114_edge_path_valid H G m)
    (@X114Legacy.x114_internal_avoids_branch H G m)
    (@X114Legacy.x114_paths_internally_disjoint H G m)
    (@X114Legacy.x114_global_induced H G m).

Definition x114_model_to_legacy (H G : sgraph)
    (m : x114_induced_subdivision_model H G) : X114Legacy.x114_induced_subdivision_model H G :=
  @X114Legacy.X114Model H G (@x114_branch H G m) (@x114_branch_injective H G m)
    (@x114_edge_path H G m) (@x114_edge_path_valid H G m)
    (@x114_internal_avoids_branch H G m) (@x114_paths_internally_disjoint H G m)
    (@x114_global_induced H G m).

Lemma x114_induced_subdivision_model_compat (H G : sgraph) :
  {f : X114Legacy.x114_induced_subdivision_model H G -> x114_induced_subdivision_model H G &
   {g : x114_induced_subdivision_model H G -> X114Legacy.x114_induced_subdivision_model H G |
    cancel f g /\ cancel g f}}.
Proof. by exists (@x114_model_of_legacy H G), (@x114_model_to_legacy H G); split; case. Qed.

Lemma x114_induced_subdivision_compat (H G : sgraph) :
  X114Legacy.x114_induced_subdivision H G <-> x114_induced_subdivision H G.
Proof.
split=> -[m]; constructor; first exact: x114_model_of_legacy m.
exact: x114_model_to_legacy m.
Qed.


Lemma x114_hisc_problem_compat (H : sgraph) :
  [/\ forall G : sgraph,
        @pmem (X114Legacy.x114_hisc_problem H) G <-> @pmem (x114_hisc_problem H) G,
      in_NP (X114Legacy.x114_hisc_problem H) <-> in_NP (x114_hisc_problem H) &
      NP_hard (X114Legacy.x114_hisc_problem H) <-> NP_hard (x114_hisc_problem H)].
Proof.
have mem G : @pmem (X114Legacy.x114_hisc_problem H) G <-> @pmem (x114_hisc_problem H) G.
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
have np H : x114_np_complete (X114Legacy.x114_hisc_problem H) <->
            x114_np_complete (x114_hisc_problem H).
  have [_ inNP hard] := x114_hisc_problem_compat H.
  by split=> -[a b]; split; [exact/inNP | exact/hard | exact/inNP | exact/hard].
by split=> -[H [sub hnp]]; exists H; split=> //; apply/np.
Qed.

Definition x114_model_of_original (H G : sgraph)
    (m : X114Original.x114_induced_subdivision_model H G) : x114_induced_subdivision_model H G :=
  @X114Model H G (@X114Original.x114_branch H G m) (@X114Original.x114_branch_injective H G m)
    (@X114Original.x114_edge_path H G m) (@X114Original.x114_edge_path_valid H G m)
    (@X114Original.x114_internal_avoids_branch H G m)
    (@X114Original.x114_paths_internally_disjoint H G m)
    (@X114Original.x114_global_induced H G m).

Definition x114_model_to_original (H G : sgraph)
    (m : x114_induced_subdivision_model H G) : X114Original.x114_induced_subdivision_model H G :=
  @X114Original.X114Model H G (@x114_branch H G m) (@x114_branch_injective H G m)
    (@x114_edge_path H G m) (@x114_edge_path_valid H G m)
    (@x114_internal_avoids_branch H G m) (@x114_paths_internally_disjoint H G m)
    (@x114_global_induced H G m).

Lemma x114_induced_subdivision_model_original_compat (H G : sgraph) :
  {f : X114Original.x114_induced_subdivision_model H G -> x114_induced_subdivision_model H G &
   {g : x114_induced_subdivision_model H G -> X114Original.x114_induced_subdivision_model H G |
    cancel f g /\ cancel g f}}.
Proof. by exists (@x114_model_of_original H G), (@x114_model_to_original H G); split; case. Qed.

Lemma x114_induced_subdivision_original_compat (H G : sgraph) :
  X114Original.x114_induced_subdivision H G <-> x114_induced_subdivision H G.
Proof.
split=> -[m]; constructor; first exact: x114_model_of_original m.
exact: x114_model_to_original m.
Qed.

Lemma x114_hisc_problem_original_compat (H : sgraph) :
  [/\ forall G : sgraph,
        @pmem (X114Original.x114_hisc_problem H) G <-> @pmem (x114_hisc_problem H) G,
      in_NP (X114Original.x114_hisc_problem H) <-> in_NP (x114_hisc_problem H) &
      NP_hard (X114Original.x114_hisc_problem H) <-> NP_hard (x114_hisc_problem H)].
Proof.
have mem G : @pmem (X114Original.x114_hisc_problem H) G <-> @pmem (x114_hisc_problem H) G.
  exact: x114_induced_subdivision_original_compat.
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

Lemma subcubic_induced_subdivision_np_complete_statement_original_compat :
  X114Original.subcubic_induced_subdivision_np_complete_statement <->
  subcubic_induced_subdivision_np_complete_statement.
Proof.
have np H : x114_np_complete (X114Original.x114_hisc_problem H) <->
            x114_np_complete (x114_hisc_problem H).
  have [_ inNP hard] := x114_hisc_problem_original_compat H.
  by split=> -[a b]; split; [exact/inNP | exact/hard | exact/inNP | exact/hard].
split=> -[H [sub hnp]]; exists H; split.
- exact/A14.x114_subcubic_compat.
- exact/np.
- exact/A14.x114_subcubic_compat.
- exact/np.
Qed.
