(** C19 (Minor): raw subdivision-model support, frozen at the private union
    bb0bf3cd7c1d14e014704ebd5e24b03e4c475cb8 (exact C18 15a5a5c + reviewed A14
    f52251a).
    - [Legacy]: the public [Minor.foundations.containment.sdm_covers] verbatim in
      the same Section shape ([K H : sgraph], [m : subdiv_model K H]), so its
      discharged type keeps the explicit Section arguments; the live definition
      now unfolds to [GTBase.model_support.model_support (sdm_branch m)
      (sdm_path m) x].  [subdiv_rep] and [is_subdivision_of] are frozen over it;
      inside the copied Section the live, already discharged [sdm_realises] is
      named with its Section arguments, [@sdm_realises K H m]; the frozen
      [sdm_covers] is closed in its own Section first and named the same way.
    - [X220Legacy]: [x220_theta], [x220_prism] and the two complete current rows
      over the frozen chain; B4's [x220_even_wheel_free] stays live here.
    - [X220Original]: the complete theta/prism row, combining this family's frozen
      chain with B4's frozen even-wheel chain.  B4's own X220 snapshot remains
      unchanged.
    The raw support is read on Minor's INTERIOR lists; no Record of the X98/X114
    full-path presentation is identified with [subdiv_model].  Every certificate
    is a kernel-checked conversion.  The earlier B4 module is aliased, not
    imported. *)
From GTBase Require Import base model_support.
From GraphTheory Require Import minor.
From Minor.foundations Require Import containment width_params.
From Minor.conjectures Require Import X27 X42 X220.
From Minor.migration Require consecutive_in_cycle.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module B4 := Minor.migration.consecutive_in_cycle.

Module Legacy.

Section IsSubdivision.
Variables (K H : sgraph) (m : subdiv_model K H).

Definition sdm_covers (x : H) : Prop :=
  (exists u : K, sdm_branch m u = x) \/
  (exists u v : K, u -- v /\ x \in sdm_path m u v).

End IsSubdivision.

Section IsSubdivisionRep.
Variables (K H : sgraph) (m : subdiv_model K H).

Definition subdiv_rep : Prop :=
  (forall x : H, (@Legacy.sdm_covers K H m) x) /\ (forall x y : H, x -- y -> (@sdm_realises K H m) x y).

End IsSubdivisionRep.

Definition is_subdivision_of (H K : sgraph) : Prop :=
  exists m : subdiv_model K H, Legacy.subdiv_rep m.

End Legacy.

Module X220Legacy.

Definition x220_theta (H : sgraph) : Prop := Legacy.is_subdivision_of H (KB 2 3).

Definition x220_prism (H : sgraph) : Prop :=
  exists m : subdiv_model x220_prism3 H,
    Legacy.subdiv_rep m /\
    forall u v : x220_prism3,
      u -- v -> ((val u < 3) == (val v < 3)) -> sdm_path m u v = [::].

Definition four_family_free_logarithmic_treewidth_statement : Prop :=
  forall t : nat, exists c : nat,
    forall G : sgraph,
      ~ has_induced_copy G 'K_t ->
      ~ has_induced_copy G (KB t t) ->
      (forall W : sgraph, Legacy.is_subdivision_of W (x220_wall t) -> ~ has_induced_copy G W) ->
      (forall W : sgraph, Legacy.is_subdivision_of W (x220_wall t) ->
         ~ has_induced_copy G (sline_graph W)) ->
      tw_le G (c * (trunc_log 2 #|G|).+1).

Definition theta_prism_even_wheel_free_bounded_treewidth_statement : Prop :=
  forall t : nat, exists c : nat,
    forall G : sgraph,
      ~ has_induced_copy G (cycle_graph 4) ->
      ~ has_induced_copy G x42_diamond ->
      (forall H : sgraph, X220Legacy.x220_theta H -> ~ has_induced_copy G H) ->
      (forall H : sgraph, X220Legacy.x220_prism H -> ~ has_induced_copy G H) ->
      x220_even_wheel_free G ->
      x220_clique_free G t ->
      tw_le G c.

End X220Legacy.

Module X220Original.

Definition theta_prism_even_wheel_free_bounded_treewidth_statement : Prop :=
  forall t : nat, exists c : nat,
    forall G : sgraph,
      ~ has_induced_copy G (cycle_graph 4) ->
      ~ has_induced_copy G x42_diamond ->
      (forall H : sgraph, X220Legacy.x220_theta H -> ~ has_induced_copy G H) ->
      (forall H : sgraph, X220Legacy.x220_prism H -> ~ has_induced_copy G H) ->
      B4.X220Legacy.even_wheel_free G ->
      x220_clique_free G t ->
      tw_le G c.

End X220Original.

(** ** Certificates *)

Lemma sdm_covers_compat (K H : sgraph) (m : subdiv_model K H) (x : H) :
  Legacy.sdm_covers m x <-> sdm_covers m x.
Proof. exact: iff_refl. Qed.

Lemma subdiv_rep_compat (K H : sgraph) (m : subdiv_model K H) :
  Legacy.subdiv_rep m <-> subdiv_rep m.
Proof. exact: iff_refl. Qed.

Lemma is_subdivision_of_compat (H K : sgraph) :
  Legacy.is_subdivision_of H K <-> is_subdivision_of H K.
Proof. exact: iff_refl. Qed.

Lemma x220_theta_compat (H : sgraph) : X220Legacy.x220_theta H <-> x220_theta H.
Proof. exact: iff_refl. Qed.

Lemma x220_prism_compat (H : sgraph) : X220Legacy.x220_prism H <-> x220_prism H.
Proof. exact: iff_refl. Qed.

Lemma four_family_free_logarithmic_treewidth_statement_compat :
  X220Legacy.four_family_free_logarithmic_treewidth_statement <->
  four_family_free_logarithmic_treewidth_statement.
Proof. exact: iff_refl. Qed.

Lemma theta_prism_even_wheel_free_bounded_treewidth_statement_compat :
  X220Legacy.theta_prism_even_wheel_free_bounded_treewidth_statement <->
  theta_prism_even_wheel_free_bounded_treewidth_statement.
Proof. exact: iff_refl. Qed.

Lemma theta_prism_even_wheel_free_bounded_treewidth_statement_original_compat :
  X220Original.theta_prism_even_wheel_free_bounded_treewidth_statement <->
  theta_prism_even_wheel_free_bounded_treewidth_statement.
Proof. exact: iff_refl. Qed.
