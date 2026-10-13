(** prism-configuration (Minor): the X220 3-prism and prism predicate, frozen at the family parent
    29336a8c9d22d7016d665c696c444bfb15dbefb5.
    - [Legacy]: [x220_prism3] (the explicit nine-edge [el_graph] of the 3-prism) and [x220_prism]
      verbatim, the predicate over the frozen graph and the current [subdiv_model] / [subdiv_rep];
      the endpoint value test, the adjacency hypothesis, the witness model and the empty
      interiors of the six triangle edges are kept.
    - [X220Legacy]: the complete current theta/prism row over [Legacy.x220_prism]; its theta,
      even-wheel, clique and treewidth helpers stay live.
    - [Original] / [X220Original]: the deepest row.  It is C19's
      [Minor.migration.model_support.X220Original] row (C19's raw subdivision support, B4's raw
      even-wheel chain) with its prism replaced by a prism over C19's raw [Legacy.subdiv_rep] and
      THIS family's frozen [Legacy.x220_prism3]: the explicit graph is frozen here, not inherited
      from the earlier snapshots that still apply the live [x220_prism3].
    Every certificate is a kernel conversion, except the Original, which goes through C19's
    certificate (and so B4's even-wheel certificate).  Earlier certificate files are unchanged. *)
From GTBase Require Import base.
From GraphTheory Require Import minor.
From Minor.foundations Require Import containment width_params prism_configurations.
From Minor.conjectures Require Import X27 X42 X220.
From Minor.migration Require model_support consecutive_in_cycle.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module MS := Minor.migration.model_support.
Module B4 := Minor.migration.consecutive_in_cycle.

Module Legacy.

Definition x220_prism3 : sgraph :=
  el_graph 6 [:: (0,1); (1,2); (0,2); (3,4); (4,5); (3,5); (0,3); (1,4); (2,5)].

Definition x220_prism (H : sgraph) : Prop :=
  exists m : subdiv_model Legacy.x220_prism3 H,
    subdiv_rep m /\
    forall u v : Legacy.x220_prism3,
      u -- v -> ((val u < 3) == (val v < 3)) -> sdm_path m u v = [::].

End Legacy.

Module X220Legacy.

Definition theta_prism_even_wheel_free_bounded_treewidth_statement : Prop :=
  forall t : nat, exists c : nat,
    forall G : sgraph,
      ~ has_induced_copy G (cycle_graph 4) ->
      ~ has_induced_copy G x42_diamond ->
      (forall H : sgraph, x220_theta H -> ~ has_induced_copy G H) ->
      (forall H : sgraph, Legacy.x220_prism H -> ~ has_induced_copy G H) ->
      x220_even_wheel_free G ->
      x220_clique_free G t ->
      tw_le G c.

End X220Legacy.

Module Original.

Definition x220_prism (H : sgraph) : Prop :=
  exists m : subdiv_model Legacy.x220_prism3 H,
    MS.Legacy.subdiv_rep m /\
    forall u v : Legacy.x220_prism3,
      u -- v -> ((val u < 3) == (val v < 3)) -> sdm_path m u v = [::].

End Original.

Module X220Original.

Definition theta_prism_even_wheel_free_bounded_treewidth_statement : Prop :=
  forall t : nat, exists c : nat,
    forall G : sgraph,
      ~ has_induced_copy G (cycle_graph 4) ->
      ~ has_induced_copy G x42_diamond ->
      (forall H : sgraph, MS.X220Legacy.x220_theta H -> ~ has_induced_copy G H) ->
      (forall H : sgraph, Original.x220_prism H -> ~ has_induced_copy G H) ->
      B4.X220Legacy.even_wheel_free G ->
      x220_clique_free G t ->
      tw_le G c.

End X220Original.

(** ** Certificates *)

Lemma x220_prism3_compat : Legacy.x220_prism3 = x220_prism3.
Proof. by []. Qed.

Lemma x220_prism_compat (H : sgraph) : Legacy.x220_prism H <-> x220_prism H.
Proof. exact: iff_refl. Qed.

Lemma theta_prism_even_wheel_free_bounded_treewidth_statement_compat :
  X220Legacy.theta_prism_even_wheel_free_bounded_treewidth_statement <->
  theta_prism_even_wheel_free_bounded_treewidth_statement.
Proof. exact: iff_refl. Qed.

Lemma x220_prism_original_compat (H : sgraph) : Original.x220_prism H <-> x220_prism H.
Proof. exact: iff_refl. Qed.

Lemma theta_prism_even_wheel_free_bounded_treewidth_statement_original_compat :
  X220Original.theta_prism_even_wheel_free_bounded_treewidth_statement <->
  theta_prism_even_wheel_free_bounded_treewidth_statement.
Proof. exact: MS.theta_prism_even_wheel_free_bounded_treewidth_statement_original_compat. Qed.

(** The frozen sources in the public vocabulary. *)
Lemma x220_prism3_canonical : Legacy.x220_prism3 = prism_base.
Proof. by []. Qed.

Lemma x220_prism_canonical (H : sgraph) : Legacy.x220_prism H <-> prism_configuration H.
Proof. exact: iff_refl. Qed.

Print Assumptions x220_prism3_compat.
Print Assumptions x220_prism_compat.
Print Assumptions theta_prism_even_wheel_free_bounded_treewidth_statement_compat.
Print Assumptions x220_prism_original_compat.
Print Assumptions theta_prism_even_wheel_free_bounded_treewidth_statement_original_compat.
Print Assumptions x220_prism3_canonical.
Print Assumptions x220_prism_canonical.
