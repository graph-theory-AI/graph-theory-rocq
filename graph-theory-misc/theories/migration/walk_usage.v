(** * GTMisc.migration.walk_usage — B28 certificates: D7's walk usage, its MaxEDP chain and row

    Frozen verbatim at the fixed B27 016b868: D7's [walk_uses s p u v] (the Boolean test that [(u, v)] or [(v, u)] is
    a pair of [zip (s :: p) p]; no edge, nonempty-walk, uniqueness, distinct-endpoint or terminal premise), the chain
    [edp_feasible] (both clauses: each demand of [S] routed by a nonempty walk [walkb], and the walks of distinct
    demands use no common pair), [edp_opt] (an [S] and [route] attain [k], and every feasible [S] has at most [k]
    demands), [edp_ratio_spec] (the Wagner planarity guard, then [dnat_val out <= k <= rho #|G| * dnat_val out]) and
    [maxedp_approx] (the same program realizes the specification and has polynomial cost on [enc_edp]), and the
    complete row [approximation_ratio_for_maximum_edge_disjoint_paths_statement] (some [p] and [rho] with
    [maxedp_approx p rho] and [little_o_sqrt rho]).  The row keeps its documented selection of the improvement branch
    and its value-estimation reading; the older two-branch wording of D7's Row 2 section comment and of the
    implications_D7 header is recorded, not repaired.  Since B28 the live [walk_uses] is
    [GTBase.walk_usage.seq_consecutiveb (s :: p) u v], the same body by conversion, so all six certificates below are
    kernel-checked conversions.  No earlier migration snapshot reaches these declarations. *)

From GraphTheory Require Import minor.
From GTBase Require Import base walk_usage.
From GTMisc.foundations Require Import complexity.
From GTMisc.conjectures Require Import D7.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Legacy.

Definition walk_uses {G : sgraph} (s : G) (p : seq G) (u v : G) : bool :=
  ((u, v) \in zip (s :: p) p) || ((v, u) \in zip (s :: p) p).

End Legacy.

Module D7Legacy.

Definition edp_feasible {G : sgraph} {D : seq (G * G)}
  (S : {set 'I_(size D)}) (route : 'I_(size D) -> seq G) : Prop :=
  (forall i : 'I_(size D), i \in S ->
     walkb (tnth (in_tuple D) i).1 (tnth (in_tuple D) i).2 (route i)) /\
  (forall (i j : 'I_(size D)) (u v : G),
     i \in S -> j \in S -> i != j ->
     Legacy.walk_uses (tnth (in_tuple D) i).1 (route i) u v ->
     ~~ Legacy.walk_uses (tnth (in_tuple D) j).1 (route j) u v).

Definition edp_opt {G : sgraph} (D : seq (G * G)) (k : nat) : Prop :=
  (exists (S : {set 'I_(size D)}) (route : 'I_(size D) -> seq G),
      D7Legacy.edp_feasible S route /\ #|S| = k) /\
  (forall (S : {set 'I_(size D)}) (route : 'I_(size D) -> seq G),
      D7Legacy.edp_feasible S route -> #|S| <= k).

Definition edp_ratio_spec (rho : nat -> nat) (x : edp_input) (out : data) : Prop :=
  forall k : nat,
    wagner_planar (projT1 x) -> D7Legacy.edp_opt (projT2 x) k ->
    dnat_val out <= k /\ k <= rho #|projT1 x| * dnat_val out.

Definition maxedp_approx (p : prog) (rho : nat -> nat) : Prop :=
  realizes_on enc_edp (D7Legacy.edp_ratio_spec rho) p /\ poly_cost_on enc_edp p.

Definition approximation_ratio_for_maximum_edge_disjoint_paths_statement : Prop :=
  exists (p : prog) (rho : nat -> nat),
    D7Legacy.maxedp_approx p rho /\ little_o_sqrt rho.

End D7Legacy.

Lemma walk_uses_compat (G : sgraph) (s : G) (p : seq G) (u v : G) :
  Legacy.walk_uses s p u v = walk_uses s p u v.
Proof. by []. Qed.

Lemma edp_feasible_compat (G : sgraph) (D : seq (G * G))
  (S : {set 'I_(size D)}) (route : 'I_(size D) -> seq G) :
  D7Legacy.edp_feasible S route <-> edp_feasible S route.
Proof. exact: iff_refl. Qed.

Lemma edp_opt_compat (G : sgraph) (D : seq (G * G)) (k : nat) :
  D7Legacy.edp_opt D k <-> edp_opt D k.
Proof. exact: iff_refl. Qed.

Lemma edp_ratio_spec_compat (rho : nat -> nat) (x : edp_input) (out : data) :
  D7Legacy.edp_ratio_spec rho x out <-> edp_ratio_spec rho x out.
Proof. exact: iff_refl. Qed.

Lemma maxedp_approx_compat (p : prog) (rho : nat -> nat) :
  D7Legacy.maxedp_approx p rho <-> maxedp_approx p rho.
Proof. exact: iff_refl. Qed.

Lemma approximation_ratio_for_maximum_edge_disjoint_paths_statement_compat :
  D7Legacy.approximation_ratio_for_maximum_edge_disjoint_paths_statement <->
  approximation_ratio_for_maximum_edge_disjoint_paths_statement.
Proof. exact: iff_refl. Qed.

Print Assumptions walk_uses_compat.
Print Assumptions edp_feasible_compat.
Print Assumptions edp_opt_compat.
Print Assumptions edp_ratio_spec_compat.
Print Assumptions maxedp_approx_compat.
Print Assumptions approximation_ratio_for_maximum_edge_disjoint_paths_statement_compat.
