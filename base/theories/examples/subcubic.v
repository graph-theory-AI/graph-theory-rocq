(** Downstream use of the simple-graph subcubic bound ([subcubic]), without corpus imports: the
    maximum-degree bridge, the empty graph, complete graphs, regular graphs and isomorphisms.
    The multigraph incidence contracts [mcubic]/[loopless_cubic] are separate (examples/mregular.v). *)
From GTBase Require Import base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** The pointwise bound and the maximum-degree bound agree on every graph. *)
Example pointwise_iff_Delta (G : sgraph) : subcubic G <-> Delta G <= 3.
Proof. exact: subcubicP. Qed.

(** The empty graph is subcubic in both readings (vacuously, and because its [Delta] is 0). *)
Example K0_subcubic : subcubic 'K_0 /\ Delta 'K_0 <= 3.
Proof. by split; [|apply/subcubicP]; exact: subcubic_K0. Qed.

Example K4_subcubic : subcubic 'K_4 /\ Delta 'K_4 <= 3.
Proof. by split; [|apply/subcubicP]; exact: (@subcubic_Kn 3). Qed.

(** [K_5] fails both readings. *)
Example K5_not_subcubic : ~ subcubic 'K_5 /\ ~ Delta 'K_5 <= 3.
Proof. by split=> [|/subcubicP]; exact: not_subcubic_K5. Qed.

(** An upper bound, not an exact degree: [K_2] is subcubic but not 3-regular. *)
Example K2_subcubic_not_3_regular : subcubic 'K_2 /\ ~ regular 'K_2 3.
Proof.
split; first exact: (@subcubic_Kn 1).
by move=> h; have := min_degree_uniq (regular_min_degree (ord0 : 'K_2) h) (min_degree_Kn 1).
Qed.

Example cubic_graphs (G : sgraph) : regular G 3 -> subcubic G.
Proof. by move=> h; exact: regular_subcubic h _. Qed.

Example isomorphic_graphs (G H : sgraph) (i : G ≃ H) : subcubic G -> subcubic H.
Proof. exact: subcubic_diso. Qed.

Print Assumptions pointwise_iff_Delta.
Print Assumptions K0_subcubic.
Print Assumptions K5_not_subcubic.
Print Assumptions K2_subcubic_not_3_regular.
Print Assumptions isomorphic_graphs.
