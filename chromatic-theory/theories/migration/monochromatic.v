(** * Frozen monochromatic subsets and complete reaching statements (C8)
    Original source: 47eed16, before C8. Every frozen body below preserves
    the original binders, guards and witnesses; only the recorded family
    references are redirected to other frozen bodies. Existing source
    discrepancies and partial/blocked statuses are not repaired. *)
From GTBase Require Import base monochromatic.
From GTBase.migration Require monochromatic.
From Chromatic.conjectures Require Import X181 X194 X218.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module BaseLegacy := GTBase.migration.monochromatic.Legacy.

Module X181Legacy.

Definition x181_monochromatic
    (G : sgraph) (k : nat) (col : G -> 'I_k) (S : {set G}) : bool :=
  [forall x in S, [forall y in S, col x == col y]].

Definition x181_clique_colourable (G : sgraph) (k : nat) : bool :=
  [exists col : {ffun G -> 'I_k},
    [forall S : {set G},
      x181_maximal_clique S ==> ~~ X181Legacy.x181_monochromatic (fun v => col v) S]].

Definition x181_clique_chromatic_window
    (a b n : nat) (E : {set {set 'I_n}}) : bool :=
  let G := fg_labelled_sgraph E in
  [exists k : 'I_n.+1,
    [&& X181Legacy.x181_clique_colourable G k,
        (b - a) * (trunc_log 2 n) <= b * (2 * k)
      & b * (2 * k) <= (b + a) * (trunc_log 2 n).+1]].

Definition x181_random_graph_clique_chromatic_constant : Prop :=
  forall a b : nat, 0 < a -> a <= b ->
    @fg_whp (fun n : nat => {set {set 'I_n}})
      (fun n => @fg_gnp_weight 1 2 n)
      (X181Legacy.x181_clique_chromatic_window a b).

Definition random_graph_clique_chromatic_tight_constant_statement : Prop :=
  X181Legacy.x181_random_graph_clique_chromatic_constant.

End X181Legacy.

Module X194Legacy.

Definition x194_clustered_chromatic_minor_class_le (H : sgraph) (k : nat) : Prop :=
  exists c : nat,
    forall G : sgraph, ~ minor G H -> BaseLegacy.clustered_colouring G k c.

Definition clustered_chromatic_minor_class_treedepth_bound_statement : Prop :=
  forall H : sgraph,
    forall k : nat,
      2 <= k ->
      x194_treedepth_at_most H k ->
      X194Legacy.x194_clustered_chromatic_minor_class_le H (2 * k - 2).

End X194Legacy.

Module X218Legacy.

Definition x218_clustered_chromatic_class_le (F : sgraph -> Prop) (k : nat) : Prop :=
  exists c : nat, forall G : sgraph, F G -> BaseLegacy.clustered_colouring G k c.

Definition odd_minor_free_defective_clustered_treedepth_statement : Prop :=
  forall (H : sgraph) (k : nat),
    1 <= k ->
    x218_connected_treedepth_at_most H k ->
    ~ x218_connected_treedepth_at_most H k.-1 ->
    x218_defective_chromatic_class_le (fun G : sgraph => ~ x218_odd_minor G H) (k - 1) /\
    X218Legacy.x218_clustered_chromatic_class_le (fun G : sgraph => ~ x218_odd_minor G H) (k - 1).

End X218Legacy.

Lemma x181_monochromatic_compat (G : sgraph) k (col : G -> 'I_k) (S : {set G}) :
  X181Legacy.x181_monochromatic col S = x181_monochromatic col S.
Proof. by rewrite /X181Legacy.x181_monochromatic /x181_monochromatic monochromatic_onE. Qed.

Lemma x181_clique_colourable_compat (G : sgraph) k :
  X181Legacy.x181_clique_colourable G k = x181_clique_colourable G k.
Proof.
rewrite /X181Legacy.x181_clique_colourable /x181_clique_colourable.
apply: eq_existsb => col; apply: eq_forallb => S.
by rewrite x181_monochromatic_compat.
Qed.

Lemma x181_clique_chromatic_window_compat a b n E :
  @X181Legacy.x181_clique_chromatic_window a b n E = @x181_clique_chromatic_window a b n E.
Proof.
rewrite /X181Legacy.x181_clique_chromatic_window /x181_clique_chromatic_window.
by apply: eq_existsb => k; rewrite x181_clique_colourable_compat.
Qed.

Lemma x181_event_weight_compat a b n :
  fg_event_weight (@fg_gnp_weight 1 2 n) (@X181Legacy.x181_clique_chromatic_window a b n) =
  fg_event_weight (@fg_gnp_weight 1 2 n) (@x181_clique_chromatic_window a b n).
Proof.
by apply: eq_bigl => E; exact: x181_clique_chromatic_window_compat.
Qed.

Lemma x181_random_graph_clique_chromatic_constant_compat :
  X181Legacy.x181_random_graph_clique_chromatic_constant <->
  x181_random_graph_clique_chromatic_constant.
Proof.
rewrite /X181Legacy.x181_random_graph_clique_chromatic_constant
  /x181_random_graph_clique_chromatic_constant /fg_whp /eventually.
split=> h a b a0 ab c d c0 cd; have [N hn] := h a b a0 ab c d c0 cd; exists N => n Nn.
- by move: (hn n Nn); rewrite x181_event_weight_compat.
- by move: (hn n Nn); rewrite x181_event_weight_compat.
Qed.

Lemma random_graph_clique_chromatic_tight_constant_statement_compat :
  X181Legacy.random_graph_clique_chromatic_tight_constant_statement <->
  random_graph_clique_chromatic_tight_constant_statement.
Proof. exact: x181_random_graph_clique_chromatic_constant_compat. Qed.

Lemma x194_clustered_chromatic_minor_class_le_compat (H : sgraph) k :
  X194Legacy.x194_clustered_chromatic_minor_class_le H k <->
  x194_clustered_chromatic_minor_class_le H k.
Proof.
split=> -[c hc]; exists c => G minor_free; have hg := hc G minor_free.
all: by apply/GTBase.migration.monochromatic.clustered_colouring_compat.
Qed.

Lemma clustered_chromatic_minor_class_treedepth_bound_statement_compat :
  X194Legacy.clustered_chromatic_minor_class_treedepth_bound_statement <->
  clustered_chromatic_minor_class_treedepth_bound_statement.
Proof.
split=> h H k k2 td; have hc := h H k k2 td.
all: by apply/x194_clustered_chromatic_minor_class_le_compat.
Qed.

Lemma x218_clustered_chromatic_class_le_compat (F : sgraph -> Prop) k :
  X218Legacy.x218_clustered_chromatic_class_le F k <-> x218_clustered_chromatic_class_le F k.
Proof.
split=> -[c hc]; exists c => G in_class; have hg := hc G in_class.
all: by apply/GTBase.migration.monochromatic.clustered_colouring_compat.
Qed.

(** X218 RE-ENCODING (2026-11-02, PROGRAMME section 3, A2 + A4 re-encode; record meta/STATEMENT_IMPROVEMENTS.md),
    not a migration equivalence.  The live row is Conjecture 2 of arXiv:2308.15721v2 (clustered <= 2 ctd(H) - 2 and
    defective = ctd(H) - 1, over the source's tree model and connected tree-depth); the frozen row gave both class
    parameters the bound k - 1 over [x218_odd_minor].  No implication between them is certified.  The type below is
    the placeholder relation of the spec's repair entry, not a claim. *)
Lemma odd_minor_free_defective_clustered_treedepth_statement_compat :
  (X218Legacy.odd_minor_free_defective_clustered_treedepth_statement -> True) /\
  (odd_minor_free_defective_clustered_treedepth_statement -> True).
Proof. by split. Qed.

(** ** X218 re-encoding: the normalisation defect, kernel-checked *)

(* on K_3, the colouring (false, true, false) of the vertices 0, 1, 2 *)
Definition x218_normalisation_sigma (v : 'K_3) : bool := val v == 1.

(* the bichromatic edges inside the branch set {0, 1, 2} *)
Definition x218_normalisation_rel (a b : 'K_3) : bool :=
  [&& a \in [set: 'K_3], b \in [set: 'K_3], a -- b & x218_normalisation_sigma a != x218_normalisation_sigma b].

Definition x218_normalisation_v1 : 'K_3 := @Ordinal 3 1 isT.

(* every vertex of K_3 reaches the middle vertex 1 and back through bichromatic edges *)
Lemma x218_normalisation_hub (a : 'K_3) :
  connect x218_normalisation_rel a x218_normalisation_v1 /\ connect x218_normalisation_rel x218_normalisation_v1 a.
Proof.
case: a => [[|[|[|m]]] p].
- by split; apply: connect1; rewrite /x218_normalisation_rel /x218_normalisation_sigma !inE /=.
- have -> : Ordinal p = x218_normalisation_v1 by apply: val_inj.
  by split; exact: connect0.
- by split; apply: connect1; rewrite /x218_normalisation_rel /x218_normalisation_sigma !inE /=.
- by [].
Qed.

(* DEFECT (the normalisation): with H = K_1, the branch set {0, 1, 2} of K_3 is connected through its bichromatic
   edges 0-1 and 1-2, so the source's tree model (arXiv.tex l.139-145) accepts it, while the edge 0-2 inside it is
   monochromatic, which [x218_odd_minor]'s per-edge condition rejects *)
Lemma x218_normalisation_defect :
  (forall (x : 'K_1) (u v : 'K_3), connect x218_normalisation_rel u v) /\
  ~ (forall (x : 'K_1) (u v : 'K_3), u \in [set: 'K_3] -> v \in [set: 'K_3] -> u -- v ->
       x218_normalisation_sigma u != x218_normalisation_sigma v).
Proof.
split.
- move=> _ u v; have [cu _] := x218_normalisation_hub u; have [_ cv] := x218_normalisation_hub v.
  exact: connect_trans cu cv.
- by move=> /(_ ord0 (@Ordinal 3 0 isT) (@Ordinal 3 2 isT) (in_setT _) (in_setT _) isT).
Qed.

(* the frozen model is a special case of the source's: every [x218_odd_minor] model is a tree model, so the live
   class (no odd H-minor in the tree model) is contained in the frozen one; the converse is not claimed *)
Lemma x218_legacy_model_is_tree_model (G H : sgraph) : x218_odd_minor G H -> x218_odd_minor_tree_model G H.
Proof.
case=> B [sigma [ne conn dis bi mono]].
exists B, sigma; split=> // x u v uB vB.
apply: connect_sub (conn x u v uB vB) => a b /=.
case/andP=> /andP [aB bB] ab; apply: connect1; rewrite aB bB ab /=.
exact: bi x a b aB bB ab.
Qed.
