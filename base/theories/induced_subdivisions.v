(** * Strong induced-subdivision models with full edge paths

    [induced_subdivision_model H G] (pattern [H] before host [G]) supplies:
    - injective branch vertices [isd_branch : H -> G];
    - a FULL vertex sequence [isd_edge_path u v] for every ordered pair of pattern
      vertices; only pattern edges are constrained, and nothing relates
      [isd_edge_path u v] to [isd_edge_path v u] (no reversal coherence);
    - for every pattern edge [u -- v], an endpoint-inclusive induced path: the
      sequence is nonempty, starts at [isd_branch u], ends at [isd_branch v], is
      duplicate-free, follows host edges, and any host edge between two of its
      vertices joins consecutive entries ([seq_consecutive]); in particular the
      empty sequence is never valid and a singleton forces equal endpoints;
    - internal vertices ([x] in the sequence, different from both endpoints) avoid
      every branch vertex;
    - a shared internal vertex forces the same undirected pattern edge;
    - global inducedness: a host edge between two vertices of the raw support
      ([GTBase.model_support.model_support], branch images and genuine-edge list
      entries) joins consecutive entries of some pattern-edge sequence.
    The Prop fields are stated with exactly the formulas of the X98 and X114
    copies (the endpoint-inclusive induced-path match, the internal-vertex
    conjunction, [seq_consecutive], raw support), so those copies' field types are
    convertible to these.  There is no nonempty-graph, positive-length, reversal or
    off-edge condition.  [induced_subdivision H G] is the inhabitation of the
    Record.

    This is not [Minor.foundations.containment.subdiv_model]: that Record stores
    interior vertices, requires reversal coherence, has no inducedness, and its
    [has_subdivision G H] puts the host first.  Import explicitly; [GTBase.base]
    does not re-export this module. *)
From GTBase Require Import base model_support.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

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
  inhabited (induced_subdivision_model H G).

Section Basics.
Variables (H G : sgraph) (m : induced_subdivision_model H G).

(** Pattern-edge sequences are endpoint-inclusive: nonempty, from [isd_branch u]
    to [isd_branch v]. *)
Lemma isd_edge_path_ends (u v : H) :
  u -- v ->
  exists q : seq G, isd_edge_path m u v = isd_branch m u :: q /\ last (isd_branch m u) q = isd_branch m v.
Proof.
move=> uv; have := isd_edge_path_valid m uv.
by case: (isd_edge_path m u v) => [//|x q] [-> [lst _]]; exists q.
Qed.

Lemma isd_edge_path_nil (u v : H) : u -- v -> isd_edge_path m u v != [::].
Proof. by move=> uv; have [q [-> _]] := isd_edge_path_ends uv. Qed.

Lemma isd_branch_supported (h : H) :
  model_support (isd_branch m) (isd_edge_path m) (isd_branch m h).
Proof. exact: model_support_branch. Qed.

Lemma isd_edge_path_supported (u v : H) (x : G) :
  u -- v -> x \in isd_edge_path m u v -> model_support (isd_branch m) (isd_edge_path m) x.
Proof. exact: model_support_edge. Qed.

End Basics.

(** Sequences on non-edges are unconstrained: replacing them keeps a model with the same
    branch vertices and the same pattern-edge sequences. *)
Lemma isd_off_edge_free (H G : sgraph) (m : induced_subdivision_model H G) (ep : H -> H -> seq G) :
  (forall u v : H, u -- v -> ep u v = isd_edge_path m u v) ->
  exists m' : induced_subdivision_model H G,
    isd_branch m' = isd_branch m /\ forall u v : H, isd_edge_path m' u v = ep u v.
Proof.
case: m => br inj ep0 valid avoid disj glob /= same.
unshelve eexists (@InducedSubdivisionModel H G br inj ep _ _ _ _).
- by move=> u v uv; rewrite (same u v uv); exact: valid uv.
- by move=> u v w x uv; rewrite (same u v uv); exact: avoid uv.
- by move=> u v u' v' x uv uv'; rewrite (same u v uv) (same u' v' uv'); exact: disj uv uv'.
- move=> x y sx sy xy.
  have [u [v [uv c]]] := glob x y (proj1 (@model_support_eq_on_edges H G br ep ep0 x same) sx)
    (proj1 (@model_support_eq_on_edges H G br ep ep0 y same) sy) xy.
  by exists u, v; split=> //; rewrite (same u v uv).
- by [].
Qed.

Lemma induced_subdivision_card (H G : sgraph) : induced_subdivision H G -> #|H| <= #|G|.
Proof. by case=> m; exact: (@leq_card _ _ (isd_branch m) (@isd_branch_injective _ _ m)). Qed.

(** ** Basic models *)

Lemma pair_seq_internal (G : sgraph) (u v x : G) :
  x \in [:: u; v] /\ x != u /\ x != v -> False.
Proof. by rewrite !inE => -[/orP [] /eqP -> [] ]; rewrite eqxx.
Qed.

Lemma pair_seq_consecutive (G : sgraph) (u v : G) : seq_consecutive [:: u; v] u v.
Proof. by left; rewrite /= inE eqxx. Qed.

Lemma pair_seq_consecutive_rev (G : sgraph) (u v : G) : seq_consecutive [:: u; v] v u.
Proof. by right; rewrite /= inE eqxx. Qed.

(** Every graph is a strong induced subdivision of itself: identity branches and the
    two-vertex sequence [[:: u; v]] for every pair. *)
Definition identity_induced_subdivision_model (G : sgraph) : induced_subdivision_model G G.
Proof.
apply: (@InducedSubdivisionModel G G id (@inj_id G) (fun u v => [:: u; v])).
- move=> u v uv /=; do 2 (split=> //); split.
    by rewrite /= inE andbT (sg_edgeNeq uv).
  split; first by rewrite /= uv.
  move=> a b; rewrite !inE => /orP [] /eqP -> /orP [] /eqP ->; rewrite ?sg_irrefl // => _ _.
  + exact: pair_seq_consecutive.
  + exact: pair_seq_consecutive_rev.
- by move=> u v w x _ /pair_seq_internal.
- by move=> u v u' v' x _ _ /pair_seq_internal.
- by move=> x y _ _ xy; exists x, y; split=> //; exact: pair_seq_consecutive.
Defined.

Lemma induced_subdivision_refl (G : sgraph) : induced_subdivision G G.
Proof. by constructor; exact: identity_induced_subdivision_model. Qed.

(** The empty pattern has a model in every host. *)
Lemma induced_subdivision_K0 (G : sgraph) : induced_subdivision 'K_0 G.
Proof.
have br : 'K_0 -> G by move=> [].
constructor; apply: (@InducedSubdivisionModel 'K_0 G br _ (fun _ _ => [::])).
- by move=> [].
- by move=> [].
- by move=> [].
- by move=> [].
- by move=> x y /model_support_K0.
Qed.

(** A nonempty pattern has no model in the empty host. *)
Lemma not_induced_subdivision_empty_host (H : sgraph) (h : H) : ~ induced_subdivision H 'K_0.
Proof. by case=> m; case: (isd_branch m h). Qed.

(** A single pattern vertex has a model exactly in a nonempty host: there are no
    pattern edges, so host edges at the branch vertex are irrelevant. *)
Lemma induced_subdivision_K1 (G : sgraph) : induced_subdivision 'K_1 G <-> 0 < #|G|.
Proof.
split=> [/induced_subdivision_card|G0]; first by rewrite card_ord.
have [g _] := card_gt0P G0 ; constructor.
apply: (@InducedSubdivisionModel 'K_1 G (fun _ => g) _ (fun _ _ => [::])).
- by move=> u v _; rewrite (fintype.ord1 u) (fintype.ord1 v).
- by move=> u v; rewrite (fintype.ord1 u) (fintype.ord1 v).
- by move=> u v w x; rewrite (fintype.ord1 u) (fintype.ord1 v).
- by move=> u v u' v' x; rewrite (fintype.ord1 u) (fintype.ord1 v).
- have nil : forall u v : ('K_1), u -- v -> (fun _ _ : 'K_1 => [::] : seq G) u v = [::] by [].
  move=> x y /(model_support_nil _ _ nil) [h <-] /(model_support_nil _ _ nil) [h' <-].
  by rewrite /= sg_irrefl.
Qed.
