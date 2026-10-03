(** * Ambient-radius branch sets and shallow minor models

    [ambient_radius_at_most G S r] uses the existing [graph_dist] of the HOST G:
    the centre lies in S, but distance paths may leave S. [graph_dist] searches
    [rel_ball] and is truncated at #|G|, including disconnected pairs. These
    conventions are retained explicitly; this is not an internal branch-radius
    predicate or a claim to repair the existing strong-colouring-number row.

    [ambient_shallow_minor G H r] supplies H-branches in G with this radius and
    upstream [minor_rmap] on the SAME map. Nonempty connected disjoint branches
    and realization of every pattern edge are retained. Empty H is allowed;
    there is no global inhabitance, covering-host or inducedness condition. *)
From GTBase Require Import base minor_models.
From GraphTheory Require Import minor.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition ambient_radius_at_most (G : sgraph) (S : {set G}) (r : nat) : Prop :=
  exists c : G,
    c \in S /\ forall x : G, x \in S -> @graph_dist G c x <= r.

Definition ambient_shallow_minor (G H : sgraph) (r : nat) : Prop :=
  exists branch : H -> {set G},
    minor_rmap branch /\ forall h : H, ambient_radius_at_most (branch h) r.

Lemma ambient_rel_ball_mono (T : finType) (e : rel T) (x : T) (k l : nat) :
  k <= l -> rel_ball e k x \subset rel_ball e l x.
Proof.
elim: l => [|l IH] in k *.
- by rewrite leqn0 => /eqP ->.
- rewrite leq_eqVlt ltnS => /orP [/eqP ->|kl]; first exact: subxx.
  exact: subset_trans (IH _ kl) (subsetUl _ _).
Qed.

Lemma ambient_graph_dist_ball (G : sgraph) (x y : G) (r : nat) :
  y \in rel_ball (--) r x -> graph_dist x y <= r.
Proof.
rewrite /graph_dist; case: ex_minnP => m _ minm br.
apply: minm; by rewrite br.
Qed.

Lemma ambient_graph_dist_smallE (G : sgraph) (x y : G) (r : nat) :
  r < #|G| -> (graph_dist x y <= r) = (y \in rel_ball (--) r x).
Proof.
move=> rG; rewrite /graph_dist; case: ex_minnP => m pm minm.
apply/idP/idP.
- move=> mr; have mG := leq_ltn_trans mr rG.
  have mb : y \in rel_ball (--) m x.
    by move: pm; rewrite (ltn_eqF mG) orbF.
  exact: (subsetP (@ambient_rel_ball_mono G (--) x m r mr) y mb).
- move=> br; apply: minm; by rewrite br.
Qed.

Lemma ambient_graph_dist_card (G : sgraph) (x y : G) :
  graph_dist x y <= #|G|.
Proof.
rewrite /graph_dist; case: ex_minnP => m _ minm.
apply: minm; by rewrite eqxx orbT.
Qed.

Lemma ambient_graph_distxx (G : sgraph) (x : G) : graph_dist x x = 0.
Proof.
apply/eqP; rewrite -leqn0; apply: ambient_graph_dist_ball.
by rewrite /= inE eqxx.
Qed.

Lemma ambient_radius_at_mostW (G : sgraph) (S : {set G}) (r s : nat) :
  r <= s -> ambient_radius_at_most S r -> ambient_radius_at_most S s.
Proof.
move=> rs [c [cS dist]]; exists c; split=> // x xS.
exact: leq_trans (dist x xS) rs.
Qed.

Lemma ambient_radius_nonempty (G : sgraph) (S : {set G}) (r : nat) :
  ambient_radius_at_most S r -> S != set0.
Proof. move=> [c [cS _]]; apply/set0Pn; by exists c. Qed.

Lemma not_ambient_radius_set0 (G : sgraph) (r : nat) :
  ~ ambient_radius_at_most (set0 : {set G}) r.
Proof. by move=> /ambient_radius_nonempty; rewrite eqxx. Qed.

Lemma ambient_radius_singleton (G : sgraph) (x : G) :
  ambient_radius_at_most [set x] 0.
Proof.
exists x; split; first by rewrite inE eqxx.
by move=> y /set1P ->; rewrite ambient_graph_distxx.
Qed.

Lemma ambient_radius_card (G : sgraph) (S : {set G}) :
  S != set0 -> ambient_radius_at_most S #|G|.
Proof.
move=> /set0Pn [c cS]; exists c; split=> // x _.
exact: ambient_graph_dist_card.
Qed.

Lemma ambient_shallow_minor_nestedE (G H : sgraph) (r : nat) :
  ambient_shallow_minor G H r <->
  exists branch : H -> {set G},
    (forall h : H, branch h != set0) /\
    (forall h : H, connected (branch h)) /\
    (forall h : H, ambient_radius_at_most (branch h) r) /\
    (forall h1 h2 : H, h1 != h2 -> branch h1 :&: branch h2 = set0) /\
    (forall h1 h2 : H, h1 -- h2 ->
      exists x y : G, [/\ x \in branch h1, y \in branch h2 & x -- y]).
Proof.
split.
- move=> [branch [/minor_rmap_nestedE [ne [co [dj ed]]] rad]].
  by exists branch; repeat split.
- move=> [branch [ne [co [rad [dj ed]]]]]; exists branch; split=> //.
  by apply/minor_rmap_nestedE; repeat split.
Qed.

Lemma ambient_shallow_minor_minor (G H : sgraph) (r : nat) :
  ambient_shallow_minor G H r -> minor G H.
Proof. by move=> [branch [model _]]; exact: minor_of_rmap model. Qed.

Lemma ambient_shallow_minorW (G H : sgraph) (r s : nat) :
  r <= s -> ambient_shallow_minor G H r -> ambient_shallow_minor G H s.
Proof.
move=> rs [branch [model rad]]; exists branch; split=> // h.
exact: ambient_radius_at_mostW rs (rad h).
Qed.

Lemma ambient_shallow_minor_empty_pattern (G : sgraph) (r : nat) :
  ambient_shallow_minor G 'K_0 r.
Proof.
exists (fun _ => set0); split; first exact: minor_rmap_empty_pattern.
by move=> [].
Qed.

Lemma not_ambient_shallow_minor_empty_host (H : sgraph) (h : H) (r : nat) :
  ~ ambient_shallow_minor 'K_0 H r.
Proof. by move=> [branch [model _]]; exact: (@not_minor_rmap_empty_host H h branch model). Qed.

Lemma ambient_shallow_minor_refl (G : sgraph) (r : nat) :
  ambient_shallow_minor G G r.
Proof.
exists (fun x => [set x]); split; first exact: minor_rmap_singletons.
move=> x; exact: (ambient_radius_at_mostW (leq0n r) (ambient_radius_singleton x)).
Qed.
