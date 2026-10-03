(** * Internal-radius branch sets and shallow minor models

    [internal_ball_in B c r] says that every vertex [v] of the supplied set [B]
    is reached from the supplied vertex [c] by a walk [c :: p] with [last c p = v]
    and at most [r] edges ([size p] counts edges), all of whose vertices lie
    INSIDE [B].  By itself it does not assert [c \in B]: on the empty set it holds
    for every [c] and [r] ([internal_ball_in_set0]); on a nonempty set it forces
    [c \in B] ([internal_ball_in_centre]).  The bound is an exact finite walk
    length.  No host distance and no [graph_dist] with its truncation at the
    number of vertices is involved, so a disconnected set is an internal ball for
    no centre and no radius ([not_internal_ball_in_disconnected]).

    [internal_shallow_minor G H r] supplies BOTH a branch map [B : H -> {set G}]
    and a centre map [ctr : H -> G]: upstream [minor_rmap] holds on the SAME map
    [B] (nonempty, connected, pairwise disjoint branches with a host edge between
    the branches of every pattern edge), each centre lies in its branch, and each
    branch is an internal ball of radius [r] around its centre.  The supplied-map
    adapter [internal_shallow_suppliedE] shows that, for the same [B] and [ctr],
    these clauses are equivalent to the explicit list "centre membership, internal
    ball, pairwise disjointness, edge realisation".  Extra host edges, unused host
    vertices and the empty pattern are allowed; there is no inducedness, covering
    or global nonemptiness condition.  Radius zero gives exactly the (not
    necessarily induced) subgraphs ([internal_shallow_minor0E]).

    This is not the ambient-radius contract of
    [GTMisc.foundations.ambient_shallow_minors], whose distances may leave the
    branch; no equivalence between the two is claimed. *)
From GTBase Require Import base minor_models.
From GraphTheory Require Import preliminaries minor.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition internal_ball_in (G : sgraph) (B : {set G}) (c : G) (r : nat) : Prop :=
  forall v : G, v \in B ->
    exists p : seq G,
      [/\ path (--) c p, last c p = v, size p <= r & all (mem B) (c :: p)].

Definition internal_shallow_minor (G H : sgraph) (r : nat) : Prop :=
  exists (B : H -> {set G}) (ctr : H -> G),
    [/\ minor_rmap B,
        forall x : H, ctr x \in B x &
        forall x : H, internal_ball_in (B x) (ctr x) r].

(** ** Internal balls *)

Lemma internal_ball_in_set0 (G : sgraph) (c : G) (r : nat) :
  internal_ball_in (set0 : {set G}) c r.
Proof. by move=> v; rewrite inE. Qed.

Lemma internal_ball_in_centre (G : sgraph) (B : {set G}) (c v : G) (r : nat) :
  v \in B -> internal_ball_in B c r -> c \in B.
Proof. by move=> vB /(_ v vB) [p [_ _ _ /andP [cB _]]]. Qed.

Lemma internal_ball_inW (G : sgraph) (B : {set G}) (c : G) (r s : nat) :
  r <= s -> internal_ball_in B c r -> internal_ball_in B c s.
Proof.
move=> rs ball v vB; have [p [pth lst sz inB]] := ball v vB.
by exists p; split=> //; exact: leq_trans sz rs.
Qed.

Lemma internal_ball_in_set1 (G : sgraph) (c : G) (r : nat) :
  internal_ball_in [set c] c r.
Proof.
move=> v; rewrite inE => /eqP ->; exists [::]; split=> //=.
by rewrite andbT inE.
Qed.

Lemma internal_ball_in0 (G : sgraph) (B : {set G}) (c : G) :
  internal_ball_in B c 0 -> B \subset [set c].
Proof.
move=> ball; apply/subsetP => v vB; have [p [_ lst sz _]] := ball v vB.
by move: sz lst; rewrite leqn0 size_eq0 => /eqP -> /= <-; rewrite inE.
Qed.

Lemma internal_ball_in_connect (G : sgraph) (B : {set G}) (c v : G) (r : nat) :
  internal_ball_in B c r -> v \in B -> connect (restrict B (--)) c v.
Proof.
move=> ball vB; have [p [pth <- _ inB]] := ball v vB.
apply/connectP; exists p => //.
apply: (sub_in_path _ inB pth) => x y xB yB xy /=.
by apply/andP; split; first (apply/andP; split).
Qed.

Lemma internal_ball_in_connected (G : sgraph) (B : {set G}) (c : G) (r : nat) :
  c \in B -> internal_ball_in B c r -> connected B.
Proof.
move=> cB ball; apply: (@connected_center _ c) => // v vB.
exact: internal_ball_in_connect ball vB.
Qed.

Lemma connected_internal_ball_in (G : sgraph) (B : {set G}) (c : G) (r : nat) :
  c \in B -> connected B -> #|B| <= r.+1 -> internal_ball_in B c r.
Proof.
move=> cB con Br v vB.
have /connectP [q qpth ->] := con c v cB vB.
case: (shortenP qpth) => p pth up _.
have inB : all (mem B) (c :: p).
  apply/andP; split=> //.
  elim: p c pth {cB qpth up} => [//|y p IH] x /= /andP [xy pth].
  move: xy => /andP [/andP [_ yB] _].
  by apply/andP; split; last exact: IH pth.
exists p; split=> //.
- by apply: sub_path pth => x y /andP [_ xy].
- have sub : {subset c :: p <= enum B}.
    by move=> z hz; rewrite mem_enum; exact: (allP inB).
  have := uniq_leq_size up sub; rewrite -cardE /= => pB.
  by rewrite -ltnS; exact: leq_trans pB Br.
Qed.

Lemma internal_ball_in_connectedE (G : sgraph) (B : {set G}) (c : G) :
  c \in B -> connected B <-> exists r : nat, internal_ball_in B c r.
Proof.
move=> cB; split=> [con|[r ball]].
- by exists #|B|; exact: connected_internal_ball_in cB con (leqnSn _).
- exact: internal_ball_in_connected cB ball.
Qed.

Lemma not_internal_ball_in_disconnected (G : sgraph) (B : {set G}) (c : G) (r : nat) :
  ~ connected B -> ~ internal_ball_in B c r.
Proof.
move=> ncon ball; apply: ncon.
have [->|[v vB]] := set_0Vmem B; first exact: connected0.
exact: internal_ball_in_connected (internal_ball_in_centre vB ball) ball.
Qed.

(** ** Shallow minor models on supplied maps *)

Lemma internal_shallow_suppliedE (G H : sgraph) (B : H -> {set G}) (ctr : H -> G)
    (r : nat) :
  [/\ minor_rmap B,
      forall x : H, ctr x \in B x &
      forall x : H, internal_ball_in (B x) (ctr x) r] <->
  [/\ forall x : H, ctr x \in B x,
      forall x : H, internal_ball_in (B x) (ctr x) r,
      forall x y : H, x != y -> [disjoint B x & B y] &
      forall x y : H, x -- y -> exists u v : G, [/\ u \in B x, v \in B y & u -- v]].
Proof.
split.
- by move=> [[_ _ dj ed] ctrB ball]; split=> // x y /ed /neighborP.
- move=> [ctrB ball dj ed]; split=> //; split=> //.
  + by move=> x; apply/set0Pn; exists (ctr x).
  + by move=> x; exact: internal_ball_in_connected (ctrB x) (ball x).
  + by move=> x y xy; apply/neighborP; exact: ed x y xy.
Qed.

Lemma internal_shallow_minorE (G H : sgraph) (r : nat) :
  internal_shallow_minor G H r <->
  exists (B : H -> {set G}) (ctr : H -> G),
    [/\ forall x : H, ctr x \in B x,
        forall x : H, internal_ball_in (B x) (ctr x) r,
        forall x y : H, x != y -> [disjoint B x & B y] &
        forall x y : H, x -- y -> exists u v : G, [/\ u \in B x, v \in B y & u -- v]].
Proof.
split=> -[B [ctr model]]; exists B, ctr.
- exact: (proj1 (internal_shallow_suppliedE B ctr r) model).
- exact: (proj2 (internal_shallow_suppliedE B ctr r) model).
Qed.

Lemma internal_shallow_minor_minor (G H : sgraph) (r : nat) :
  internal_shallow_minor G H r -> minor G H.
Proof. by move=> [B [ctr [model _ _]]]; exact: minor_of_rmap model. Qed.

Lemma internal_shallow_minor_card (G H : sgraph) (r : nat) :
  internal_shallow_minor G H r -> #|H| <= #|G|.
Proof. by move=> [B [ctr [model _ _]]]; exact: minor_rmap_card model. Qed.

Lemma internal_shallow_minorW (G H : sgraph) (r s : nat) :
  r <= s -> internal_shallow_minor G H r -> internal_shallow_minor G H s.
Proof.
move=> rs [B [ctr [model ctrB ball]]]; exists B, ctr; split=> // x.
exact: internal_ball_inW rs (ball x).
Qed.

Lemma internal_shallow_minor_empty_pattern (G : sgraph) (r : nat) :
  internal_shallow_minor G 'K_0 r.
Proof.
have ctr : 'K_0 -> G by move=> [].
exists (fun _ => set0), ctr; split; first exact: minor_rmap_empty_pattern.
- by move=> [].
- by move=> [].
Qed.

Lemma not_internal_shallow_minor_empty_host (H : sgraph) (h : H) (r : nat) :
  ~ internal_shallow_minor 'K_0 H r.
Proof.
by move=> [B [ctr [model _ _]]]; exact: (@not_minor_rmap_empty_host H h B model).
Qed.

Lemma internal_shallow_minor_refl (G : sgraph) (r : nat) :
  internal_shallow_minor G G r.
Proof.
exists (fun x => [set x]), id; split; first exact: minor_rmap_singletons.
- by move=> x; rewrite inE.
- by move=> x; exact: internal_ball_in_set1.
Qed.

Lemma internal_shallow_minor0E (G H : sgraph) :
  internal_shallow_minor G H 0 <-> has_subgraph G H.
Proof.
split.
- move=> [B [ctr [[_ _ dj ed] ctrB ball]]].
  have BE x : B x = [set ctr x].
    apply/eqP; rewrite eqEsubset; apply/andP; split; first exact: internal_ball_in0.
    by rewrite sub1set ctrB.
  apply/has_subgraphP; exists ctr; split.
  + move=> x y exy; apply/eqP; apply: contraT => nxy.
    by have := dj x y nxy; rewrite !BE disjoints1 inE exy eqxx.
  + move=> x y /ed /neighborP [u [v [ux vy uv]]].
    by move: ux vy; rewrite !BE !inE => /eqP <- /eqP <-.
- move=> /has_subgraphP [f [injf homf]].
  exists (fun x => [set f x]), f; split.
  + split.
    * by move=> x; apply/set0Pn; exists (f x); rewrite inE.
    * by move=> x; exact: connected1.
    * by move=> x y xy; rewrite disjoints1 inE (inj_eq injf).
    * by move=> x y xy; apply/neighborP; exists (f x), (f y); rewrite !inE !eqxx homf.
  + by move=> x; rewrite inE.
  + by move=> x; exact: internal_ball_in_set1.
Qed.
