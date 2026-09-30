(** * Infinite.conjectures.D4inf3 — the two ENDS rows.

    Both are built on the combinatorial end-equivalence [end_equiv]
    (foundations.igraph), itself on [finite_sub]/[reachP] — no point-set topology,
    no Freudenthal compactification, no choice.

    - end_devouring_rays (done): a purely combinatorial reconfiguration claim.
    - infinite_uniquely_hamiltonian (PARTIAL): "uniquely hamiltonian" is rendered
      by a spanning DOUBLE RAY (an [int]-indexed two-way path).  In the co-assumed
      one-ended locally-finite class a Hamilton CIRCLE of [|G|] collapses to a
      spanning double ray, so this is a faithful proxy there — but it is NOT the
      general topological Hamilton circle, hence PARTIAL. *)

From GTBase Require Export base.
From Infinite Require Import foundations.igraph.
From mathcomp Require Import all_boot.
From mathcomp Require Import all_algebra.
Import GRing.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** end_devouring_rays  (Problem, OPEN)

    Source: "Let [G] be a graph, [ω] a countable end, [K] an infinite set of
    pairwise-disjoint [ω]-rays.  Prove there is a set [K'] of pairwise-disjoint
    [ω]-rays that DEVOURS [ω] whose set of starting vertices equals that of [K]."

    The end [ω] is given by a representative ray [r0]; an [ω]-ray is a ray
    end-equivalent to [r0] ([wray]).  [K],[K'] are [nat]-indexed families of rays
    (infinite + pairwise disjoint).  [K'] DEVOURS [ω] when every [ω]-ray meets
    some ray of [K']; [same_start] equates the two families' initial vertices.
    "Countable end" is guarded by [countable_graph]. *)
Definition wray (G : iGraph) (r0 r : nat -> iV G) : Prop :=
  ray r /\ end_equiv r r0.
Definition disjoint_rays (G : iGraph) (K : nat -> nat -> iV G) : Prop :=
  forall i j n m, i <> j -> K i n <> K j m.
Definition devours (G : iGraph) (r0 : nat -> iV G) (K' : nat -> nat -> iV G) : Prop :=
  forall r : nat -> iV G, wray r0 r -> exists i n m, r n = K' i m.
Definition same_start (G : iGraph) (K K' : nat -> nat -> iV G) : Prop :=
  (forall i, exists j, K' j 0 = K i 0) /\ (forall j, exists i, K i 0 = K' j 0).

(** Corpus row: opg:end_devouring_rays
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/end_devouring_rays/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/end_devouring_rays.json
    English statement: (Open Problem Garden, "End-Devouring Rays") Let G be a
      countable graph, r0 a ray of G (an injective sequence of vertices with
      consecutive entries adjacent) representing an end, and K a nat-indexed
      family of pairwise disjoint rays all end-equivalent to r0.  Then there is
      a nat-indexed family K' of pairwise disjoint rays, again all
      end-equivalent to r0, that DEVOURS the end - every ray end-equivalent to
      r0 meets some ray of K' - and whose set of starting vertices is exactly
      that of K.
    Definitions: [iGraph]/[iV]/[iadj], [ray r] (injective, consecutive entries
      adjacent), [countable_graph G] (the vertex type injects into nat),
      [finite_sub], [reachP] and [end_equiv r r'] (no finite vertex set
      separates the tails of the two rays) - all in
      infinite-graph-theory/theories/foundations/igraph.v; [wray r0 r] - r is a
      ray end-equivalent to r0 (this file, D4inf3.v); [disjoint_rays K] - rays
      with different indices share no vertex (D4inf3.v); [devours r0 K']
      (D4inf3.v); [same_start K K'] - the two families have the same set of
      initial vertices (D4inf3.v).
    Notes: ends are handled combinatorially (Halin's ray equivalence, built on
      finite separators and finite-walk reachability) - no point-set topology,
      no Freudenthal compactification, no choice.  The end omega is given by a
      REPRESENTATIVE ray r0 rather than as an equivalence class, and "countable
      end" is guarded by countability of the whole graph, which is a slightly
      stronger hypothesis than the source's.  "An infinite set of pairwise
      disjoint rays" is a nat-indexed family with [disjoint_rays]; the family
      need not be injective in the index, but distinct indices give
      vertex-disjoint rays, which forces infinitely many distinct rays. *)
Definition end_devouring_rays_statement : Prop :=
  forall (G : iGraph) (r0 : nat -> iV G) (K : nat -> nat -> iV G),
    countable_graph G -> ray r0 ->
    (forall i, wray r0 (K i)) -> disjoint_rays K ->
    exists K' : nat -> nat -> iV G,
      [/\ (forall i, wray r0 (K' i)), disjoint_rays K',
          devours r0 K' & same_start K K' ].

(** ** infinite_uniquely_hamiltonian_graphs  (Problem, OPEN — PARTIAL proxy)

    Source: "Are there uniquely hamiltonian locally finite 1-ended graphs which
    are regular of degree r > 2?"

    [locally_finite]/[regular r]/[one_ended] are combinatorial (finite_sub,
    end_equiv).  A DOUBLE RAY is an injective [int]-indexed path; a SPANNING one
    is a Hamilton-circle proxy; [uniquely_hamiltonian] asks for one that is unique
    up to its edge set ([same_circle]). *)
Definition locally_finite (G : iGraph) : Prop :=
  forall x : iV G, finite_sub (fun w => iadj x w).
Definition regular (r : nat) (G : iGraph) : Prop :=
  forall x : iV G, exists e : 'I_r -> iV G,
    injective e /\ (forall w, iadj x w <-> exists i, e i = w).
Definition one_ended (G : iGraph) : Prop :=
  (exists r : nat -> iV G, ray r) /\
  (forall r r' : nat -> iV G, ray r -> ray r' -> end_equiv r r').

Definition dray (G : iGraph) (d : int -> iV G) : Prop :=
  injective d /\ forall n : int, iadj (d n) (d (n + 1)%R).
Definition spanning_dray (G : iGraph) (d : int -> iV G) : Prop :=
  dray d /\ forall x : iV G, exists n : int, d n = x.
Definition dray_edge (G : iGraph) (d : int -> iV G) (x y : iV G) : Prop :=
  exists n : int, (d n = x /\ d (n + 1)%R = y) \/ (d n = y /\ d (n + 1)%R = x).
Definition same_circle (G : iGraph) (d d' : int -> iV G) : Prop :=
  forall x y, dray_edge d x y <-> dray_edge d' x y.
Definition uniquely_hamiltonian (G : iGraph) : Prop :=
  exists d : int -> iV G,
    spanning_dray d /\ forall d', spanning_dray d' -> same_circle d d'.

(** Corpus row: opg:infinite_uniquely_hamiltonian_graphs
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/infinite_uniquely_hamiltonian_graphs/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/infinite_uniquely_hamiltonian_graphs.json
    English statement: (Open Problem Garden, "Infinite uniquely hamiltonian
      graphs") There exist a graph G and a degree r > 2 such that G is locally
      finite (every neighbourhood is finite), r-regular (every vertex has
      exactly r neighbours), one-ended (G has a ray and all its rays are
      end-equivalent) and uniquely hamiltonian in the double-ray sense: G has a
      spanning double ray - an injective path indexed by the integers passing
      through every vertex - and every spanning double ray of G has the same
      edge set as it.
    Definitions: [iGraph]/[iV]/[iadj], [ray], [end_equiv], [finite_sub] -
      infinite-graph-theory/theories/foundations/igraph.v; [locally_finite G],
      [regular r G], [one_ended G], [dray d] (an injective integer-indexed
      path), [spanning_dray d], [dray_edge d x y], [same_circle d d'] and
      [uniquely_hamiltonian G] - all in this file, D4inf3.v.
    Notes: PARTIAL, one labelled PROXY.  The source's "uniquely hamiltonian" for
      an infinite graph means a unique Hamilton CIRCLE in the Freudenthal
      compactification; that topological notion is proxied by a spanning DOUBLE
      RAY.  In the co-assumed locally finite one-ended class a Hamilton circle
      collapses to a spanning double ray, so the proxy is faithful there, but it
      is not the general notion - hence the corpus leg is `partial`.  The local
      [regular] shadows base's [regular] (a different, [sgraph]-valued
      constant); the source poses a question and the body asserts existence. *)
Definition infinite_uniquely_hamiltonian_graphs_statement : Prop :=
  exists (G : iGraph) (r : nat),
    [/\ 2 < r, locally_finite G, regular r G, one_ended G & uniquely_hamiltonian G].
