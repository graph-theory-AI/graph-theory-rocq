(** * Signed rotation systems — general (orientable OR non-orientable) combinatorial maps.

    Track-A extension closing the orientability gap found by the adversarial review:
    plain rotation systems ([Topological.foundations.embedding]) capture exactly the
    ORIENTABLE cellular embeddings (Heffter–Edmonds), so rows whose source says
    "embedded in a surface" (any surface) were only expressible in a strictly
    stronger orientable form.  Following Mohar–Thomassen (Graphs on Surfaces, §3.3,
    embedding schemes), a general map is a rotation system PLUS an edge signature:

    - [emap G]  = an [embedding G] (the rotation) + [stwist : dart G -> bool]
      (per-edge signature: [true] = the edge is orientation-reversing/"twisted"),
      edge-consistent ([stwist_edge]);
    - face tracing runs on FLAGS [dart G * bool] (a dart with a local orientation):
      rotate by the current sign (forward on [true], backward on [false]), then
      cross the edge, flipping the sign iff the crossed edge is twisted
      ([sface_fun] / [sface_perm]).  On the all-[false] signature the
      [true]-flags reproduce the orientable [face_perm] exactly.
    - Each geometric face is traced TWICE (once per direction), so the face count
      in flags is [emFs = 2F], and the (unified, crosscap-scale) EULER GENUS is
      computed by the doubled relation
        [seuler_genus = (4 + 2E - 2V - emFs) / 2  ( = 2 - χ )].
      AUDIT STATUS of the doubling: the mirror involution
      [τ (d,s) := (edge_perm d, ~~(s (+) stwist d))] conjugates [sface_perm] to
      its inverse, is fixed-point-free, and never fixes an orbit (adversarial
      audit, machine-checked in probes; the τ/no-self-mirror lemmas are not yet
      Qed'd IN this file — a hardening TODO).  Fail-safe direction: were a
      self-mirrored orbit ever possible, [emFs] would UNDERcount flags per face,
      so [seuler_genus] could only OVER-estimate, never certify a too-small genus.
      On the trivial signature the [true]-flags reproduce [face_perm] exactly, so
      [seuler_genus (emap_of E) = 2 * euler_genus E] (audit-verified).
      Scale note: orientable surface S_g has Euler genus 2g and non-orientable
      N_k has Euler genus k, so for the trivial signature
      [seuler_genus (emap_of E) = 2 * euler_genus E] by design.
    - [orientable_map M] = the signature is SWITCHING-TRIVIAL: some vertex
      2-colouring [o] has [stwist d = o (source d) (+) o (target d)] (switching a
      vertex toggles the signs of its incident edges; a map embeds in an
      orientable surface iff its signature switches to all-[false]).
    - [circular_emap M] = every face boundary is a CYCLE (the source map is
      injective on every face orbit) — the general-surface strong-embedding
      predicate needed by the circular-embedding conjecture.

    SCOPE CAVEATS (inherited from the orientable layer, same review): the doubled
    Euler relation is the CONNECTED-map one over truncating nat arithmetic, so
    consumers must carry a connectivity hypothesis.  The isolated-vertex caveat is
    GONE since 2026-09-23: [emV] is now [#|G|] (embedding.v, mirroring
    base/theories/surface.v), so isolated vertices are counted and an edgeless graph
    with at least one vertex has genus 0; only the EMPTY graph still hits the
    empty-map truncation anomaly.  Everything is finite/decidable at the term level,
    hence axiom-free. *)

From mathcomp Require Import all_boot fingroup perm.
From GTBase Require Import base.
From Topological.foundations Require Import embedding.
Set Implicit Arguments.
Unset Strict Implicit.

Section Signed.
Variable G : sgraph.

Record emap := EMap {
  smap : embedding G;
  stwist : dart G -> bool;
  stwist_edge : forall d : dart G, stwist (edge_perm G d) = stwist d }.

(** Directed rotation: forward on [true] flags, backward on [false] flags. *)
Definition srot_dir (M : emap) (s : bool) : {perm dart G} :=
  if s then erot (smap M) else ((erot (smap M))^-1)%g.

(** Signed face tracing on flags: rotate by the current sign, then cross the
    edge, flipping the sign iff the crossed edge is twisted. *)
Definition sface_fun (M : emap) (x : dart G * bool) : dart G * bool :=
  let y := srot_dir M x.2 x.1 in (edge_perm G y, x.2 (+) stwist M y).

Lemma sface_inj (M : emap) : injective (sface_fun M).
Proof.
move=> [d1 s1] [d2 s2]; rewrite /sface_fun /=.
case=> /perm_inj Ey Es.
have Es12 : s1 = s2 by move: Es; rewrite Ey => /addIb.
apply/eqP; rewrite xpair_eqE; apply/andP; split; apply/eqP => //.
move: Ey; rewrite /srot_dir Es12; case: (s2) => /perm_inj //.
Qed.
Definition sface_perm (M : emap) : {perm (dart G * bool)%type} := perm (@sface_inj M).

(** Flag-face count ([= 2 ×] geometric faces) and the doubled-relation Euler genus. *)
Definition emFs (M : emap) : nat := #|porbits (sface_perm M)|.
Definition seuler_genus (M : emap) : nat :=
  (4 + 2 * emE G - 2 * emV (smap M) - emFs M) %/ 2.

(** Orientability: the signature is switching-trivial. *)
Definition orientable_map (M : emap) : Prop :=
  exists o : G -> bool,
    forall d : dart G, stwist M d = addb (o (sval d).1) (o (sval d).2).

(** General-surface embeddability in Euler genus ≤ k (orientable or not).
    WARNING (audit): this is NOT "embeds in the non-orientable surface N_k" — it
    minimizes over ALL schemes, so orientable schemes leak in (K7 has a torus
    scheme, giving [semb_in_genus 'K_7 2], yet crosscap(K7) = 3 — Ringel's
    exception — so K7 does NOT embed in the Klein bottle).  An embeds-in-N_k
    predicate needs the minimum over NON-orientable schemes plus the
    orientable→non-orientable interpolation subtleties; currently consumer-free. *)
Definition semb_in_genus (k : nat) : Prop :=
  exists M : emap, seuler_genus M <= k.

(** Every face boundary is a cycle (general-surface strong embedding).
    SCOPE CAVEAT (audit): on graphs with degree-1 vertices this is strictly
    WEAKER than "every face boundary is a cycle" — a pendant edge yields a
    2-flag face orbit with distinct sources (so the injectivity test passes)
    although its facial walk traverses one edge twice (K2's unique map satisfies
    [circular_emap], but K2 has no cycles).  A 2-flag orbit forces a
    rotation-fixed dart = a degree-1 source (probe: sface_no2orbit), so under a
    min-degree ≥ 2 hypothesis — e.g. the D6emb row's [k_connected G 2] — orbit
    length is ≥ 3 and the predicate is EXACTLY "boundary is a simple cycle".
    Unguarded standalone use on graphs with pendant vertices is unfaithful. *)
Definition circular_emap (M : emap) : Prop :=
  forall x : dart G * bool,
    {in porbit (sface_perm M) x &, injective (fun y : dart G * bool => (sval y.1).1)}.

(** Existence: any rotation system with the trivial (all-orientable) signature —
    so [emap] is inhabited for EVERY graph and the predicates are non-vacuous. *)
Definition emap_of (E : embedding G) : emap := @EMap E (fun _ => false) (fun _ => erefl).
Lemma orientable_emap_of (E : embedding G) : orientable_map (emap_of E).
Proof. by exists (fun _ => false). Qed.
Lemma emap_exists : inhabited emap.
Proof. exact: (inhabits (emap_of (embedding_of G))). Qed.

End Signed.

(** ** Non-vacuity of NON-orientability: the triangle with one twisted edge.
    Its twist sum around the 3-cycle is 1, which is switching-invariant, so no
    vertex 2-colouring trivializes the signature — the projective-plane triangle. *)
Section TwistedTriangle.

Definition K3 : sgraph := 'K_3.
Definition tt_v0 : K3 := @Ordinal 3 0 isT.
Definition tt_v1 : K3 := @Ordinal 3 1 isT.
Definition tt_v2 : K3 := @Ordinal 3 2 isT.

(** Twist exactly the {v0,v1} edge (both endpoints differ from v2). *)
Definition tt_twist (d : dart K3) : bool :=
  ((sval d).1 != tt_v2) && ((sval d).2 != tt_v2).

Lemma tt_twist_edge (d : dart K3) : tt_twist (edge_perm K3 d) = tt_twist d.
Proof. by rewrite edge_permE /tt_twist /= andbC. Qed.

Definition tt_d01 : dart K3 := exist _ (tt_v0, tt_v1) isT.
Definition tt_d02 : dart K3 := exist _ (tt_v0, tt_v2) isT.
Definition tt_d12 : dart K3 := exist _ (tt_v1, tt_v2) isT.

Definition twisted_triangle : emap K3 :=
  @EMap K3 (embedding_of K3) tt_twist tt_twist_edge.

Lemma twisted_triangle_nonorientable : ~ orientable_map twisted_triangle.
Proof.
case=> o H.
have H01 := H tt_d01. have H02 := H tt_d02. have H12 := H tt_d12.
move: H01 H02 H12; rewrite /= /tt_twist /=.
by case: (o tt_v0); case: (o tt_v1); case: (o tt_v2).
Qed.

End TwistedTriangle.
