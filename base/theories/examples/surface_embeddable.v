(** * GTBase.examples.surface_embeddable — public-only client of GTBase.surface's [surface_embeddable]

    Compiles against GTBase.base (which re-exports GTBase.surface) alone, with no conjecture or migration module.
    [surface_embeddable surface G] asks for a finite rotation system [E] of [G] whose encoded orientable-genus value
    [surface_euler_genus E = (2 + edges - vertices - faces) %/ 2], in truncated [nat] arithmetic, is at most [surface]:
    a BOUND, so it is monotone in [surface]; [K_1] and every edgeless graph with a vertex reach the bound 0.  The
    formula hard-codes the connected-map Euler relation: the EMPTY graph reads 1 (so it misses the bound 0 but meets
    the bound 1), and on a disconnected graph the formula can understate the genus, which is why the corpus rows that
    need the classical reading carry their own [connected [set: G]] guard.  A wrapper taking an extra, unused boundary
    argument (as X164's does) is the same predicate for every boundary value. *)

From mathcomp Require Import all_boot fingroup perm.
From GTBase Require Import base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** A bound, not an exact genus. *)
Lemma example_monotone (s s' : nat) (G : sgraph) :
  s <= s' -> surface_embeddable s G -> surface_embeddable s' G.
Proof. by move=> le_s [E gE]; exists E; exact: leq_trans le_s. Qed.

(** [K_1], and any edgeless graph with at least one vertex, meet the bound 0. *)
Example example_K1 : surface_embeddable 0 'K_1.
Proof. exact: surface_embeddable_K1. Qed.

Lemma example_edgeless (G : sgraph) (s : nat) :
  (forall d : surface_dart G, False) -> 0 < #|G| -> surface_embeddable s G.
Proof. by move=> nodart cG; apply: example_monotone (leq0n s) _; exact: surface_embeddable_edgeless. Qed.

(** The empty graph: no dart, no face orbit, no vertex, so the formula reads [(2 + 0 - 0 - 0) %/ 2 = 1]. *)
Lemma example_empty_misses_bound0 : ~ surface_embeddable 0 'K_0.
Proof.
have nodart (d : surface_dart 'K_0) : False by case: d => -[x y] _; case: x.
case=> E; rewrite /surface_euler_genus /surface_embedding_edges /surface_embedding_vertices.
rewrite /surface_embedding_faces card_ord.
have -> : #|{: surface_dart 'K_0}| = 0 by apply: eq_card0 => d; case: (nodart d).
have -> : #|porbits (surface_face_perm E)| = 0.
  by apply: eq_card0 => X; apply/negP => /imsetP [d _ _]; case: (nodart d).
by [].
Qed.

(** ... while the identity rotation system on its empty dart type witnesses the bound 1. *)
Lemma example_empty_meets_bound1 : surface_embeddable 1 'K_0.
Proof.
have nodart (d : surface_dart 'K_0) : False by case: d => -[x y] _; case: x.
have Hsrc (d : surface_dart 'K_0) : (sval ((1%g : {perm surface_dart 'K_0}) d)).1 = (sval d).1.
  by case: (nodart d).
have Hvtx (d : surface_dart 'K_0) :
    porbit (1%g : {perm surface_dart 'K_0}) d = [set d' | (sval d').1 == (sval d).1].
  by case: (nodart d).
exists (@SurfaceEmbedding 'K_0 1%g Hsrc Hvtx).
rewrite /surface_euler_genus /surface_embedding_edges /surface_embedding_vertices.
rewrite /surface_embedding_faces card_ord.
have -> : #|{: surface_dart 'K_0}| = 0 by apply: eq_card0 => d; case: (nodart d).
have -> : #|porbits (surface_face_perm (@SurfaceEmbedding 'K_0 1%g Hsrc Hvtx))| = 0.
  by apply: eq_card0 => X; apply/negP => /imsetP [d _ _]; case: (nodart d).
by [].
Qed.

(** An extra boundary argument that the predicate ignores changes nothing, whatever its value. *)
Definition boundary_adapter (surface boundary : nat) (G : sgraph) : Prop := surface_embeddable surface G.

Lemma example_boundary_ignored (surface b b' : nat) (G : sgraph) :
  boundary_adapter surface b G <-> boundary_adapter surface b' G.
Proof. exact: iff_refl. Qed.
