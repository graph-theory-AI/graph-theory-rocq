(** * GTBase.surface -- shared finite surface and clustered-colouring vocabulary *)

From mathcomp Require Import all_boot.
From mathcomp Require Import fingroup perm.
From GraphTheory Require Import digraph sgraph.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section SurfaceEmbedding.
Variable G : sgraph.

Definition surface_dart : Type := {p : G * G | p.1 -- p.2}.

Lemma surface_rev_dart_proof (d : surface_dart) :
  (sval d).2 -- (sval d).1.
Proof. by rewrite sg_sym; exact: (svalP d). Qed.

Definition surface_rev_dart (d : surface_dart) : surface_dart :=
  exist _ ((sval d).2, (sval d).1) (surface_rev_dart_proof d).

Lemma surface_rev_dartK : involutive surface_rev_dart.
Proof. by move=> d; apply/val_inj; case: d => [[x y] p]. Qed.

Definition surface_edge_perm : {perm surface_dart} :=
  perm (inv_inj surface_rev_dartK).

Record surface_embedding := SurfaceEmbedding {
  surface_erot : {perm surface_dart};
  surface_erot_src :
    forall d : surface_dart, (sval (surface_erot d)).1 = (sval d).1;
  surface_erot_vertex :
    forall d : surface_dart,
      porbit surface_erot d = [set d' | (sval d').1 == (sval d).1]
}.

Definition surface_face_perm (E : surface_embedding) : {perm surface_dart} :=
  (surface_erot E * surface_edge_perm)%g.

(** The vertex count of the embedded map.  TEXTBOOK CONVENTION (base fix
    2026-09-23): [V] counts EVERY vertex of [G], isolated ones included.

    It used to be [#|porbits (surface_erot E)|], which by [surface_erot_vertex]
    counts only the vertices that CARRY A DART (see
    [surface_embedding_vertices_orbits] below); isolated vertices were therefore
    invisible and [surface_euler_genus] OVERSTATED the genus of every graph with
    an isolated vertex -- an edgeless graph came out with V = E = F = 0 and
    genus 1, so [~ surface_embeddable 0 'K_1] was provable although [K_1] is
    planar.  The parameter [E] is kept so that the call sites are unchanged. *)
Definition surface_embedding_vertices (E : surface_embedding) : nat := #|G|.

Definition surface_embedding_edges : nat := #|{: surface_dart}| %/ 2.

Definition surface_embedding_faces (E : surface_embedding) : nat :=
  #|porbits (surface_face_perm E)|.

(** Orientable Euler genus from a finite rotation system, [(2 + E - V - F) %/ 2]
    over truncating [nat] arithmetic.  V counts every vertex including isolated
    ones (base fix 2026-09-23), E = [#|dart| %/ 2] and F is the number of face
    orbits.  Consumers should keep the usual connected-graph guard when they
    need the classical connected surface reading: the formula hard-codes the
    CONNECTED-map relation [2 - 2g = V - E + F], so on a [c]-component graph it
    computes [max(0, sum_i g_i + 1 - c)] and UNDERSTATES the (additive) genus by
    [c - 1].  Residual wrinkle of the truncating arithmetic: the EMPTY graph
    still evaluates to [(2 - 0 - 0) %/ 2 = 1]; every graph with at least one
    vertex is now free of the isolated-vertex artefact (see
    [surface_embeddable_edgeless]). *)
Definition surface_euler_genus (E : surface_embedding) : nat :=
  (2 + surface_embedding_edges - surface_embedding_vertices E -
     surface_embedding_faces E) %/ 2.

Definition surface_embeds_in_euler_genus (g : nat) : Prop :=
  exists E : surface_embedding, surface_euler_genus E <= g.

Definition surface_embeds_in_fixed_surface (surface : nat) : Prop :=
  surface_embeds_in_euler_genus surface.

(** ** Sanity lemmas for the repaired vertex count *)

(** What the OLD count was: by [surface_erot_vertex] the rotation orbits are
    exactly the dart sets of the vertices that carry a dart, so
    [#|porbits (surface_erot E)|] is the number of NON-ISOLATED vertices.  This
    is the lemma that pins down the defect repaired above; it also shows the old
    and the new count agree as soon as every vertex carries a dart. *)
Lemma surface_embedding_vertices_orbits (E : surface_embedding) :
  #|porbits (surface_erot E)| =
  #|[set v : G | [exists d : surface_dart, (sval d).1 == v]]|.
Proof.
pose A := [set v : G | [exists d : surface_dart, (sval d).1 == v]].
pose phi (v : G) := [set d : surface_dart | (sval d).1 == v].
have AE : forall v : G, (v \in A) = [exists d : surface_dart, (sval d).1 == v].
  by move=> v; rewrite /A inE.
have phiE : forall (v : G) (d : surface_dart), (d \in phi v) = ((sval d).1 == v).
  by move=> v d; rewrite /phi inE.
have eqim : porbits (surface_erot E) = [set phi v | v in A].
  apply/setP => X; apply/idP/idP.
    case/imsetP => d _ ->; apply/imsetP; exists (sval d).1.
      by rewrite AE; apply/existsP; exists d.
    by rewrite surface_erot_vertex.
  case/imsetP => v; rewrite AE => /existsP[d /eqP dv] ->.
  by apply/imsetP; exists d; rewrite ?inE // surface_erot_vertex dv.
have phi_inj : {in A &, injective phi}.
  move=> v w; rewrite AE => /existsP[d /eqP dv] _ eqphi.
  have dw : d \in phi w by rewrite -eqphi phiE dv.
  by move: dw; rewrite phiE dv => /eqP.
by rewrite eqim card_in_imset.
Qed.

(** An EDGELESS graph with at least one vertex is PLANAR under the repaired
    count: the identity is a rotation system on the empty dart type, and the
    Euler count returns [(2 - #|G|) %/ 2 = 0].  With the old count it returned
    [1] for every edgeless graph. *)
Lemma surface_edgeless_genus0 :
  (forall d : surface_dart, False) -> 0 < #|G| ->
  exists E : surface_embedding, surface_euler_genus E = 0.
Proof.
move=> nodart cG.
have Hsrc : forall d : surface_dart,
    (sval ((1%g : {perm surface_dart}) d)).1 = (sval d).1.
  by move=> d; case: (nodart d).
have Hvtx : forall d : surface_dart,
    porbit (1%g : {perm surface_dart}) d = [set d' | (sval d').1 == (sval d).1].
  by move=> d; case: (nodart d).
have c0 : #|{: surface_dart}| = 0 by apply: eq_card0 => d; case: (nodart d).
exists (@SurfaceEmbedding 1%g Hsrc Hvtx).
rewrite /surface_euler_genus /surface_embedding_edges /surface_embedding_vertices.
rewrite c0 div0n addn0; apply: divn_small.
by apply: leq_ltn_trans (leq_subr _ _) _; rewrite ltn_subrL cG.
Qed.

End SurfaceEmbedding.

Definition surface_embeddable (surface : nat) (G : sgraph) : Prop :=
  surface_embeds_in_fixed_surface G surface.

Definition surface_embeddable_with_boundary
    (surface boundary : nat) (G : sgraph) : Prop :=
  surface_embeddable surface G /\
  exists B : {set G}, #|B| <= boundary.

Definition same_colour_on (G : sgraph) (k : nat)
    (col : G -> 'I_k) (S : {set G}) : Prop :=
  forall x y : G, x \in S -> y \in S -> col x = col y.

(** [clustered_colouring G k c] says every connected monochromatic vertex set
    has size at most [c], equivalently every monochromatic component has size at
    most [c]. *)
Definition clustered_colouring (G : sgraph) (k c : nat) : Prop :=
  exists col : G -> 'I_k,
    forall S : {set G},
      connected S -> same_colour_on col S -> #|S| <= c.

Definition clustered_chromatic_at_most (G : sgraph) (k : nat) : Prop :=
  exists c : nat, clustered_colouring G k c.

(** ** Canaries for the vertex-count convention (base fix 2026-09-23)

    These pin the repaired reading of [surface_embedding_vertices] down to
    concrete graphs: with the old orbit count both statements below were FALSE
    (an edgeless graph evaluated to genus 1), so they also serve as the
    mutation-testing canary for the definition. *)

Lemma surface_embeddable_edgeless (G : sgraph) :
  (forall d : surface_dart G, False) -> 0 < #|G| -> surface_embeddable 0 G.
Proof.
move=> nodart cG; have [E gE] := surface_edgeless_genus0 nodart cG.
by exists E; rewrite gE.
Qed.

Lemma surface_no_dart_K1 (d : surface_dart 'K_1) : False.
Proof. by case: d => [[x y]] /=; rewrite /edge_rel /= (ord1 x) (ord1 y) eqxx. Qed.

(** [K_1] is planar.  (With the old vertex count this was refutable.) *)
Lemma surface_embeddable_K1 : surface_embeddable 0 'K_1.
Proof.
by apply: surface_embeddable_edgeless surface_no_dart_K1 _; rewrite card_ord.
Qed.
