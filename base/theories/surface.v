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

(** Count graph vertices, rather than only vertices incident with a dart.  The
    distinction is essential for the connected one-vertex graph. *)
Definition surface_embedding_vertices (E : surface_embedding) : nat :=
  #|G|.

Definition surface_embedding_edges : nat := #|{: surface_dart}| %/ 2.

(** A dartless connected graph is [K_1] and its cellular embedding has one
    face.  Otherwise the face permutation gives the usual face cycles. *)
Definition surface_embedding_faces (E : surface_embedding) : nat :=
  if #|{: surface_dart}| == 0 then 1
  else #|porbits (surface_face_perm E)|.

(** Orientable genus of a connected cellular rotation system. *)
Definition surface_orientable_genus (E : surface_embedding) : nat :=
  (2 + surface_embedding_edges - surface_embedding_vertices E -
     surface_embedding_faces E) %/ 2.

(** Euler genus is twice the orientable genus. *)
Definition surface_euler_genus (E : surface_embedding) : nat :=
  2 * surface_orientable_genus E.

(** This primitive deliberately models connected graphs on orientable closed
    surfaces.  A model for disconnected or non-orientable embeddings needs
    additional component/surface data and must not reuse this predicate. *)
Definition surface_embeds_in_orientable_genus (g : nat) : Prop :=
  connected [set: G] /\
  exists E : surface_embedding, surface_orientable_genus E <= g.

(** Euler-genus form of the same connected, orientable-only model. *)
Definition surface_embeds_in_orientable_euler_genus (g : nat) : Prop :=
  connected [set: G] /\
  exists E : surface_embedding, surface_euler_genus E <= g.

(** Compatibility alias.  Despite its older unqualified name, this predicate
    does not represent embeddings in non-orientable surfaces. *)
Definition surface_embeds_in_euler_genus (g : nat) : Prop :=
  surface_embeds_in_orientable_euler_genus g.

Definition surface_embeds_in_fixed_surface (orientable_genus : nat) : Prop :=
  surface_embeds_in_orientable_genus orientable_genus.

End SurfaceEmbedding.

(** Backwards-compatible name: the numeric parameter is an orientable-genus
    bound, and the graph is required to be connected. *)
Definition surface_embeddable (orientable_genus : nat) (G : sgraph) : Prop :=
  surface_embeds_in_fixed_surface G orientable_genus.

(** Grounding check for the dartless connected case. *)
Lemma surface_dart_K1_false (d : surface_dart 'K_1) : False.
Proof.
case: d => [[x y] xy] /=.
by case: x xy => [[|x] hx] //; case: y => [[|y] hy].
Qed.

Lemma surface_dart_K1_card : #|{: surface_dart 'K_1}| = 0.
Proof.
rewrite card_sig; apply: eq_card0 => [[x y]] /=.
by case: x => [[|x] hx] //; case: y => [[|y] hy].
Qed.

Definition surface_embedding_K1 : surface_embedding 'K_1.
Proof.
refine (@SurfaceEmbedding 'K_1 (perm.perm_one _) _ _).
- by move=> d; case: (surface_dart_K1_false d).
- by move=> d; case: (surface_dart_K1_false d).
Defined.

Lemma surface_K1_connected : connected [set: 'K_1].
Proof.
apply: connectedTI => x y.
have -> : y = x by
  apply/val_inj; case: x => [[|x] hx]; case: y => [[|y] hy].
exact: connect0.
Qed.

Lemma surface_embeddable_K1 : surface_embeddable 0 'K_1.
Proof.
split; first exact: surface_K1_connected.
exists surface_embedding_K1.
rewrite /surface_orientable_genus /surface_embedding_edges
        /surface_embedding_vertices /surface_embedding_faces
        surface_dart_K1_card card_ord /=.
by [].
Qed.

(** Legacy lightweight placeholder: [B] is only a bounded marked vertex set;
    this definition does not model topological boundary components. *)
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
