(** * Hypergraph.foundations.hypergraph_forcing -- forcing a monochromatic copy under every colouring

    Library migration D5 (registry entry [forces-mono]; report meta/migration_reports/forces_mono.md;
    record meta/LIBRARY_MIGRATION_D5.md; public client theories/examples/forcing.v).

    [hg_forces_mono E U C]: EVERY colouring [col : {set U} -> C] of all subsets of the finite host [U]
    by the palette [C : Type] admits a monochromatic copy [hg_mono_copy E col] (D4) of the pattern
    [E : {set {set T}}].  The host [U] and the palette [C] are explicit arguments.  No inhabited
    palette, positive palette size, uniformity, nonempty family or no-isolated condition: with an
    empty palette there is no colouring at all (the host has the subset [set0]), so forcing holds
    vacuously.  Statements needing a colour state that witness explicitly ([hg_forces_mono_card]).
    Ramsey numbers (forcing at [R] and minimality against every forcing host) are not defined here.

    Axiom-free: no Axiom/Parameter/Admitted. *)
From GTBase Require Import base.
From Hypergraph.foundations Require Import hypergraph hypergraph_copies.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition hg_forces_mono (T : finType) (E : {set {set T}}) (U : finType) (C : Type) : Prop :=
  forall col : {set U} -> C, hg_mono_copy E col.

Section Forcing.
Variables (T U : finType).
Implicit Types (E F : {set {set T}}).

(** Elimination: a forcing host gives a copy for each supplied colouring. *)
Lemma hg_forces_monoE E (C : Type) (col : {set U} -> C) : hg_forces_mono E U C -> hg_mono_copy E col.
Proof. by move=> fE; exact: fE. Qed.

(** Subfamilies of a forced pattern are forced. *)
Lemma hg_forces_monoS E F (C : Type) : F \subset E -> hg_forces_mono E U C -> hg_forces_mono F U C.
Proof. by move=> FE fE col; exact: hg_mono_copyS FE (fE col). Qed.

(** An empty palette admits no colouring of the host subsets, so forcing holds vacuously. *)
Lemma hg_forces_mono_empty_palette E (C : Type) : (C -> False) -> hg_forces_mono E U C.
Proof. by move=> C0 col; case: (C0 (col set0)). Qed.

(** With a colour [c0] at hand, a forced pattern injects into the host. *)
Lemma hg_forces_mono_card E (C : Type) (c0 : C) : hg_forces_mono E U C -> #|T| <= #|U|.
Proof. by move=> fE; exact: hg_mono_copy_card (fE (fun _ => c0)). Qed.

(** A singleton palette (an explicit colour [c0] equal to every colour) forces exactly when the
    whole pattern carrier injects into the host. *)
Lemma hg_forces_mono_singleton E (C : Type) (c0 : C) :
  (forall c : C, c = c0) -> hg_forces_mono E U C <-> exists f : T -> U, injective f.
Proof.
move=> one; split=> [/(_ (fun _ => c0)) [c [f [fi _]]]|[f fi] col]; first by exists f.
by exists c0, f; split=> // e _; exact: one.
Qed.

(** Transport along palette maps [g : C -> D] and [h : D -> C] with [g (h d) = d]: forcing with
    palette [C] gives forcing with palette [D]. *)
Lemma hg_forces_mono_transport E (C D : Type) (g : C -> D) (h : D -> C) :
  cancel h g -> hg_forces_mono E U C -> hg_forces_mono E U D.
Proof.
move=> hK fE col; have [c [f [fi H]]] := fE (fun s => h (col s)).
by exists (g c), f; split=> // e eE; move: (H e eE) => /= <-; rewrite hK.
Qed.

End Forcing.
