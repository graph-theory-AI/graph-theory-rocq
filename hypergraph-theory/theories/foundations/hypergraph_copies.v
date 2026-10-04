(** * Hypergraph.foundations.hypergraph_copies -- monochromatic copies of a supplied hypergraph

    Library migration D4 (registry entry [monochromatic-copy]; report
    meta/migration_reports/monochromatic_copy.md; record meta/LIBRARY_MIGRATION_D4.md; public client
    theories/examples/monochromatic_copies.v).

    [hg_mono_copy E col]: for a pattern family [E : {set {set T}}] and a colouring
    [col : {set U} -> C] of ALL subsets of a finite host [U] by any palette [C], some colour [c]
    and some injection [f : T -> U] of the whole pattern carrier (isolated pattern vertices
    included) send every member [e] of [E] to a host set [f @: e] of colour [c].  No uniformity,
    rank, nonempty family or carrier, palette size or no-isolated premise; the map [f] is the only
    injectivity in play, [f @: e] itself needs none.

    For an [eqType] palette this is exactly the existing containment [hg_containsb] of the pattern
    in one colour class [[set e | col e == c]] ([hg_mono_copyP]).  The coloured view is kept
    because the corpus supplies the colour map, chooses the colour existentially and needs the
    witnesses as data (the forcing and Ramsey rows quantify over such maps).  It is not
    [GTBase.monochromatic.monochromatic_on] (constancy on one supplied set, no embedding) nor the
    Extremal graph copies (adjacency or pair colourings).

    Axiom-free: no Axiom/Parameter/Admitted. *)
From GTBase Require Import base.
From Hypergraph.foundations Require Import hypergraph.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Copies.
Variables (T U : finType) (C : Type).
Implicit Types (E F : {set {set T}}) (col : {set U} -> C).

Definition hg_mono_copy E col : Prop :=
  exists (c : C) (f : T -> U), injective f /\ forall e : {set T}, e \in E -> col (f @: e) = c.

(** The colouring supplies the colour of the empty family: a copy exists iff an injection does. *)
Lemma hg_mono_copy0 col : hg_mono_copy set0 col <-> exists f : T -> U, injective f.
Proof.
split=> [[c [f [fi _]]]|[f fi]]; first by exists f.
by exists (col set0), f; split=> // e; rewrite inE.
Qed.

(** The whole carrier is injected: no copy of a pattern with more vertices than the host, even
    without edges. *)
Lemma hg_mono_copy_card E col : hg_mono_copy E col -> #|T| <= #|U|.
Proof. by move=> [c [f [fi _]]]; exact: leq_card fi. Qed.

(** Subfamilies keep the same colour and injection. *)
Lemma hg_mono_copyS E F col : F \subset E -> hg_mono_copy E col -> hg_mono_copy F col.
Proof. by move=> /subsetP FE [c [f [fi H]]]; exists c, f; split=> // e /FE; exact: H. Qed.

(** A constant colouring and any injection give a copy. *)
Lemma hg_mono_copy_const E (c : C) (f : T -> U) : injective f -> hg_mono_copy E (fun _ => c).
Proof. by move=> fi; exists c, f. Qed.

End Copies.

(** Relabelling the palette keeps copies; a relabelling with a left inverse reflects them. *)
Lemma hg_mono_copy_map (T U : finType) (C D : Type) (g : C -> D) (E : {set {set T}})
    (col : {set U} -> C) :
  hg_mono_copy E col -> hg_mono_copy E (fun s => g (col s)).
Proof. by move=> [c [f [fi H]]]; exists (g c), f; split=> // e eE; rewrite H. Qed.

Lemma hg_mono_copy_mapK (T U : finType) (C D : Type) (g : C -> D) (h : D -> C)
    (E : {set {set T}}) (col : {set U} -> C) :
  cancel g h -> hg_mono_copy E (fun s => g (col s)) -> hg_mono_copy E col.
Proof.
move=> gK [d [f [fi H]]]; exists (h d), f; split=> // e eE.
by rewrite -(H e eE) gK.
Qed.

Section ColourClasses.
Variables (T U : finType) (C : eqType).

(** The colour-class bridge: a monochromatic copy is a copy, in the sense of [hg_containsb], of
    the pattern inside one colour class of the host subsets. *)
Lemma hg_mono_copyP (E : {set {set T}}) (col : {set U} -> C) :
  hg_mono_copy E col <-> exists c : C, hg_containsb E [set e | col e == c].
Proof.
split=> [[c [f [fi H]]]|[c /existsP[g /andP[/injectiveP gi /forall_inP H]]]].
  exists c; apply/existsP; exists [ffun x => f x]; apply/andP; split.
    by apply/injectiveP => x y; rewrite !ffunE; exact: fi.
  apply/forall_inP => e eE; rewrite inE.
  have -> : [set [ffun x => f x] x | x in e] = f @: e.
    by apply: eq_imset => x; rewrite ffunE.
  by rewrite H ?eqxx.
exists c, g; split=> // e eE.
by move: (H e eE); rewrite inE => /eqP.
Qed.

End ColourClasses.
