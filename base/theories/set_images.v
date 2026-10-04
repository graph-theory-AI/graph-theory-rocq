(** * GTBase.set_images -- the image of a supplied finite set is MathComp's [imset]

    Library migration D3 (registry entry [image-edge]; report meta/migration_reports/image_edge.md;
    record meta/LIBRARY_MIGRATION_D3.md; public client theories/examples/set_images.v).

    The image of [A : {set aT}] under any [f : aT -> rT] between finite types is MathComp's
    [f @: A] ([mathcomp.boot.finset.imset], the HB-locked constant [imset.body]).  No injectivity,
    nonempty domain/set or codomain condition is part of it.  Because [imset] is locked, its
    bounded-existential presentation is a proved set equality ([imset_existsE]), not a conversion.
    Everything else is MathComp's own API, reused as it is: [imsetP], [imset0], [imset_set1],
    [imsetU], [imset_comp], [imset_id], [leq_imset_card], and [card_imset], which keeps its
    injectivity premise.

    Axiom-free: no Axiom/Parameter/Admitted. *)
From mathcomp Require Import all_boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** The bounded-existential presentation used by the corpus: [y] is in the image of [A] exactly
    when some [x] in [A] is sent to [y]. *)
Lemma imset_existsE (aT rT : finType) (f : aT -> rT) (A : {set aT}) :
  [set y | [exists x, (x \in A) && (y == f x)]] = f @: A.
Proof.
apply/setP => y; rewrite inE.
apply/existsP/imsetP => [[x /andP[xA /eqP->]]|[x xA ->]]; first by exists x.
by exists x; rewrite xA eqxx.
Qed.
