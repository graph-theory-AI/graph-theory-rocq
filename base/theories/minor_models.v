(** * Supplied finite branch-set minor models

    The canonical predicate is upstream [minor_rmap], already exposed by base:
    for host G, pattern H and the SAME supplied map H -> {set G}, each branch
    is nonempty and connected, distinct branches are disjoint, and every H-edge
    has a G-edge between its branches. Extra host edges, unused host vertices
    and an empty pattern are allowed. No inducedness or global nonemptiness
    condition is added. The lemmas below only change the presentation of these
    four clauses; they do not introduce another canonical minor predicate.

    Infinite Prop-set models, internal- versus ambient-radius shallow models,
    subdivision support, and odd/fat/fractional/multigraph minors have separate
    contracts. This module has no conjecture import or base re-export cycle. *)
From GTBase Require Import base.
From GraphTheory Require Import minor.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma minor_rmap_nestedE (G H : sgraph) (branch : H -> {set G}) :
  minor_rmap branch <->
  (forall h : H, branch h != set0) /\
  (forall h : H, connected (branch h)) /\
  (forall h1 h2 : H, h1 != h2 -> branch h1 :&: branch h2 = set0) /\
  (forall h1 h2 : H, h1 -- h2 ->
    exists x y : G, [/\ x \in branch h1, y \in branch h2 & x -- y]).
Proof.
split.
- move=> [ne co dj ed]; split=> //; split=> //; split.
  + by move=> x y xy; exact: disjoint_setI0 (dj x y xy).
  + by move=> x y /ed/neighborP.
- move=> [ne [co [dj ed]]]; split=> //.
  + by move=> x y xy; rewrite -setI_eq0 (dj x y xy) eqxx.
  + by move=> x y xy; apply/neighborP; exact: ed x y xy.
Qed.

Lemma minor_rmap_pairE (G H : sgraph) (branch : H -> {set G}) :
  minor_rmap branch <->
  [/\ (forall h : H, branch h != set0),
      (forall h : H, connected (branch h)),
      (forall h1 h2 : H, h1 != h2 -> [disjoint branch h1 & branch h2])
    & (forall h1 h2 : H, h1 -- h2 ->
         exists p : G * G, [/\ p.1 \in branch h1, p.2 \in branch h2 & p.1 -- p.2])].
Proof.
split=> -[ne co dj ed]; split=> // x y xy.
- by have /neighborP [a [b [ax byb ab]]] := ed x y xy; exists (a,b).
- by have [[a b] [ax byb ab]] := ed x y xy; apply/neighborP; exists a, b.
Qed.

Lemma minor_rmap_existsE (G H : sgraph) :
  (exists branch : H -> {set G}, minor_rmap branch) <-> minor G H.
Proof.
split=> [[branch model]|m]; first exact: minor_of_rmap model.
exact: minorRE m.
Qed.

Lemma minor_rmap_singletons (G : sgraph) :
  minor_rmap (fun x : G => [set x]).
Proof.
split.
- by move=> x; apply/set0Pn; exists x; rewrite inE.
- exact: connected1.
- by move=> x y xy; rewrite disjoints1 !inE.
- move=> x y xy; apply/neighborP; exists x, y.
  by split; rewrite ?inE ?eqxx.
Qed.

Lemma minor_rmap_empty_pattern (G : sgraph) (branch : 'K_0 -> {set G}) :
  minor_rmap branch.
Proof. by split; move=> []. Qed.

Lemma minor_rmap_host_nonempty (G H : sgraph) (branch : H -> {set G}) (h : H) :
  minor_rmap branch -> 0 < #|G|.
Proof.
move=> [ne _ _ _]; have /set0Pn [x _] := ne h.
by apply/card_gt0P; exists x; rewrite inE.
Qed.

Lemma not_minor_rmap_empty_host (H : sgraph) (h : H) (branch : H -> {set 'K_0}) :
  ~ minor_rmap branch.
Proof. by move=> /(@minor_rmap_host_nonempty _ _ _ h); rewrite card_ord. Qed.

Lemma minor_rmap_card (G H : sgraph) (branch : H -> {set G}) :
  minor_rmap branch -> #|H| <= #|G|.
Proof. by move/minor_of_rmap/minor_card. Qed.

Lemma minor_rmap_compose (G H K : sgraph) (f : H -> {set G}) (g : K -> {set H}) :
  minor_rmap f -> minor_rmap g ->
  minor_rmap (fun x => \bigcup_(y in g x) f y).
Proof. exact: minor_rmap_comp. Qed.
