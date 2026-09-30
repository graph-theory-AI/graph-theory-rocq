(** * Digraph.conjectures.implications_X52 — wave X52 implication edges

      - e019 : opg:oriented_trees_in_n_chromatic_digraphs (Burr, P9.v)
               ==> arxiv:1610.00876#03 (the chromatic Mader bound, X52.v).

    VERIFIED in wave E4.  Two things had to happen first.

    1. The X52 body was GUARD-REPAIRED (see the row's Notes in X52.v): without
       [0 < #|D|] the target is refutable at [k = 1] (the one-vertex oriented tree
       makes the threshold [2 * 1 - 2 = 0], so the EMPTY digraph would have to
       contain a subdivision of a one-vertex digraph), while Burr's statement,
       guarded by [2 <= k], says nothing there.  With the guard, [k = 1] becomes a
       theorem ([grounding_X52.v: x52_k1_holds]).

    2. The two files use DIFFERENT tree vocabularies, and the edge needs the
       harder direction between them:
         [X2.oriented_tree T] = nonempty, asymmetric, underlying graph a connected
           forest  (the target's hypothesis),
         [P9.oriented_tree T] = [tree_digraph T] = weakly connected with exactly
           [#V - 1] arcs  (the source's hypothesis).
       The arc count is the classical "a tree on n vertices has n-1 edges", which
       coq-graph-theory does not provide.  It is proved here as [tree_nb_arcs] by
       an explicit BIJECTION between the arcs and the non-root vertices: pick a
       root [r]; every arc is sent to the end that its other end separates from
       [r] ([foundations/subdivision.v: fsep]).  Injectivity uses that in a forest
       the separating neighbour of a vertex is the second vertex of its (unique)
       path to the root, and that two arcs between the same pair would be a digon;
       surjectivity uses the first step of the path from a non-root vertex to the
       root.

    The rest of the corpus argument is the structural half proved here already:
    a subdigraph copy of [T] is a subdivision of [T] with all replacement paths of
    length one ([subdig_contains_subdivision]). *)

From HB Require Import structures.
From mathcomp Require Import all_boot.
From Digraph Require Import prelude interop_graph_theory digraph oriented tournament.
From Digraph Require Import dipath subdivision.
From Digraph.conjectures Require Import chi_bounded X2 X52 P9 grounding_X52.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Endpoint resolution check *)
Check oriented_trees_in_n_chromatic_digraphs_statement : Prop.
Check oriented_tree_mader_chi_linear_bound_statement : Prop.

(** A (non-induced) subdigraph copy of [F] in [D] IS a subdivision of [F]: take
    the copy as the branch map and, for every arc [u --> v] of [F], the
    one-vertex path [[:: branch v]].  Its internal vertices form the empty set,
    so all the disjointness clauses hold trivially. *)
Lemma subdig_contains_subdivision (F D : diGraphType) :
  (forall u : F, ~~ (u --> u)) ->
  contains_subdig D F -> contains_subdivision F D.
Proof.
move=> Firr [phi [phi_inj phi_arc]]; exists phi; split=> //.
exists (fun u v : F => [:: phi v]).
have hempty : forall u v : F, x2_path_internal phi u v [:: phi v] =i pred0.
  move=> u v z; rewrite /x2_path_internal /x2_path_vertices !inE /=.
  by case: (z == phi u); case: (z == phi v).
split.
- move=> u v huv.
  have uv : u != v.
    by apply/eqP => e; move: huv; rewrite e (negbTE (Firr v)).
  have puv : phi u != phi v by apply: contra uv => /eqP/phi_inj ->.
  split=> //.
  + rewrite /dipath; apply/andP; split; first by rewrite /= (phi_arc _ _ huv).
    by rewrite /= mem_seq1 andbT.
  + by apply: eq_disjoint0; exact: hempty.
- by move=> u v x y _ _ _; apply: eq_disjoint0; exact: hempty.
Qed.

(** The underlying simple graph has the same carrier as the digraph, so vertex
    equality and the number of vertices are the same up to conversion. *)
Lemma x52_eqUG (F : orientedDigraph) (u v : F) :
  ((u : chi_bounded.underlying F) == (v : chi_bounded.underlying F)) = (u == v).
Proof. by []. Qed.

Lemma x52_cardUG (F : orientedDigraph) : #|chi_bounded.underlying F| = #|F|.
Proof. by []. Qed.

Section TreeArcCount.
Variable F : orientedDigraph.
Variable hor : chi_bounded.oriented_dg F.
Variable hforest : is_forest [set: chi_bounded.underlying F].
Variable hconn : connected [set: chi_bounded.underlying F].
Variable r : chi_bounded.underlying F.

Lemma x52_arc_irr (u : F) : ~~ (u --> u).
Proof. by apply/negP => h; move: (hor h); rewrite h. Qed.

Lemma x52_arc_edge (u v : F) : u --> v ->
  (u : chi_bounded.underlying F) -- (v : chi_bounded.underlying F).
Proof.
move=> huv; have hne : u != v.
  by apply/negP => /eqP e; move: huv; rewrite e (negbTE (x52_arc_irr v)).
by rewrite /edge_rel/= /chi_bounded.urel hne huv.
Qed.

Lemma x52_arc_neq (u v : F) : u --> v ->
  (u : chi_bounded.underlying F) != (v : chi_bounded.underlying F).
Proof.
move=> huv; apply/negP => /eqP e.
by move: (x52_arc_edge huv); rewrite e sg_irrefl.
Qed.

(** The arc-to-vertex map: send an arc to the end that the other end separates
    from the root -- the end that is further from the root. *)
Definition tphi (p : F * F) : F := if fsep r p.1 p.2 then p.2 else p.1.

Lemma tphi_neq_r (p : F * F) : p.1 --> p.2 ->
  (tphi p : chi_bounded.underlying F) != r.
Proof.
case: p => u v /= huv; rewrite /tphi /=.
case: ifP => hsep; first exact: fsep_neq hsep.
have hne := x52_arc_neq huv.
apply/negP => /eqP eu; rewrite eu in hsep hne.
have hvr : (v : chi_bounded.underlying F) != r by rewrite eq_sym hne.
by move: (fsep_from_root hvr); rewrite hsep.
Qed.

Lemma tphi_inj : {in [set p : F * F | p.1 --> p.2] &, injective tphi}.
Proof.
move=> [u v] [x y]; rewrite !inE /= => huv hxy.
rewrite /tphi /=.
have huvE := x52_arc_edge huv.
have hxyE := x52_arc_edge hxy.
case: ifP => h1; case: ifP => h2 e.
- have hvy : v = y := e.
  have hux : u = x.
    have [s [hp hu hl]] := tree_upath hconn r v.
    have e1 := fsep_head hforest huvE h1 hp hu hl.
    have hxv : (x : chi_bounded.underlying F) -- (v : chi_bounded.underlying F)
      by rewrite hvy hxyE.
    have h2' : fsep r x v by rewrite hvy h2.
    have e2 := fsep_head hforest hxv h2' hp hu hl.
    by rewrite -e1 -e2.
  by rewrite hux hvy.
- exfalso.
  have [p1 [hp hu hl]] := not_fsep_upath hxyE (negbT h2).
  have hpv : path (--) (v : (chi_bounded.underlying F)) (y :: p1) by rewrite e; exact: hp.
  have huv' : uniq ((v : (chi_bounded.underlying F)) :: y :: p1) by rewrite e; exact: hu.
  have hlv : last (v : (chi_bounded.underlying F)) (y :: p1) = r by rewrite e; exact: hl.
  have e1 := fsep_head hforest huvE h1 hpv huv' hlv.
  move: e1; rewrite /= => e1'.
  by move: (hor huv); rewrite e -e1' hxy.
- exfalso.
  have [p1 [hp hu hl]] := not_fsep_upath huvE (negbT h1).
  have hpv : path (--) (y : (chi_bounded.underlying F)) (v :: p1) by rewrite -e; exact: hp.
  have huv' : uniq ((y : (chi_bounded.underlying F)) :: v :: p1) by rewrite -e; exact: hu.
  have hlv : last (y : (chi_bounded.underlying F)) (v :: p1) = r by rewrite -e; exact: hl.
  have e1 := fsep_head hforest hxyE h2 hpv huv' hlv.
  move: e1; rewrite /= => e1'.
  by move: (hor hxy); rewrite -e -e1' huv.
- have hux : u = x := e.
  have hvy : v = y.
    have [p1 [hp1 hu1 hl1]] := not_fsep_upath huvE (negbT h1).
    have [p2 [hp2 hu2 hl2]] := not_fsep_upath hxyE (negbT h2).
    have hp2' : path (--) (u : (chi_bounded.underlying F)) (y :: p2) by rewrite hux; exact: hp2.
    have hu2' : uniq ((u : (chi_bounded.underlying F)) :: y :: p2) by rewrite hux; exact: hu2.
    have hl2' : last (u : (chi_bounded.underlying F)) (y :: p2) = r by rewrite hux; exact: hl2.
    by have := forest_upath_eq hforest hp1 hu1 hl1 hp2' hu2' hl2'; case.
  by rewrite hux hvy.
Qed.

Lemma tphi_image : tphi @: [set p : F * F | p.1 --> p.2] = [set~ r].
Proof.
apply/setP => w; apply/idP/idP.
- case/imsetP => p; rewrite inE => hp ew; rewrite !inE ew.
  exact: tphi_neq_r hp.
- rewrite !inE => hw.
  have [s [hp hu hl]] := tree_upath hconn r w.
  have hsnil : s != [::] by exact: upath_to_root_neq hl hw.
  case: s hp hu hl hsnil => [//|z t] hp hu hl _.
  have hwz : (w : chi_bounded.underlying F) -- z by move: hp => /= /andP[].
  have harc2 : (w --> z) || (z --> w).
    by move: hwz; rewrite /edge_rel/= /chi_bounded.urel => /andP[].
  have hpt : path (--) z t by move: hp => /= /andP[].
  have hlt : last z t = r by move: hl => /=.
  case/orP: harc2 => [hwz'|hzw'].
  + apply/imsetP; exists (w, z); first by rewrite inE /= hwz'.
    rewrite /tphi /=; case: ifP => // hsep.
    by move: (not_fsep_of_upath hpt hu hlt); rewrite hsep.
  + apply/imsetP; exists (z, w); first by rewrite inE /= hzw'.
    by rewrite /tphi /= (fsep_of_upath hforest hp hu hl (mem_head z t)).
Qed.

Lemma tree_nb_arcs : nb_arcs F = #|F|.-1.
Proof.
by rewrite /nb_arcs -(card_in_imset tphi_inj) tphi_image cardsC1 x52_cardUG.
Qed.

End TreeArcCount.

(** ** The two tree vocabularies agree *)

Lemma x52_weakly_connected (F : orientedDigraph) :
  connected [set: chi_bounded.underlying F] -> weakly_connected F.
Proof.
move=> hconn; apply/forallP => u; apply/forallP => v.
have := connectedTE hconn u v; case/connectP => p hp hl.
apply/connectP; exists p; last exact: hl.
apply: (sub_path (e := @chi_bounded.urel F)) hp => x y.
by rewrite /chi_bounded.urel => /andP[].
Qed.

(** [X2.oriented_tree] (underlying graph a connected forest) implies
    [P9.oriented_tree] (weakly connected with [#V - 1] arcs): the arc count is
    the tree edge count, proved by [tree_nb_arcs]. *)
Lemma x52_oriented_tree_tree_digraph (F : orientedDigraph) :
  X2.oriented_tree F -> P9.oriented_tree F.
Proof.
move=> [hne hor hforest hconn]; rewrite /P9.oriented_tree /tree_digraph.
apply/andP; split; first exact: x52_weakly_connected hconn.
move/card_gt0P: hne => [r _].
by rewrite (tree_nb_arcs hor hforest hconn r) subn1.
Qed.

(** ** e019: Burr's conjecture implies the chromatic Mader bound *)

(*@EDGE from=oriented_trees_in_n_chromatic_digraphs_statement to=oriented_tree_mader_chi_linear_bound_statement kind=implies status=verified proof=oriented_trees_in_n_chromatic_digraphs_implies_oriented_tree_mader_chi_linear_bound cite="gc:e019" note="The corpus argument (a copy of T is a trivial subdivision of T, so Burr's chi >= 2k-2 bound forces mader_chi(T) <= 2k-2) now closes on the bodies, after the wave-E4 nonemptiness guard repair of the X52 row. Three ingredients: (i) k <= 1 is handled directly - k = 0 contradicts the nonemptiness of an oriented tree, and at k = 1 every non-empty host contains a subdivision of the one-vertex tree, which has no arc to replace (grounding_X52.v: x52_k1_holds); before the guard repair this instance was FALSE, which is why the edge was recorded refuted-direction. (ii) For 2 <= k the source applies once the two tree vocabularies are bridged: X2.oriented_tree (underlying graph a connected forest) implies P9.oriented_tree (weakly connected with #V-1 arcs) by x52_oriented_tree_tree_digraph, whose arc count is the tree edge count tree_nb_arcs, proved here by an explicit bijection arcs -> non-root vertices built from the separation predicate fsep of foundations/subdivision.v. (iii) The subdigraph copy is turned into a subdivision by subdig_contains_subdivision. No hypothesis is added to either row." *)

Theorem oriented_trees_in_n_chromatic_digraphs_implies_oriented_tree_mader_chi_linear_bound :
  oriented_trees_in_n_chromatic_digraphs_statement ->
  oriented_tree_mader_chi_linear_bound_statement.
Proof.
move=> H T k hT hcard D hD hchi.
case: k hcard hchi => [|[|k']] hcard hchi.
- by move: hT => [hne _ _ _]; rewrite hcard in hne.
- exact: (x52_k1_holds hT hcard hD).
- apply: subdig_contains_subdivision.
    by move: hT => [_ hor _ _] u; apply/negP => h; move: (hor _ _ h); rewrite h.
  by apply: (H D k'.+2) => //; exact: x52_oriented_tree_tree_digraph hT.
Qed.


(** ** Print Assumptions audit *)

Print Assumptions subdig_contains_subdivision.
Print Assumptions tree_nb_arcs.
Print Assumptions x52_weakly_connected.
Print Assumptions x52_oriented_tree_tree_digraph.
Print Assumptions oriented_trees_in_n_chromatic_digraphs_implies_oriented_tree_mader_chi_linear_bound.
