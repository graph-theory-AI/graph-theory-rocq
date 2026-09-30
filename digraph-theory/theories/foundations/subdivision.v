(** * Digraph.foundations.subdivision — reusable ingredients for the
      subdivision / Mader rows of waves P9, X2 and X52

    Everything here is GENERAL (no conjecture vocabulary, no [_statement]): the
    wiring to the two subdivision encodings ([P9.subdivides] and
    [X2.contains_subdivision]) lives in [conjectures/implications_X2.v].

    Contents:
    1. [mem_behead_belast] : a vertex of [x :: s] that is neither [x] nor
       [last x s] lies in the INTERIOR [behead (belast x s)] of the walk.  This is
       the seq-level bridge between the two spellings of "internal vertices of a
       replacement path".
    2. [dense_dg n] : the complete digraph on [n.+1] vertices (all arcs both
       ways), a NON-EMPTY host of minimum out-degree and in-degree exactly [n].
       Used by the grounding files to show the guarded minimum-degree hypothesis
       classes are inhabited at every threshold.
    3. [acyclic_topo_embed] : a digraph with no arc [u --> v] whose head reaches
       back to its tail admits an injective [g : D -> 'I_#|D|] with
       [u --> v -> g u < g v] — a TOPOLOGICAL ORDER.  The rank is built without
       recursion: [#|ancestors|] strictly increases along an arc, and ties are
       broken by [enum_rank], so the number of strictly smaller vertices is the
       required ordinal.
    4. [forest_last_nonadj] (ported from chromatic-theory/foundations/forest_paths.v)
       and [forest_no_backarc] : an ASYMMETRIC digraph whose arcs are edges of a
       FOREST has no such back-reaching arc, hence (with 3) a topological order.
       This is the acyclicity of oriented trees. *)

From HB Require Import structures.
From mathcomp Require Import all_boot.
From Digraph Require Import prelude interop_graph_theory digraph oriented dipath.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** 1. Interior of a walk *)

(** A member of [x :: s] other than [last x s] survives in [belast x s]. *)
Lemma mem_belast_cons (T : eqType) (x z : T) (s : seq T) :
  z \in x :: s -> z != last x s -> z \in belast x s.
Proof. by move=> hz hl; move: hz; rewrite lastI mem_rcons inE (negbTE hl) orFb. Qed.

(** [x :: s] with its first and last element removed is [behead (belast x s)];
    every other member of [x :: s] lies in it. *)
Lemma mem_behead_belast (T : eqType) (x z : T) (s : seq T) :
  z \in x :: s -> z != x -> z != last x s -> z \in behead (belast x s).
Proof.
case: s => [|a s]; first by rewrite mem_seq1 => /eqP ->; rewrite eqxx.
move=> hz hx hl; move: {hz hl}(mem_belast_cons hz hl) => /=.
by rewrite inE (negbTE hx) orFb.
Qed.

(** ** 2. A dense host: the complete digraph on [n.+1] vertices *)

Definition dense_dg (n : nat) : Type := 'I_n.+1.

Section Dense.
Variable n : nat.

HB.instance Definition _ := Finite.on (dense_dg n).
HB.instance Definition _ := HasArc.Build (dense_dg n) (fun u v : 'I_n.+1 => u != v).

Lemma card_dense : #|{: dense_dg n}| = n.+1.
Proof. exact: card_ord. Qed.

Lemma dense_gt0 : (0 < #|{: dense_dg n}|)%N.
Proof. by rewrite card_dense. Qed.

Lemma outdeg_dense (v : dense_dg n) : outdeg v = n.
Proof.
rewrite /outdeg (_ : [set w | v --> w] = [set~ v]); first by rewrite cardsC1 card_ord.
by apply/setP=> w; rewrite !inE eq_sym.
Qed.

(** The in-degree, spelled with the [{set _}] of in-neighbours so that this file
    stays free of the [conjectures/classic_core.v] vocabulary ([indeg v] is
    convertible to [#|[set u | u --> v]|]). *)
Lemma indeg_dense (v : dense_dg n) : #|[set u : dense_dg n | u --> v]| = n.
Proof.
rewrite (_ : [set u | u --> v] = [set~ v]); first by rewrite cardsC1 card_ord.
by apply/setP=> w; rewrite !inE.
Qed.

End Dense.

(** ** 3. A topological order from the absence of back-reaching arcs *)

Section TopoOrder.
Variable D : diGraphType.
Variable noback : forall u v : D, u --> v -> ~~ connect (@arc D) v u.

Definition anc (v : D) : {set D} := [set u | connect (@arc D) u v].

Lemma anc_refl (v : D) : v \in anc v.
Proof. by rewrite inE connect0. Qed.

Lemma anc_sub (u v : D) : u --> v -> anc u \subset anc v.
Proof.
move=> huv; apply/subsetP=> w; rewrite !inE => hw.
by apply: connect_trans hw _; exact: connect1.
Qed.

Lemma anc_lt (u v : D) : u --> v -> (#|anc u| < #|anc v|)%N.
Proof.
move=> huv; apply: proper_card; rewrite properEneq (anc_sub huv) andbT.
apply/negP => /eqP e; have hv : v \in anc u by rewrite e anc_refl.
by move: (noback huv); rewrite inE in hv; rewrite hv.
Qed.

(** The rank: ancestors first, [enum_rank] to break ties. *)
Definition tlt : rel D := fun u v =>
  (#|anc u| < #|anc v|)%N ||
  ((#|anc u| == #|anc v|) && (enum_rank u < enum_rank v)%N).

Lemma tlt_irr : irreflexive tlt.
Proof. by move=> u; rewrite /tlt ltnn eqxx ltnn. Qed.

Lemma tlt_trans : transitive tlt.
Proof.
move=> v u w; rewrite /tlt => /orP[h1|/andP[/eqP e1 r1]] /orP[h2|/andP[/eqP e2 r2]].
- by rewrite (ltn_trans h1 h2).
- by rewrite -e2 h1.
- by rewrite e1 h2.
- by rewrite e1 e2 eqxx (ltn_trans r1 r2) orbT.
Qed.

Lemma tlt_total (u v : D) : u != v -> tlt u v || tlt v u.
Proof.
move=> huv; have [e|ne] := eqVneq #|anc u| #|anc v|.
- have hr : (enum_rank u : nat) != enum_rank v.
    apply/negP => /eqP /val_inj /(can_inj (@enum_rankK D)) eq.
    by rewrite eq eqxx in huv.
  move: hr; rewrite neq_ltn => /orP[h|h].
  + by apply/orP; left; rewrite /tlt e eqxx h /= orbT.
  + by apply/orP; right; rewrite /tlt -e eqxx h /= orbT.
- move: ne; rewrite neq_ltn => /orP[h|h].
  + by apply/orP; left; rewrite /tlt h.
  + by apply/orP; right; rewrite /tlt h.
Qed.

Definition tless (v : D) : {set D} := [set w : D | tlt w v].

Lemma tless_lt (u v : D) : tlt u v -> (#|tless u| < #|tless v|)%N.
Proof.
move=> huv; apply: proper_card; rewrite properEneq; apply/andP; split.
- apply/eqP => e; have hu : u \in tless v by rewrite inE.
  by move: hu; rewrite -e inE tlt_irr.
- by apply/subsetP=> w; rewrite !inE => hw; exact: tlt_trans hw huv.
Qed.

Lemma tless_bound (v : D) : (#|tless v| < #|D|)%N.
Proof.
apply: leq_ltn_trans (_ : #|[set~ v]| < #|D|)%N.
  apply: subset_leq_card; apply/subsetP=> w; rewrite !inE => hw.
  by apply/negP => /eqP e; move: hw; rewrite e tlt_irr.
by rewrite cardsC1 ltn_predL; apply/card_gt0P; exists v.
Qed.

Definition tord (v : D) : 'I_#|D| := Ordinal (tless_bound v).

Lemma tord_lt (u v : D) : tlt u v -> (tord u < tord v)%N.
Proof. exact: tless_lt. Qed.

Lemma tord_inj : injective tord.
Proof.
move=> u v e; have ev : #|tless u| = #|tless v| by move/(f_equal val): e.
have [//|huv] := eqVneq u v.
by case/orP: (tlt_total huv) => /tless_lt hlt; move: hlt; rewrite ev ltnn.
Qed.

(** A digraph in which no arc reaches back to its own tail has a topological
    order: an injective numbering of its vertices strictly increasing along arcs. *)
Lemma acyclic_topo_embed :
  exists g : D -> 'I_#|D|, injective g /\ forall u v : D, u --> v -> (g u < g v)%N.
Proof.
exists tord; split; first exact: tord_inj.
by move=> u v huv; apply: tord_lt; rewrite /tlt (anc_lt huv).
Qed.

End TopoOrder.

(** ** 4. Arcs inside a forest never reach back *)

(** Ported from chromatic-theory/foundations/forest_paths.v (that package cannot
    be imported here): in a FOREST the two ends of a duplicate-free path with at
    least two edges are non-adjacent, since a chord would give two distinct
    irredundant paths between them. *)
Lemma forest_last_nonadj (G : sgraph) :
  is_forest [set: G] -> forall (x : G) (s : seq G),
  path (--) x s -> uniq (x :: s) -> (2 <= size s)%N -> ~~ (x -- last x s).
Proof.
move=> Gf x s pth uq sz; apply/negP => xy.
have irr1 : irred (Path_of_path pth) by rewrite irredE nodesE; exact: uq.
have irr2 : irred (edgep xy) by exact: irred_edge.
have e := forestT_unique Gf irr1 irr2.
move: sz; rewrite (_ : s = [:: last x s]) //.
by move: e => /(f_equal val).
Qed.

Section ForestArcs.
Variables (D : diGraphType) (G : sgraph) (h : D -> G).
Variable h_inj : injective h.
Variable arc_edge : forall u v : D, u --> v -> h u -- h v.
Variable Gf : is_forest [set: G].
Variable asym : forall u v : D, u --> v -> ~~ (v --> u).

Lemma arc_irr (v : D) : ~~ (v --> v).
Proof. by apply/negP => h1; move: (asym h1); rewrite h1. Qed.

Lemma path_arc_edge (x : D) (s : seq D) :
  path (@arc D) x s -> path (--) (h x) (map h s).
Proof.
elim: s x => [//|a s IH] x /= /andP[hxa hp].
by rewrite (arc_edge hxa) /=; exact: IH.
Qed.

(** The last vertex of a duplicate-free directed walk has no arc back to the
    first one: with one arc that would be a digon, with two or more a cycle of
    the underlying forest. *)
Lemma no_arc_back_uniq (v : D) (s : seq D) :
  path (@arc D) v s -> uniq (v :: s) -> ~~ (last v s --> v).
Proof.
move=> pth uq; apply/negP => hback.
case: s pth uq hback => [|a s] pth uq hback.
  by move: (arc_irr v); rewrite hback.
case: s pth uq hback => [|b s] pth uq hback.
  by move: pth => /= /andP[hva _]; move: (asym hback); rewrite hva.
have hp : path (--) (h v) (map h (a :: b :: s)) by exact: path_arc_edge pth.
have hu : uniq (h v :: map h (a :: b :: s)).
  by rewrite -map_cons map_inj_uniq.
have hs : (2 <= size (map h (a :: b :: s)))%N by rewrite size_map.
move: (forest_last_nonadj Gf hp hu hs); rewrite last_map => /negP; apply.
by rewrite sg_sym; exact: arc_edge hback.
Qed.

(** Hence no arc of [D] reaches back to its own tail: [D] is acyclic, and
    [acyclic_topo_embed] applies to it. *)
Lemma forest_no_backarc (u v : D) : u --> v -> ~~ connect (@arc D) v u.
Proof.
move=> huv; apply/negP => /connectP [p pth eu].
move: huv; rewrite eu.
by case/shortenP: pth => s pth' uq _; apply/negP; exact: no_arc_back_uniq.
Qed.

End ForestArcs.

(** ** 5. Trees: rooted paths, separation, and the arc count

    The ingredients of "a tree on n vertices has n-1 edges", at the level of
    duplicate-free vertex sequences (the packaged [Path] type of
    coq-graph-theory is used only inside [forest_upath_eq]).  The counting
    argument itself, which needs the digraph/underlying-graph pair, is in
    conjectures/implications_X52.v.

    [fsep r u v] says that [u] SEPARATES [v] from the root [r]: no
    duplicate-free path from [v] to [r] avoids [u].  In a tree, for every edge
    exactly one end separates the other, and the separating end is the second
    vertex of the tree path to the root - that is what turns "edges" into
    "non-root vertices". *)

(** The last element of a nonempty list is one of its elements. *)
Lemma last_mem_cons (T : eqType) (x : T) (s : seq T) : s != [::] -> last x s \in s.
Proof. by case: s => [//|a t] _ /=; exact: mem_last. Qed.

Section ForestPathsSeq.
Variable G : sgraph.

Lemma pathpI (x y : G) (s : seq G) :
  path (--) x s -> last x s = y -> pathp x y s.
Proof. by move=> ps ls; rewrite /pathp ps ls eqxx. Qed.

(** In a forest, two duplicate-free paths with the same endpoints are equal. *)
Lemma forest_upath_eq (Gf : is_forest [set: G]) (x y : G) (s t : seq G) :
  path (--) x s -> uniq (x :: s) -> last x s = y ->
  path (--) x t -> uniq (x :: t) -> last x t = y -> s = t.
Proof.
move=> ps us ls pt ut lt.
have i1 : irred (Build_Path (pathpI ps ls)) by rewrite irredE nodesE.
have i2 : irred (Build_Path (pathpI pt lt)) by rewrite irredE nodesE.
by move: (forestT_unique Gf i1 i2) => /(f_equal val).
Qed.

(** A neighbour of the first vertex lying on a duplicate-free path out of it is
    its SECOND vertex: cutting the path at that neighbour gives another
    duplicate-free path with the same ends, which must be the same path. *)
Lemma nbr_on_upath (Gf : is_forest [set: G]) (w u r : G) (s : seq G) :
  path (--) w s -> uniq (w :: s) -> last w s = r ->
  w -- u -> u \in s -> head w s = u.
Proof.
move=> ps us ls hwu hus.
have hi : index u s < size s by rewrite index_mem.
have hle : (index u s).+1 <= size s by exact: hi.
have hnth : nth w s (index u s) = u by rewrite nth_index.
have hlt : last w (take (index u s).+1 s) = u.
  by rewrite -nth_last (size_takel hle) /= nth_take // hnth.
have hpd : path (--) u (drop (index u s).+1 s).
  by move: ps; rewrite -{1}(cat_take_drop (index u s).+1 s) cat_path hlt => /andP[].
have hld : last u (drop (index u s).+1 s) = r.
  by rewrite -ls -[X in last w X](cat_take_drop (index u s).+1 s) last_cat hlt.
have hut : u \in take (index u s).+1 s.
  apply/(nthP w); exists (index u s); first by rewrite (size_takel hle).
  by rewrite (nth_take w (ltnSn (index u s))) hnth.
have hus' : uniq s by move: us; rewrite cons_uniq => /andP[].
have hcu : uniq (take (index u s).+1 s ++ drop (index u s).+1 s).
  by rewrite cat_take_drop.
move: hcu; rewrite cat_uniq => /and3P[_ /hasPn hno hdu].
have hund : u \notin drop (index u s).+1 s.
  by apply/negP => hd; move: (hno _ hd); rewrite hut.
have hwns : w \notin s by move: us; rewrite cons_uniq => /andP[].
have hpath2 : path (--) w (u :: drop (index u s).+1 s) by rewrite /= hwu.
have huniq2 : uniq (w :: u :: drop (index u s).+1 s).
  rewrite !cons_uniq hund hdu andbT /=; apply/andP; split.
    rewrite inE negb_or; apply/andP; split.
      by apply/negP => /eqP e; move: hwu; rewrite e sg_irrefl.
    by apply/negP => hd; move: hwns; rewrite (mem_drop hd).
  by [].
have hlast2 : last w (u :: drop (index u s).+1 s) = r by rewrite /= hld.
by rewrite (forest_upath_eq Gf ps us ls hpath2 huniq2 hlast2).
Qed.

(** ** Rooted paths in a tree and the separation predicate *)

(** In a connected graph every vertex has a duplicate-free path to the root. *)
Lemma tree_upath (Gc : connected [set: G]) (r v : G) :
  exists s : seq G, [/\ path (--) v s, uniq (v :: s) & last v s = r].
Proof.
have := connectedTE Gc v r; case/connectP => p pth lastp.
rewrite lastp; case/shortenP: pth => s pth' uq _.
by exists s; split.
Qed.

(** [fsep r u v] : [u] SEPARATES [v] from the root [r], i.e. [v] cannot reach [r]
    without meeting [u].  In a tree, for every edge exactly one end separates the
    other. *)
Definition fsep (r u v : G) : bool :=
  ~~ connect (preliminaries.restrict (~: [set u]) (--)) v r.

Lemma fsep_root (r u : G) : ~~ fsep r u r.
Proof. by rewrite /fsep negbK connect0. Qed.

Lemma fsep_neq (r u v : G) : fsep r u v -> v != r.
Proof.
move=> h; apply/negP => /eqP e; rewrite e in h.
by move: (fsep_root r u); rewrite h.
Qed.

(** The root separates everything from itself. *)
Lemma fsep_from_root (r v : G) : v != r -> fsep r r v.
Proof.
move=> hv; rewrite /fsep; apply/negP => /(@preliminaries.connect_restrictP _ _ _ _ _ hv)[p [_ hl _ hsub]].
have : r \in ~: [set r] by apply: hsub; rewrite -hl mem_last.
by rewrite !inE eqxx.
Qed.

(** A vertex ON the tree path from [v] to [r] separates [v] from [r]. *)
Lemma fsep_of_upath (Gf : is_forest [set: G]) (r u v : G) (s : seq G) :
  path (--) v s -> uniq (v :: s) -> last v s = r -> u \in s -> fsep r u v.
Proof.
move=> hp hu hl hus.
have hsnil : s != [::] by apply/negP => /eqP e; rewrite e in hus.
have hrs : r \in s by rewrite -hl; exact: last_mem_cons hsnil.
have hvr : v != r.
  apply/negP => /eqP e; move: hu; rewrite cons_uniq => /andP[hvs _].
  by rewrite e hrs in hvs.
apply/negP => hc.
move/(@preliminaries.connect_restrictP _ _ _ _ _ hvr): hc => [q [hq hlq huq hsubq]].
have eqs : q = s.
  apply: (forest_upath_eq Gf (x := v) (y := r)) hq huq hlq hp hu hl.
have : u \in ~: [set u] by apply: hsubq; rewrite inE eqs hus orbT.
by rewrite !inE eqxx.
Qed.

(** Conversely, the neighbour [z] of [w] that is NOT separated by [w] carries a
    path to the root avoiding [w]. *)
Lemma not_fsep_of_upath (r w z : G) (t : seq G) :
  path (--) z t -> uniq (w :: z :: t) -> last z t = r -> ~~ fsep r w z.
Proof.
move=> hp hu hl; rewrite /fsep negbK.
have [->|hzr] := eqVneq z r; first exact: connect0.
apply/(@preliminaries.connect_restrictP _ _ _ _ _ hzr); exists t; split.
- exact: hp.
- exact: hl.
- by move: hu; rewrite cons_uniq => /andP[_ hzt]; exact: hzt.
- move=> y hy; rewrite !inE; apply/negP => /eqP ey; rewrite ey in hy.
  by move: hu; rewrite cons_uniq hy.
Qed.

(** If [u] separates [v] from [r] and [u] is a neighbour of [v], then [u] is the
    SECOND vertex of every tree path from [v] to [r]. *)
Lemma fsep_head (Gf : is_forest [set: G]) (r u v : G) (s : seq G) :
  u -- v -> fsep r u v ->
  path (--) v s -> uniq (v :: s) -> last v s = r -> head v s = u.
Proof.
move=> huv hsep hp hu hl.
have hvr : v != r by exact: fsep_neq hsep.
have hmem : u \in s.
  apply/negP => hnu.
  have hcon : connect (preliminaries.restrict (~: [set u]) (--)) v r.
    apply/(@preliminaries.connect_restrictP _ _ _ _ _ hvr); exists s; split.
    - exact: hp.
    - exact: hl.
    - exact: hu.
    - move=> y; rewrite inE => /orP[/eqP ey|hys]; rewrite !inE.
      + by apply/negP => /eqP e; move: huv; rewrite -ey e sg_irrefl.
      + by apply/negP => /eqP e; rewrite e in hys; exact: hnu hys.
  by move: hsep; rewrite /fsep hcon.
by apply: (nbr_on_upath Gf hp hu hl _ hmem); rewrite sg_sym.
Qed.

(** The end of a non-separating edge carries a path to the root through it. *)
Lemma not_fsep_upath (r u v : G) : u -- v -> ~~ fsep r u v ->
  exists p : seq G, [/\ path (--) u (v :: p), uniq (u :: v :: p)
                     & last u (v :: p) = r].
Proof.
move=> huv; rewrite /fsep negbK => hc.
have hnuv : u != v by apply/negP => /eqP e; move: huv; rewrite e sg_irrefl.
have [ev|hvr] := eqVneq v r.
  exists [::]; split.
  - by rewrite /= huv.
  - by rewrite /= inE hnuv.
  - by rewrite /= ev.
move/(@preliminaries.connect_restrictP _ _ _ _ _ hvr): hc => [p [hp hl hup hsub]].
exists p; split.
- by rewrite /= huv.
- rewrite cons_uniq hup andbT; apply/negP => hun.
  have : u \in ~: [set u] by exact: hsub hun.
  by rewrite !inE eqxx.
- by rewrite /= hl.
Qed.

(** A path to the root is nonempty unless the vertex IS the root. *)
Lemma upath_to_root_neq (r v : G) (s : seq G) :
  last v s = r -> v != r -> s != [::].
Proof. by move=> hl hv; apply/negP => /eqP e; rewrite e /= in hl; rewrite hl eqxx in hv. Qed.

End ForestPathsSeq.

(** ** Print Assumptions audit *)

Print Assumptions mem_behead_belast.
Print Assumptions outdeg_dense.
Print Assumptions indeg_dense.
Print Assumptions acyclic_topo_embed.
Print Assumptions forest_last_nonadj.
Print Assumptions forest_no_backarc.
Print Assumptions forest_upath_eq.
Print Assumptions nbr_on_upath.
Print Assumptions tree_upath.
Print Assumptions fsep_of_upath.
Print Assumptions not_fsep_upath.
Print Assumptions fsep_head.
